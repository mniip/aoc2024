import Aoc2024
import Lean.Data.RBMap

inductive Cell where
  | empty
  | box
  | wall

structure Input where
  width : Nat
  height : Nat
  board : Rect width height Cell
  init : Fin width × Fin height
  moves : Array Dir4

section Parser
open Parser
def parser : Parser Input := board <*> moves
  where
    cells := (anyChar.until (string "\n")).until (string "\n")
    board := cells.filterMap λcs => do
      let ⟨width, height, r⟩ ← Rect.fromArray? cs
      let init ← r.findIdx? (· = '@')
      some λmoves =>
        { width := width
        , height := height
        , board := r.map λ
          | '#' => .wall
          | 'O' => .box
          | _ => .empty
        , init := init
        , moves := moves
        }
    move :=
      [ Functor.mapConst .E (string ">")
      , Functor.mapConst .S (string "v")
      , Functor.mapConst .W (string "<")
      , Functor.mapConst .N (string "^")
      ].foldl (· <|> ·) default
    moves := (move <* whitespace).many
end Parser

def move
  (board : Rect width height Cell) (p₀ : Fin width × Fin height) (d : Dir4)
  : Option (Rect width height Cell × Fin width × Fin height) :=
  let rec shuffle fuel p₁ p
    := if fuel > 0
    then (Rect.index? (d.advance' p)).bind λp' => match board[p'] with
      | Cell.empty => some $ (board.set p' .box).set p₁ .empty
      | Cell.box => shuffle (fuel - 1) p₁ p'
      | Cell.wall => none
    else none
  (Rect.index? (d.advance' p₀)).bind λp₁ => match board[p₁] with
    | Cell.empty => some (board, p₁)
    | Cell.wall => none
    | Cell.box => (·, p₁) <$> shuffle (max width height) p₁ p₁

def solution1 (input : Input) : Nat :=
  input.moves.foldl
    (λ(board, p) d => (move board p d).getD (board, p))
    (input.board, input.init)
  |> Prod.fst
  |> (·.foldlIdx (λ
    | sum, (x, y), Cell.box => sum + 100 * y + x
    | sum, _, _ => sum) 0)

inductive Cell2 where
  | empty
  | box (right : Bool)
  | wall

def widen : Rect width height Cell → Rect (2 * width) height Cell2
  | ⟨rows, e⟩ =>
    ⟨ rows.map λ⟨row, f⟩ =>
      ⟨ row.flatMap λ
        | .empty => #[.empty, .empty]
        | .box => #[.box false, .box true]
        | .wall => #[.wall, .wall]
      , by
        cases f
        unfold Array.flatMap
        rw
          [ Array.foldl_eq_foldl_toList
          , List.foldl_eq_foldlM
          , ← List.reverse_reverse row.toList
          , List.foldlM_reverse
          , ← List.foldr_eq_foldrM
          , Array.size_eq_length_toList row
          , ← List.length_reverse
          ]
        induction row.toList.reverse with
        | nil => rfl
        | cons c _ IH =>
          simp only [List.foldr_cons, Array.size_append, List.length_cons, IH]
          rw [Nat.mul_add_one]
          congr
          cases c <;> rfl
      ⟩
    , by rw [Array.size_map, e]
    ⟩

def move2
  (board : Rect width height Cell2) (p₀ : Fin width × Fin height) (d : Dir4)
  : Option (Rect width height Cell2 × Fin width × Fin height) :=
  let addTargets ps p := match board.get p with
    | .empty => some ps
    | .wall => none
    | .box b => if d == .N ∨ d == .S
      then do
        let q ← Rect.index? (p.1 + if b then -1 else 1, p.2)
        some $ (ps.insert p ()).insert q ()
      else some $ ps.insert p ()
  let rec shuffle fuel ps
    := if fuel > 0
    then if ps.isEmpty
      then some board
      else ps.fold
        (λk p _ ps' => do
          let p' ← Rect.index? (d.advance' p)
          let ps' ← addTargets ps' p'
          let mut board' ← k ps'
          board' := board'.set p' board'[p]
          board' := board'.set p .empty
          some board')
        (shuffle (fuel - 1))
        Lean.RBMap.empty (cmp:=lexOrd.compare)
    else none
  do
    let p₁ ← Rect.index? (d.advance' p₀)
    let ps₀ ← addTargets Lean.RBMap.empty p₁
    (·, p₁) <$> shuffle (max width height) ps₀

def solution2 (input : Input) : Nat :=
  input.moves.foldl
    (λ(board, p) d => (move2 board p d).getD (board, p))
    (widen input.board, (⟨2 * input.init.1.val, by simp⟩, input.init.2))
  |> Prod.fst
  |> (·.foldlIdx (λ
    | sum, (x, y), Cell2.box false => sum + 100 * y + x
    | sum, _, _ => sum) 0)

def main : IO Unit := IO.main parser solution1 solution2
