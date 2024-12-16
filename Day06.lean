import Aoc2024
import Lean.Data.RBMap

abbrev Input := (width : Nat) × (height : Nat)
  × Rect width height Bool
  × (Fin width × Fin height)

section Parser
open Parser
def parser : Parser Input
  := (anyChar.until (string "\n")).many.filterMap Rect.fromArray?
    |> filterMap λ⟨width, height, board⟩ => match board.findIdx? (· = '^') with
      | none => none
      | some start => some ⟨width, height, board.map (· == '#'), start⟩
end Parser

inductive Advancement (α : Type) : Type where
  | Advanced : α → Advancement α
  | Blocked : α → Advancement α
  | OffBoard : Advancement α

def advance (board : Rect width height Bool)
  : Dir4 × (Fin width × Fin height)
    → Advancement (Dir4 × (Fin width × Fin height))
  | (d, p) =>
    match Rect.index? (d.advance' p) with
    | none => .OffBoard
    | some p' => if board[p'] = true
      then .Blocked (d.cw, p)
      else .Advanced (d, p')

partial def solution1 : Input → Nat
  | ⟨_, _, board, p₀⟩ => go board (Dir4.N, p₀)
    (Lean.RBMap.empty (cmp:=(@lexOrd _ _ _ lexOrd).compare))
  where
    go {width height} (board : Rect width height Bool) p seen :=
      let seen' := seen.insert p ()
      match advance board p with
      | .Advanced p' => go board p' seen'
      | .Blocked p' => go board p' seen'
      | .OffBoard => seen'.fold (λm (_, p) _ => m.insert p Unit)
        (Lean.RBMap.empty (cmp:=lexOrd.compare))
        |> Lean.RBMap.size

partial def solution2 : Input → Nat
  | ⟨_, _, board, p₀⟩ => go1 board (Dir4.N, p₀)
    (Lean.RBMap.empty (cmp:=lexOrd.compare))
    (Lean.RBMap.empty (cmp:=(@lexOrd _ _ _ lexOrd).compare))
  where
    go1 {width height} (board : Rect width height Bool) s notchosen seen :=
      let seen' := seen.insert s ()
      match advance board s with
      | .OffBoard => 0
      | .Blocked s' => go1 board s' notchosen seen'
      | .Advanced s' =>
        if (notchosen.find? s'.2).isSome
        then go1 board s' notchosen seen'
        else go2 (board.set s'.2 true) s seen
          + go1 board s' (notchosen.insert s'.2 ()) seen'
    go2 {width height} (board : Rect width height Bool) s seen
      := if (seen.find? s).isSome
        then 1
        else
          let seen' := seen.insert s ()
          match advance board s with
          | .OffBoard => 0
          | .Blocked s' => go2 board s' seen'
          | .Advanced s' => go2 board s' seen'

def main : IO Unit := IO.main parser solution1 solution2
