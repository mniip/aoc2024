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

inductive Dir where
  | right
  | down
  | left
  | up
  deriving Ord

def Dir.cw : Dir → Dir
  | right => down
  | down => left
  | left => up
  | up => right

def Dir.delta : Dir → Int × Int
  | right => (1, 0)
  | down => (0, 1)
  | left => (-1, 0)
  | up => (0, -1)

inductive Advancement (α : Type) : Type where
  | Advanced : α → Advancement α
  | Blocked : α → Advancement α
  | OffBoard : Advancement α

def advance (board : Rect width height Bool)
  : Dir × (Fin width × Fin height)
    → Advancement (Dir × (Fin width × Fin height))
  | (d, (x, y)) =>
    match
      do
        let (Δx, Δy) := d.delta
        let p ← Rect.index? (x + Δx, y + Δy)
        pure (board[p], p)
    with
    | none => .OffBoard
    | some (true, _) => .Blocked (d.cw, (x, y))
    | some (false, p) => .Advanced (d, p)

partial def solution1 : Input → Nat
  | ⟨_, _, board, p₀⟩ => go board (Dir.up, p₀)
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
  | ⟨_, _, board, p₀⟩ => go1 board (Dir.up, p₀)
    (Lean.RBMap.empty (cmp:=lexOrd.compare))
    (Lean.RBMap.empty (cmp:=(@lexOrd _ _ _ lexOrd).compare))
  where
    go1 {width height} (board : Rect width height Bool) p notchosen seen :=
      let seen' := seen.insert p ()
      match advance board p with
      | .OffBoard => 0
      | .Blocked p' => go1 board p' notchosen seen'
      | .Advanced p' =>
        if (notchosen.find? p'.2).isSome
        then go1 board p' notchosen seen'
        else go2 (board.set p'.2 true) p seen
          + go1 board p' (notchosen.insert p'.2 ()) seen'
    go2 {width height} (board : Rect width height Bool) p seen
      := if (seen.find? p).isSome
        then 1
        else
          let seen' := seen.insert p ()
          match advance board p with
          | .OffBoard => 0
          | .Blocked p' => go2 board p' seen'
          | .Advanced p' => go2 board p' seen'

def main : IO Unit := IO.main parser solution1 solution2
