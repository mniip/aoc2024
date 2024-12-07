import Aoc2024
import Lean.Data.RBMap

section Parser
open Parser
def parser : Parser (Array (Array Bool) × Nat × Nat)
  := board
  where
    line := ((anyChar.satisfies (· != '\n')).many <* string "\n")
      <&> λchars => (chars.map (· == '#'), chars.findIdx? (· == '^'))
    board := do
      let lines ← line.many
      match (lines.map Prod.fst, ·, ·)
        <$> (lines.findSome? (λ(_, m) => m))
        <*> (lines.findIdx? (λ(_, m) => m.isSome))
      with
      | none => default
      | some res => pure res
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

def advance (board : Array (Array Bool))
  : (Dir × Nat × Nat) → Advancement (Dir × Nat × Nat)
  | (d, x, y) =>
    let (Δx, Δy) := d.delta
    match do
      let x' ← (x + Δx).toNat'
      let y' ← (y + Δy).toNat'
      let row ← board[y']?
      let cell ← row[x']?
      pure (cell, x', y')
    with
    | none => .OffBoard
    | some (true, _, _) => .Blocked (d.cw, x, y)
    | some (false, x', y') => .Advanced (d, x', y')

partial def solution1 : Array (Array Bool) × Nat × Nat → Nat
  | (board, x₀, y₀) => go board (Dir.up, x₀, y₀)
    (Lean.RBMap.empty (cmp:=(@lexOrd _ _ _ lexOrd).compare))
  where
    go board p seen :=
      let seen' := seen.insert p ()
      match advance board p with
      | .Advanced p' => go board p' seen'
      | .Blocked p' => go board p' seen'
      | .OffBoard => seen'.fold (λm (_, x, y) _ => m.insert (x, y) Unit)
        (Lean.RBMap.empty (cmp:=lexOrd.compare))
        |> Lean.RBMap.size

partial def solution2 : Array (Array Bool) × Nat × Nat → Nat
  | (board, x₀, y₀) => go1 board (Dir.up, x₀, y₀)
    (Lean.RBMap.empty (cmp:=lexOrd.compare))
    (Lean.RBMap.empty (cmp:=(@lexOrd _ _ _ lexOrd).compare))
  where
    go1 board p notchosen seen :=
      let seen' := seen.insert p ()
      match advance board p with
      | .OffBoard => 0
      | .Blocked p' => go1 board p' notchosen seen'
      | .Advanced p' =>
        let loc := (p'.2.1, p'.2.2)
        if (notchosen.find? loc).isSome
        then go1 board p' notchosen seen'
        else
          let board' := board.modify loc.2 λrow => row.modify loc.1 λ_ => true
          go2 board' p seen + go1 board p' (notchosen.insert loc ()) seen'
    go2 board p seen := if (seen.find? p).isSome
      then 1
      else
        let seen' := seen.insert p ()
        match advance board p with
        | .OffBoard => 0
        | .Blocked p' => go2 board p' seen'
        | .Advanced p' => go2 board p' seen'

def main : IO Unit := IO.main parser solution1 solution2
