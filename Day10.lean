import Aoc2024
import Lean.Data.RBMap

section Parser
open Parser
def parser : Parser (Array (Array (Fin 10)))
  := (digit.until (string "\n")).many
  where
    digit := anyChar.filterMap
      λ ch => if ch.toNat ≥ '0'.toNat
        then if p : ch.toNat - '0'.toNat < 10
          then some ⟨ch.toNat - '0'.toNat, p⟩
          else none
        else none
end Parser

def solution1 (board : Array (Array (Fin 10))) : Nat :=
  Fin.foldr _ (λi targets => if i = Fin.last _
    then board.zipWithIndex.foldl
      (λm (row, y) => row.zipWithIndex.foldl
        (λm (d, x) => if d == Fin.last _
          then m.insert (x, y) (Lean.RBMap.empty.insert (x, y) ())
          else m)
        m)
      targets
    else board.zipWithIndex.foldl
      (λm (row, y) => row.zipWithIndex.foldl
        (λm (d, x) => if d == i
          then
            [(1, 0), (0, 1), (-1, 0), (0, -1)].filterMap
              (λ(Δx, Δy) => targets.find? (x + Δx, y + Δy))
            |> List.foldl
              (Lean.RBMap.mergeBy default)
              (Lean.RBMap.empty (cmp:=lexOrd.compare))
            |> m.insert (x, y)
          else m)
        m)
      Lean.RBMap.empty)
    (Lean.RBMap.empty (α:=Int × Int) (cmp:=lexOrd.compare))
  |> Lean.RBMap.fold (λsum _ targets => sum + targets.size) 0

def solution2 (board : Array (Array (Fin 10))) : Nat :=
  Fin.foldr _ (λi targets => if i = Fin.last _
    then board.zipWithIndex.foldl
      (λm (row, y) => row.zipWithIndex.foldl
        (λm (d, x) => if d == Fin.last _
          then m.insert (x, y) 1
          else m)
        m)
      targets
    else board.zipWithIndex.foldl
      (λm (row, y) => row.zipWithIndex.foldl
        (λm (d, x) => if d == i
          then
            [(1, 0), (0, 1), (-1, 0), (0, -1)].filterMap
              (λ(Δx, Δy) => targets.find? (x + Δx, y + Δy))
            |> List.foldl (· + ·) 0
            |> m.insert (x, y)
          else m)
        m)
      Lean.RBMap.empty)
    (Lean.RBMap.empty (α:=Int × Int) (cmp:=lexOrd.compare))
  |> Lean.RBMap.fold (λsum _ targets => sum + targets) 0

def main : IO Unit := IO.main parser solution1 solution2
