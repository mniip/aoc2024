import Aoc2024
import Init.Data.List.Basic
import Lean.Data.RBMap

section Parser
open Parser
def parser : Parser (Array (Int × Int))
  := line.many
  where line := Prod.mk <$> int <* whitespace <*> int <* string "\n"
end Parser

def solution1 : Array (Int × Int) → Nat
  | input => let (left, right) := input.unzip
    Array.zipWith left.qsortOrd right.qsortOrd (Int.natAbs $ · - ·)
      |> Array.foldl (· + ·) 0

def solution2 : Array (Int × Int) → Int
  | input =>
    let (left, right) := input.unzip
    let counts : Array Int → Lean.RBMap Int Int compare
      := Array.foldl (λm y => m.insert y (m.findD y 0 + 1)) {}
    Lean.RBMap.intersectBy (· * · * ·) (counts left) (counts right)
      |> (·.toList.map Prod.snd)
      |> List.foldl (· + ·) 0

def main : IO Unit := IO.main parser solution1 solution2
