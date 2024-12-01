import Aoc2024
import Init.Data.List.Basic

section Parser
open Parser
def parser : Parser (Array (Int × Int))
  := line.many
  where line := Prod.mk <$> int <* whitespace <*> int <* string "\n"
end Parser

def solution1 : Array (Int × Int) → Nat
  | input => let (xs, ys) := input.unzip
    Array.foldl (· + ·) 0
      $ Array.zipWith xs.qsortOrd ys.qsortOrd (Int.natAbs $ · - ·)

def solution2 : Array (Int × Int) → Int
  | input => let (xs, ys) := input.unzip
    Array.foldl (· + ·) 0 $ xs.map λx => x * ys.toList.count x

def main : IO Unit := do
  match parser.parse (← IO.allStdin) with
  | none =>
    IO.eprintln "Parse error"
    return
  | some input =>
    IO.println $ solution1 input
    IO.println $ solution2 input
