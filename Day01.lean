import Aoc2024
import Init.Data.List.Basic

section Parser
open Parser
def parser : Parser (List (Int × Int))
  := line.many
  where line := Prod.mk <$> int <* whitespace <*> int <* string "\n"
end Parser

def solution1 : List (Int × Int) → Nat
  | input => let (xs, ys) := input.unzip
    Nat.sum $ List.zipWith (Int.natAbs $ · - ·) xs.mergeSort ys.mergeSort

def solution2 : List (Int × Int) → Int
  | input => let (xs, ys) := input.unzip
    List.foldl (· + ·) 0 $ xs.map λx => x * ys.count x

def main : IO Unit := do
  match parser.parse (← IO.allStdin) with
  | none =>
    IO.eprintln "Parse error"
    return
  | some input =>
    IO.println $ solution1 input
    IO.println $ solution2 input
