import Aoc2024
import Init.Data.List.Basic
import Lean.Data.RBMap

section Parser
open Parser
def parser : Parser (Array (Array Nat))
  := (((string " ").optional *> nat).many <* string "\n").many
end Parser

def solution1 : Array (Array Nat) → Nat
  | input => (input.filter λxs => safeFwd xs || safeFwd xs.reverse).size
  where
    safeFwd xs := List.all (List.zip xs.toList xs.toList.tail)
      λ(x, y) => y >= x + 1 && y <= x + 3

def solution2 : Array (Array Nat) → Nat
  | input => (input.filter λxs => safeFwd xs || safeFwd xs.reverse).size
  where
    safeFwd ys := List.any (ys.toList :: holes ys.toList)
      λxs => List.all (List.zip xs xs.tail)
        λ(x, y) => y >= x + 1 && y <= x + 3
    holes
      | x :: xs => xs :: (x :: ·) <$> holes xs
      | [] => []

def main : IO Unit := do
  match parser.parse (← IO.allStdin) with
  | none =>
    IO.eprintln "Parse error"
    return
  | some input =>
    IO.println $ solution1 input
    IO.println $ solution2 input
