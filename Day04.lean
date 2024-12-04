import Aoc2024

section Parser
open Parser
def parser : Parser (Array (Array Char))
  := ((anyChar.satisfies (· != '\n')).many <* string "\n").many
end Parser

def solution1 (input : Array (Array Char)) : Nat
  := checks.foldl
    (λacc check => if check.all λ(ch, x, y) => input[x]?.bind (·[y]?) = some ch
      then acc + 1
      else acc)
    0
  where
    width := input.toList.head?.elim 0 Array.size
    height := input.size
    dirs : List (Int × Int)
      := [(1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)]
    checks := (List.range height).bind λy₀ => (List.range width).bind λx₀ =>
      "XMAS".toList.zip <$> dirs.filterMap λ(Δx, Δy) =>
        (List.range 4).mapA λ(i : Nat) => do
          let x ← (x₀ + i * Δx).toNat'
          let y ← (y₀ + i * Δy).toNat'
          pure (x, y)

def solution2 (input : Array (Array Char)) : Nat
  := checks.foldl
    (λacc check => if check.all λ(ch, x, y) => input[x]?.bind (·[y]?) = some ch
      then acc + 1
      else acc)
    0
  where
    width := input.toList.head?.elim 0 Array.size
    height := input.size
    dirs : List (Int × Int)
      := [(1, 1), (-1, 1), (-1, -1), (1, -1)]
    checks := (List.range height).bind λy₀ => (List.range width).bind λx₀ =>
      dirs.filterMap λ(Δx, Δy) =>
        [ ('M', -Δx, -Δy)
        , ('A', 0, 0)
        , ('S', Δx, Δy)
        , ('M', Δy, -Δx)
        , ('S', -Δy, Δx)
        ].mapA λ(ch, δx, δy) => do
          let x ← (x₀ + δx).toNat'
          let y ← (y₀ + δy).toNat'
          pure (ch, x, y)

def main : IO Unit := do
  match parser.parse (← IO.allStdin) with
  | none =>
    IO.eprintln "Parse error"
    return
  | some input =>
    IO.println $ solution1 input
    IO.println $ solution2 input
