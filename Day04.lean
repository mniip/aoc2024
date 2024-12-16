import Aoc2024

section Parser
open Parser
def parser : Parser (SomeRect Char)
  := (anyChar.until (string "\n")).many.filterMap Rect.fromArray?
end Parser

def solution1 : SomeRect Char → Nat
  | ⟨width, height, board⟩ =>
    let checks := (List.range height).bind λy₀ => (List.range width).bind λx₀ =>
      "XMAS".toList.zip <$> dirs.filterMap λ(Δx, Δy) =>
        (List.range 4).mapA λ(i : Nat) => Rect.index? (x₀ + i * Δx, y₀ + i * Δy)
    checks.countP (·.all λ(ch, p) => board.get p = some ch)
  where
    dirs : List (Int × Int)
      := [(1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)]

def solution2 : SomeRect Char → Nat
  | ⟨width, height, board⟩ =>
    let checks := (List.range height).bind λy₀ => (List.range width).bind λx₀ =>
      dirs.filterMap λ(Δx, Δy) =>
        [ ('M', -Δx, -Δy)
        , ('A', 0, 0)
        , ('S', Δx, Δy)
        , ('M', Δy, -Δx)
        , ('S', -Δy, Δx)
        ].mapA λ(ch, δx, δy) => (ch, ·) <$> Rect.index? (x₀ + δx, y₀ + δy)
    checks.countP (·.all λ(ch, p) => board.get p = some ch)
  where
    dirs : List (Int × Int) := [(1, 1), (-1, 1), (-1, -1), (1, -1)]

def main : IO Unit := IO.main parser solution1 solution2
