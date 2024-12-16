import Aoc2024

section Parser
open Parser
def parser : Parser (SomeRect Char)
  := (anyChar.until (string "\n")).many.filterMap Rect.fromArray?
end Parser

def solution1 : SomeRect Char → Nat
  | ⟨width, height, board⟩ =>
    let checks :=
      (List.range height).flatMap λy₀ =>
      (List.range width).flatMap λx₀ =>
      Dir8.list.filterMap λd =>
        "XMAS".toList.zip <$>
          (List.range 4).mapA λi => Rect.index? (d.advanceBy i (x₀, y₀))
    checks.countP (·.all λ(ch, p) => board.get p = some ch)

def solution2 : SomeRect Char → Nat
  | ⟨width, height, board⟩ =>
    let checks :=
      (List.range height).flatMap λy₀ =>
      (List.range width).flatMap λx₀ =>
      Dir4.list.filterMap λd =>
        [ ('M', -1, -1)
        , ('M', -1, 1)
        , ('A', 0, 0)
        , ('S', 1, -1)
        , ('S', 1, 1)
        ].mapA λ(ch, along, ccw) =>
          (ch, ·) <$> Rect.index? (d.transform along ccw (x₀, y₀))
    checks.countP (·.all λ(ch, p) => board.get p = some ch)

def main : IO Unit := IO.main parser solution1 solution2
