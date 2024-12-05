import Aoc2024

section Parser
open Parser
def parser : Parser (Array (Int × Int) × Array (Array Int))
  := Prod.mk
    <$> (Prod.mk <$> int <* string "|" <*> int <* string "\n").many
    <* string "\n"
    <*> (((string ",").optional *> int).many <* string "\n").many
end Parser

def List.pairs : List α → List (α × α)
  | x :: xs => ((x, ·) <$> xs) ++ pairs xs
  | [] => []

def solution1 : Array (Int × Int) × Array (Array Int) → Int
  | (rules, pages) => pages
    |> Array.filter (λbook => book.toList.pairs.all rules.elem)
    |> Array.filterMap (λbook => book[book.size / 2]?)
    |> Array.foldl (· + ·) 0

def solution2 : Array (Int × Int) × Array (Array Int) → Int
  | (rules, pages) => pages
    |> Array.filter (λbook => !book.toList.pairs.all rules.elem)
    |> Array.map (λbook => book.qsort λx y => rules.elem (x, y))
    |> Array.filterMap (λbook => book[book.size / 2]?)
    |> Array.foldl (· + ·) 0

def main : IO Unit := IO.main parser solution1 solution2
