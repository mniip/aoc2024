import Aoc2024

section Parser
open Parser
def parser : Parser (Array (SomeRect Bool))
  := (rect.filterMap Rect.fromArray?).many
  where
    cell := anyChar <&> (· == '#')
    row := cell.until (string "\n")
    rect := (#[·] ++ ·) <$> row <*> row.until (string "\n" <|> eof)
end Parser

def Rect.transpose (r : Rect width height α) : Rect height width α
  := Rect.tabulate λ(x, y) => r[(y, x)]

def solution1 (input : Array (SomeRect Bool)) : Nat :=
  let (locks, keys) := input.partition λ⟨w, h, a⟩ => if p : 0 < h
    then Fin.foldl w (λb x => b && a.get (x, ⟨0, p⟩)) true
    else false
  let heights := λ⟨w, h, a⟩ =>
    ( h
    , Fin.foldr w
      (λx xs => Fin.foldl h (λs y => s + a[(x, y)].toNat) 0 :: xs)
      []
    )
  let locks := locks.map heights
  let keys := keys.map heights
  locks.foldl
    (λs (h₁, lock) => keys.foldl
      (λs (h₂, key) => if h₁ == h₂ && (lock.zipWith (· + ·) key).all (· ≤ h₁)
        then s + 1
        else s)
      s)
    0

def main : IO Unit := IO.main parser solution1 λ_ => ""
