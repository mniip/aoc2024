import Aoc2024
import Lean.Data.RBMap

section Parser
open Parser
def parser : Parser (SomeRect (Option Char))
  := (cell.until (string "\n")).many.filterMap Rect.fromArray?
  where
    cell := anyChar <&> λ
      | '.' => none
      | ch => some ch
end Parser

def asMap (board : Rect width height (Option Char))
  : Lean.RBMap Char (List (Fin width × Fin height)) compare
  := board.foldlIdx
    (λm p cell => match cell with
      | some ch => m.insert ch $ p :: m.findD ch []
      | none => m)
    Lean.RBMap.empty

def List.pairs : List α → List (α × α)
  | [] => []
  | x :: xs => (x, ·) <$> xs ++ pairs xs

def List.upairs : List α → List (α × α)
  | xs => xs.pairs.bind λ(a, b) => [(a, b), (b, a)]

def solution1 : SomeRect (Option Char) → Nat
  | ⟨width, height, board⟩ =>
    (asMap board).fold
      (λantis _ points => points.upairs.foldl
        (λantis ((x₁, y₁), (x₂, y₂))
          => antis.setD (Int.ofNat 2 * x₂ - x₁, Int.ofNat 2 * y₂ - y₁) true)
        antis)
      (Rect.mk (width:=width) (height:=height) false)
    |> (·.foldl (· + ·.toNat) 0)

def solution2 : SomeRect (Option Char) → Nat
  | ⟨width, height, board⟩ =>
    let scale := max width height
    (asMap board).fold
      (λantis _ points => points.upairs.foldl
        (λantis ((x₁, y₁), (x₂, y₂)) =>
          let Δx := Int.ofNat x₁ - Int.ofNat x₂
          let Δy := Int.ofNat y₁ - Int.ofNat y₂
          let δx := Δx / Int.gcd Δx Δy
          let δy := Δy / Int.gcd Δx Δy
          (List.range scale).foldl
            (λantis d
              => antis.setD (x₁ + δx * Int.ofNat d, y₁ + δy * Int.ofNat d) true)
            antis)
        antis)
      (Rect.mk (width:=width) (height:=height) false)
    |> (·.foldl (· + ·.toNat) 0)

def main : IO Unit := IO.main parser solution1 solution2
