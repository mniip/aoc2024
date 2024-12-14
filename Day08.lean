import Aoc2024
import Lean.Data.RBMap

section Parser
open Parser
def parser : Parser (Array (Array (Option Char)))
  := (cell.until (string "\n")).many
  where
    cell := anyChar <&> λ
      | '.' => none
      | ch => some ch
end Parser

def asMap (input : Array (Array (Option Char)))
  : (width : Nat)
    × (height : Nat)
    × Lean.RBMap Char (List (Fin width × Fin height)) compare
  :=
    ⟨ width
    , input.size
    , (input.mapIdx Prod.mk).foldl
      (λm (y, row) => (row.mapIdx Prod.mk).foldl
        (λm (x, cell) => match cell with
          | some ch => if p : x < width
            then m.insert ch $ (⟨x, p⟩, y) :: m.findD ch []
            else m
          | none => m)
        m)
      Lean.RBMap.empty
    ⟩
  where
    width := input.back?.elim 0 Array.size

def List.pairs : List α → List (α × α)
  | [] => []
  | x :: xs => (x, ·) <$> xs ++ pairs xs

def List.upairs : List α → List (α × α)
  | xs => xs.pairs.bind λ(a, b) => [(a, b), (b, a)]

def bound (w h : Nat) : Int × Int → Option (Fin w × Fin h)
  | (x, y) => do
    let x' ← x.toNat'
    let y' ← y.toNat'
    if p : x' < w
    then
      if q : y' < h
      then some (⟨x', p⟩, ⟨y', q⟩)
      else none
    else none

def solution1 (input : Array (Array (Option Char))) : Nat :=
  let ⟨w, h, map⟩ := asMap input
  map.fold
    (λantis _ points => points.upairs.foldl
      (λantis ((x₁, y₁), (x₂, y₂)) =>
        match bound w h (Int.ofNat 2 * x₂ - x₁, Int.ofNat 2 * y₂ - y₁) with
        | none => antis
        | some p => antis.insert p ())
      antis)
    (Lean.RBMap.empty (cmp:=lexOrd.compare))
    |> Lean.RBMap.size

def solution2 (input : Array (Array (Option Char))) : Nat :=
  let ⟨w, h, map⟩ := asMap input
  let scale := max w h
  map.fold
    (λantis _ points => points.upairs.foldl
      (λantis ((x₁, y₁), (x₂, y₂)) =>
        let Δx := Int.ofNat x₁ - Int.ofNat x₂
        let Δy := Int.ofNat y₁ - Int.ofNat y₂
        let δx := Δx / Int.gcd Δx Δy
        let δy := Δy / Int.gcd Δx Δy
        (List.range scale).foldl
          (λantis d =>
            match bound w h (x₁ + δx * Int.ofNat d, y₁ + δy * Int.ofNat d) with
            | none => antis
            | some p => antis.insert p ())
          antis)
      antis)
    (Lean.RBMap.empty (cmp:=lexOrd.compare))
    |> Lean.RBMap.size

def main : IO Unit := IO.main parser solution1 solution2
