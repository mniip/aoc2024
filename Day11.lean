import Aoc2024
import Lean.Data.RBMap

section Parser
open Parser
def parser : Parser (Array Nat) := (whitespace *> nat).until (string "\n")
end Parser

def solution : Nat → Array Nat → Nat
  | n, input => Fin.foldl n
    (λmults _ => mults.fold
      (λmults val mul => (evolve val).foldl
        (λmults val' => mults.insert val' (mults.findD val' 0 + mul))
        mults)
      Lean.RBMap.empty)
    (input.foldl
      (λm val => m.insert val (m.findD val 0 + 1))
      (Lean.RBMap.empty (cmp:=compare)))
    |> Lean.RBMap.fold (λsum _ mul => sum + mul) 0
  where
    evolve n := if n = 0
      then [1]
      else if 2 ∣ digits n
        then [n / 10 ^ (digits n / 2), n % 10 ^ (digits n / 2)]
        else [n * 2024]
    digits (n : Nat) : Nat := if n ≥ 10 then digits (n / 10) + 1 else 1

def solution1 : Array Nat → Nat := solution 25

def solution2 : Array Nat → Nat := solution 75

def main : IO Unit := IO.main parser solution1 solution2
