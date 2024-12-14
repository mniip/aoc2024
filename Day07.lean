import Aoc2024

section Parser
open Parser
def parser : Parser (Array (Nat × Array Nat))
  := (Prod.mk
    <$> (nat <* string ":")
    <*> (whitespace *> nat).until (string "\n")).many
end Parser

def canEvaluateTo (preimages : Nat → Nat → List Nat) (arr : Array Nat)
  : Nat → Bool
  := if p : arr.size = 0
    then λ_ => false
    else
      let rec go (i : Fin arr.size) (tgt : Nat) : Bool :=
        let x := arr[i]
        if i.val = 0
        then tgt == x
        else
          let i' : Fin arr.size :=
            ⟨ i.val - 1
            , calc
              i.val - 1 ≤ i := Nat.sub_le _ _
              _ < _ := i.isLt
            ⟩
          (preimages x tgt).any (go i')
      go ⟨arr.size - 1, Nat.sub_one_lt p⟩

def solution1 : Array (Nat × Array Nat) → Nat
  | input => input.toList
    |> List.filterMap (λ(tgt, arr) => (some tgt).filter (canEvaluateTo pre arr))
    |> List.foldl (· + ·) 0
  where
    pre x tgt
      := (if tgt ≥ x then [tgt - x] else [])
      ++ (if tgt % x == 0 then [tgt / x] else [])

def solution2 : Array (Nat × Array Nat) → Nat
  | input => input.toList
    |> List.filterMap (λ(tgt, arr) => (some tgt).filter (canEvaluateTo pre arr))
    |> List.foldl (· + ·) 0
  where
    pre x tgt
      := (if tgt ≥ x then [tgt - x] else [])
      ++ (if tgt % x == 0 then [tgt / x] else [])
      ++ (if tgt % 10 ^ digits x == x then [tgt / 10 ^ digits x] else [])

    digits (n : Nat) : Nat := if n ≥ 10 then digits (n / 10) + 1 else 1

def main : IO Unit := IO.main parser solution1 solution2
