import Aoc2024

section Parser
open Parser
def parser : Parser (Array ((Int × Int) × (Int × Int)))
  := line.many
  where line := Prod.mk
    <$> (string "p=" *> Prod.mk <$> int <* string "," <*> int)
    <*> (string " v=" *> Prod.mk <$> int <* string "," <*> int)
    <* string "\n"
end Parser

def simulate width height (steps : Nat) [NeZero width] [NeZero height]
  : (Int × Int) × (Int × Int) → Fin width × Fin height
  | ((x, y), (vx, vy)) =>
    ( Fin.ofNat' width ((x + steps * vx).fmod width).toNat
    , Fin.ofNat' height ((y + steps * vy).fmod height).toNat
    )

def solution1 (input : Array ((Int × Int) × (Int × Int))) : Nat :=
  let width := 101
  let height := 103
  input.map (simulate width height 100)
  |> Array.foldl (λ(tl, tr, bl, br) (x, y) =>
    match compare x.val (width / 2), compare y.val (height / 2) with
    | .lt, .lt => (tl + 1, tr, bl, br)
    | .lt, .gt => (tl, tr, bl + 1, br)
    | .gt, .lt => (tl, tr + 1, bl, br)
    | .gt, .gt => (tl, tr, bl, br + 1)
    | _, _ => (tl, tr, bl, br))
    (0, 0, 0, 0)
  |> (λ(tl, tr, bl, br) => tl * tr * bl * br)

partial def solution2 (input : Array ((Int × Int) × (Int × Int))) : Nat :=
  let width : Nat := 101
  let height : Nat := 103
  let sampleVariance : Array Int → Int
    | xs => xs.size * xs.foldl (λq v => q + v * v) 0 - (xs.foldl (· + ·) 0)^2
  let expected_X : Int := width^2 * input.size * (input.size - 1) / 12
  let expected_Y : Int := height^2 * input.size * (input.size - 1) / 12
  let thr_X := expected_X * 2 / 3
  let thr_Y := expected_Y * 2 / 3
  let rec
    go i :=
      let pos := input.map (simulate width height i)
      if sampleVariance (pos.map (·.1)) < thr_X
        ∧ sampleVariance (pos.map (·.2)) < thr_Y
      then i
      else go (i + 1)
  go 0

def main : IO Unit := IO.main parser solution1 solution2
