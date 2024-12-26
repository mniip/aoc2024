import Aoc2024

section Parser
open Parser
def parser : Parser (Array Nat) := (nat <* string "\n").many
end Parser

def evolve (s : Nat) : Nat := Id.run do
  let mut s := s
  s := (s ^^^ (s <<< 6)) &&& 0xFFFFFF
  s := (s ^^^ (s >>> 5)) &&& 0xFFFFFF
  s := (s ^^^ (s <<< 11)) &&& 0xFFFFFF
  s

def price (s : Nat) : Int8 := Int.toInt8 (s % 10)

def solution1 : Array Nat → Nat
  | input => input.map (λs => Nat.rec s (λ_ => evolve) 2000)
    |> Array.foldl (· + ·) 0

def packIndex : Int8 × Int8 × Int8 × Int8 → Nat
  | (a, b, c, d) => ((((a.toInt + 9) * 19 + b.toInt + 9)
    * 19 + c.toInt + 9) * 19 + d.toInt + 9).toNat

def unpackIndex : Nat → Int8 × Int8 × Int8 × Int8
  | n =>
    let d := (Int.ofNat (n % 19) - 9).toInt8
    let n := n / 19
    let c := (Int.ofNat (n % 19) - 9).toInt8
    let n := n / 19
    let b := (Int.ofNat (n % 19) - 9).toInt8
    let n := n / 19
    let a := (Int.ofNat n - 9).toInt8
    (a, b, c, d)

def recordDiffs.go (iter : Nat) (s : Nat) (p₁ : Int8) (d₁ d₂ d₃ : Int8)
  (arr : Array Int8) : Array Int8 :=
  if iter = 0
  then arr
  else
    let p₀ := price s
    let d₀ := p₀ - p₁
    let i := packIndex (d₃, d₂, d₁, d₀)
    let arr := if arr[i]? = some (-1) then arr.setD i p₀ else arr
    recordDiffs.go (iter - 1) (evolve s) p₀ d₀ d₁ d₂ arr

def recordDiffs (iter : Nat) (s : Nat) : Array Int8 :=
  let p₄ := price s
  let s := evolve s
  let p₃ := price s
  let s := evolve s
  let p₂ := price s
  let s := evolve s
  let p₁ := price s
  let s := evolve s
  recordDiffs.go (iter - 3) s p₁ (p₁ - p₂) (p₂ - p₃) (p₃ - p₄)
    (Array.mkArray (19 * 19 * 19 * 19) (-1))

def solution2 : Array Nat → Nat
  | input => input.foldl
    (λa s => a.zipWith (recordDiffs 2000 s)
      (λsum p => if p = -1 then sum else sum + p.toNat))
    (Array.mkArray (19 * 19 * 19 * 19) 0)
    |> Array.zipWithIndex
    |> (·.getMax? λ(p₁, _) (p₂, _) => p₁ < p₂)
    |> (·.elim default Prod.fst)

def main : IO Unit := IO.main parser solution1 solution2
