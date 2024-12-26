import Aoc2024

structure Input where
  width : Nat
  height : Nat
  board : Rect width height Bool
  start : Fin width × Fin height
  finish : Fin width × Fin height

section Parser
open Parser
def parser : Parser Input := (anyChar.until (string "\n")).many.filterMap
  λchars => do
    let ⟨width, height, r⟩ ← Rect.fromArray? chars
    let start ← r.findIdx? (· == 'S')
    let finish ← r.findIdx? (· == 'E')
    some
      { width := width
      , height := height
      , board := r.map (· == '#')
      , start := start
      , finish := finish
      }
end Parser

instance : Ord (Fin w × Fin h) := lexOrd

def distances (input : Input)
  : Option (Nat
    × Lean.RBMap (Fin input.width × Fin input.height) Nat compare
    × Lean.RBMap (Fin input.width × Fin input.height) Nat compare)
  := do
    let _ : Append Unit := ⟨default⟩
    let neighbors e
      := Dir4.list.filterMap (λd => Rect.index? (d.advance' e.into))
        |> List.filter (!input.board[·])
        |> List.map (⟨., 1, ()⟩)
    let (w₀, fromStart) ←
      (Dijkstra.empty.init ⟨input.start, 0, ()⟩).foldUntil
      (· = input.finish) neighbors
      (λm e _ => m.insert e.into e.weight)
      (λm e _ _ => some (e.weight, m))
      (λm _ => none)
      (Lean.RBMap.empty (cmp:=compare))
    let fromFinish := (Dijkstra.empty.init ⟨input.finish, 0, ()⟩).foldUntil
      (· = input.start) neighbors
      (λm e _ => m.insert e.into e.weight)
      (λm e _ _ => m)
      (λm _ => m)
      (Lean.RBMap.empty (cmp:=compare))
    some (w₀, fromStart, fromFinish)

def Fin.foldlAround (x : Fin n) (δ : Nat) (f : σ → Fin n → σ) : σ → σ :=
  let rec go i s := if p : i < n
    then if i > x + δ
      then s
      else go (i + 1) (f s ⟨i, p⟩)
    else s
  go (x - δ)

def foldCheats (board : Rect w h Bool) (δ : Nat)
  (f : σ → Fin w × Fin h → Fin w × Fin h → σ) : σ → σ
  := board.foldlIdx
    (λs p₁ b => if b
      then s
      else p₁.1.foldlAround δ
        (λs x₂ => p₁.2.foldlAround (δ - (Int.ofNat p₁.1 - x₂).natAbs)
          (λs y₂ =>
            let p₂ := (x₂, y₂)
            if p₁ ≠ p₂ && !board[p₂]
            then f s p₁ p₂
            else s)
          s)
        s)

def solution (δ : Nat) (input : Input) : Nat
  := match distances input with
    | none => 0
    | some (w₀, fromStart, fromFinish) => foldCheats input.board δ
      (λs p₁ p₂ => match fromStart.find? p₁ with
        | some w₁ => match fromFinish.find? p₂ with
          | some w₂ =>
            let w₃ := (Int.ofNat p₁.1 - p₂.1).natAbs
              + (Int.ofNat p₁.2 - p₂.2).natAbs
            if w₁ + w₂ + w₃ + 100 ≤ w₀
            then s + 1
            else s
          | none => s
        | none => s)
      0

def solution1 : Input → Nat := solution 2

def solution2 : Input → Nat := solution 20

def main : IO Unit := IO.main parser solution1 solution2
