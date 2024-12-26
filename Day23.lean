import Aoc2024

section Parser
open Parser
def parser : Parser (Array (String × String)) :=
  (Prod.mk
    <$> ((String.mk ∘ Array.toList) <$> anyChar.until (string "-"))
    <*> ((String.mk ∘ Array.toList) <$> anyChar.until (string "\n"))).many
end Parser

def toGraph [Ord α]
  : Array (α × α) → Lean.RBMap α (Lean.RBMap α Unit compare) compare
  := Array.foldl
    (λm (a, b) =>
      let m := m.insert a ((m.findD a Lean.RBMap.empty).insert b ())
      let m := m.insert b ((m.findD b Lean.RBMap.empty).insert a ())
      m)
    Lean.RBMap.empty

def triangles [Ord α]
  : (Lean.RBMap α (Lean.RBMap α Unit compare) compare) → Array (α × α × α)
  | edges => edges.fold
    (λa v₁ vs => vs.fold
      (λa v₂ _ => if compare v₁ v₂ = .lt
        then vs.fold
          (λa v₃ _ =>
            if compare v₂ v₃ = .lt ∧ ((edges.find? v₂).bind (·.find? v₃)).isSome
            then a.push (v₁, v₂, v₃)
            else a)
          a
        else a)
      a)
    #[]

def solution1 : Array (String × String) → Nat
  | input =>
    (triangles $ toGraph input).foldl
      (λs (v₁, v₂, v₃) =>
        if v₁.startsWith "t" ∨ v₂.startsWith "t" ∨ v₃.startsWith "t"
        then s + 1
        else s)
      0

def cliques [Ord α]
  : (Lean.RBMap α (Lean.RBMap α Unit compare) compare) → Array (Array α)
  | edges =>
    let rec go a chosen
      | v :: vs =>
        let es := edges.findD v Lean.RBMap.empty
        if chosen.all λc => (es.find? c).isSome
        then go (go a chosen vs) (chosen.push v) vs
        else go a chosen vs
      | [] => a.push chosen
    edges.fold
      (λa v₁ vs => go a #[v₁] $ vs.revFold
        (λvs v _ => if compare v₁ v = .lt then v :: vs else vs)
        [])
      #[]

def solution2 : Array (String × String) → String
  | input => (cliques $ toGraph input).foldl
    (λbest c => if c.size > best.size then c else best)
    #[]
    |> String.intercalate "," ∘ Array.toList

def main : IO Unit := IO.main parser solution1 solution2
