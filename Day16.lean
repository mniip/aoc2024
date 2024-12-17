import Aoc2024
import Lean.Data.RBMap

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

partial def dijkstra {α β γ : Type}
  [Ord α] [Ord β] [Ord γ] [Add γ] [Zero γ]
  (adj : α → List (γ × β × α)) (v₀ : α) (pred : α → Bool)
  : Option (γ × Lean.RBMap β Unit compare) :=
  let rec back prev v m := match prev.find? v with
    | none => m
    | some (_, es) => es.foldl (λm (e, v') => back prev v' (m.insert e ())) m
  let rec go
    (seen : Lean.RBMap α Unit compare)
    (queue : Lean.RBMap γ (α × List α) compare)
    (prev : Lean.RBMap α (γ × List (β × α)) compare)
    := do
      let (l, v, queue) ← queue.min.map λ
        | (l, (v, [])) => (l, v, queue.erase l)
        | (l, (v, v' :: vs)) => (l, v, queue.insert l (v', vs))
      if (seen.find? v).isSome
      then go seen queue prev
      else if pred v
        then some (l, back prev v Lean.RBMap.empty)
        else
          let seen := seen.insert v ()
          let (queue, prev) := (adj v).foldl
            (λ(queue, prev) (l', e, v') =>
              let l := l + l'
              match
                if compare v' v₀ = .eq then none
                else match prev.find? v' with
                  | none => some $ prev.insert v' (l, [(e, v)])
                  | some (l'', es) => match compare l l'' with
                    | .lt => some $ prev.insert v' (l, [(e, v)])
                    | .eq => some $ prev.insert v' (l, (e, v) :: es)
                    | .gt => none
              with
              | none => (queue, prev)
              | some prev => (·, prev) $ match queue.find? l with
                  | none => queue.insert l (v', [])
                  | some (v'', vs) => queue.insert l (v', v'' :: vs))
            (queue, prev)
          go seen queue prev
  go
    Lean.RBMap.empty
    (Lean.RBMap.empty.insert Zero.zero (v₀, []))
    Lean.RBMap.empty

instance : Ord (Fin w × Fin h) := lexOrd
instance : Ord (Dir4 × Fin w × Fin h) := lexOrd
instance : Ord Unit := ⟨λ_ _ => .eq⟩

def solution1 (input : Input) : Nat
  := dijkstra
    (λ(d, p) =>
    [(1000, (), (d.cw, p)), (1000, (), (d.ccw, p))]
    ++ match Rect.index? (d.advance' p) with
      | none => []
      | some p' => if input.board.get p' then [] else [(1, (), (d, p'))])
    (Dir4.E, input.start)
    (λ(_, p) => p = input.finish)
  |> (·.elim 0 Prod.fst)

def solution2 (input : Input) : Nat
  := dijkstra
    (λ(d, p) =>
    [(1000, p, (d.cw, p)), (1000, p, (d.ccw, p))]
    ++ match Rect.index? (d.advance' p) with
      | none => []
      | some p' => if input.board.get p' then [] else [(1, p, (d, p'))])
    (Dir4.E, input.start)
    (λ(_, p) => p = input.finish)
  |> (·.elim 0 λ(_, m) => 1 + m.size)

def main : IO Unit := IO.main parser solution1 solution2
