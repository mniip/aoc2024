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

def neighbors (board : Rect w h Bool)
  : Dir4 × Fin w × Fin h → List (Nat × (Dir4 × Fin w × Fin h))
  | (d, p) => [(1000, (d.cw, p)), (1000, (d.ccw, p))]
    ++ match Rect.index? (d.advance' p) with
      | none => []
      | some p' => if board.get p' then [] else [(1, (d, p'))]

def solution1 (input : Input) : Nat :=
  let _ : Ord (Fin input.width × Fin input.height) := lexOrd
  let _ : Ord (Dir4 × Fin input.width × Fin input.height) := lexOrd
  let _ : Append Unit := ⟨default⟩
  (Dijkstra.empty.init ⟨(Dir4.E, input.start), 0, ()⟩).until
    (λ(_, p) => p = input.finish)
    (λe => (neighbors input.board e.into).map λ(w, s) =>
      { into := s
      , weight := w
      , link := ()
      })
  |> (·.elim default λ⟨e, _⟩ => e.weight)

def solution2 (input : Input) : Nat :=
  let _ : Ord (Fin input.width × Fin input.height) := lexOrd
  let _ : Ord (Dir4 × Fin input.width × Fin input.height) := lexOrd
  let β := Lean.RBMap (Fin input.width × Fin input.height) Unit compare
  let _ : Append β := ⟨Lean.RBMap.mergeBy default⟩
  (Dijkstra.empty.init (β:=β)
    ⟨(Dir4.E, input.start), 0, Lean.RBMap.empty.insert input.start ()⟩).until
    (λ(_, p) => p = input.finish)
    (λe => (neighbors input.board e.into).map λ(w, s) =>
      { into := s
      , weight := w
      , link := e.link.insert s.2 ()
      })
  |> (·.elim 0 λ⟨e, _⟩ => e.link.size)

def main : IO Unit := IO.main parser solution1 solution2
