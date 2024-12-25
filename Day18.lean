import Aoc2024

section Parser
open Parser
def parser : Parser (Array (Nat × Nat))
  := (Prod.mk <$> nat <* string "," <*> nat <* string "\n").many
end Parser

def solution1 (input : Array (Nat × Nat)) : Nat :=
  let board : Rect 71 71 Bool := (input.take 1024).foldl
    (λr (x, y) => r.setD (x, y) true)
    (Rect.mk false)
  let _ : Ord (Fin 71 × Fin 71) := lexOrd
  let _ : Append Unit := ⟨default⟩
  (Dijkstra.empty.init (α:=Fin 71 × Fin 71) ⟨(0, 0), 0, ()⟩).until
    (· = (70, 70))
    (λe => Dir4.list.filterMap (λd => Rect.index? (d.advance' e.into))
      |> List.filter (¬board.get ·)
      |> List.map (⟨., 1, ()⟩))
  |> (·.elim default (λ⟨e, _⟩ => e.weight))

def solution2 (input : Array (Nat × Nat)) : String :=
  let board : Rect 71 71 (Option Nat) := input.zipWithIndex.foldl
    (λr ((x, y), i) => r.setD (x, y) (some i))
    (Rect.mk none)
  let _ : Ord (Fin 71 × Fin 71) := lexOrd
  let _ : Ord Nat := Ord.opposite inferInstance
  let _ : Add (Option Nat) := ⟨min⟩
  let _ : Append Unit := ⟨default⟩
  (Dijkstra.empty.init (α:=Fin 71 × Fin 71)
    ⟨(0, 0), board.get (0, 0), ()⟩).until
    (· = (70, 70))
    (λe => Dir4.list.filterMap (λd => Rect.index? (d.advance' e.into))
      |> List.map λp => ⟨p, board[p], ()⟩)
  |> (·.bind (·.val.weight.bind (input[·]?)))
  |> (·.elim default λ(x, y) => s!"{x},{y}")

def main : IO Unit := IO.main parser solution1 solution2
