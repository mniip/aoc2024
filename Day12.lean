import Aoc2024
import Lean.Data.RBMap

section Parser
open Parser
def parser : Parser (SomeRect Char)
  := (anyChar.until (string "\n")).many.filterMap Rect.fromArray?
end Parser

partial def solution1 : SomeRect Char → Nat
  | ⟨width, height, board⟩ =>
    let rec region seen
      | (x, y), ch =>
        let neighbors := [(1, 0), (0, 1), (-1, 0), (0, -1)].map
          λ(Δx, Δy) => Rect.index? (Int.ofNat x + Δx, Int.ofNat y + Δy)
            |> Option.filter (board[·] = ch)
        neighbors.reduceOption.foldl
          (λ(seen, area, perim) p => if seen[p] = true
            then (seen, area, perim)
            else
              let (seen', area', perim') := region seen p ch
              (seen', area + area', perim + perim'))
          (seen.set (x, y) true, 1, neighbors.countP Option.isNone)
    board.foldlIdx (λ(seen, sum) p ch => if seen[p]
      then (seen, sum)
      else let (seen', area, perim) := region seen p ch
        (seen', sum + area * perim))
      (Functor.mapConst false board, 0)
      |> Prod.snd

partial def solution2 : SomeRect Char → Nat
  | ⟨width, height, board⟩ =>
    let rec region seen
      | (x, y), ch =>
        let neighbor := λ(Δx, Δy)
          => Rect.index? (Int.ofNat x + Δx, Int.ofNat y + Δy)
          |> Option.filter (board[·] = ch)
        let dirs := [(1, 0), (0, 1), (-1, 0), (0, -1)]
        let ok := Option.isSome ∘ neighbor
        let isCorner := λ(Δx, Δy)
          => ¬ok (Δx, Δy) ∧ (¬ok (-Δy, Δx) ∨ ok (Δx - Δy, Δx + Δy))
        dirs.filterMap neighbor
          |> List.foldl
            (λ(seen, area, corners) p => if seen[p] = true
              then (seen, area, corners)
              else
                let (seen', area', corners') := region seen p ch
                (seen', area + area', corners + corners'))
            (seen.set (x, y) true, 1, dirs.countP isCorner)
    board.foldlIdx (λ(seen, sum) p ch => if seen[p]
      then (seen, sum)
      else let (seen', area, corners) := region seen p ch
        (seen', sum + area * corners))
      (Functor.mapConst false board, 0)
      |> Prod.snd

def main : IO Unit := IO.main parser solution1 solution2
