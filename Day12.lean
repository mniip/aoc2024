import Aoc2024

section Parser
open Parser
def parser : Parser (SomeRect Char)
  := (anyChar.until (string "\n")).many.filterMap Rect.fromArray?
end Parser

partial def solution1 : SomeRect Char → Nat
  | ⟨width, height, board⟩ =>
    let rec region (seen : Rect width height Bool)
      | p, ch =>
        let neighbors := Dir4.list.map
          λd => Rect.index? (d.advance (p.1, p.2))
            |> Option.filter (board[·] = ch)
        neighbors.reduceOption.foldl
          (λ(seen, area, perim) p => if seen[p] = true
            then (seen, area, perim)
            else
              let (seen', area', perim') := region seen p ch
              (seen', area + area', perim + perim'))
          (seen.set p true, 1, neighbors.countP Option.isNone)
    board.foldlIdx (λ(seen, sum) p ch => if seen[p] = true
      then (seen, sum)
      else let (seen', area, perim) := region seen p ch
        (seen', sum + area * perim))
      (Rect.mk false, 0)
      |> Prod.snd

partial def solution2 : SomeRect Char → Nat
  | ⟨width, height, board⟩ =>
    let rec region (seen : Rect width height Bool)
      | p, ch =>
        let ok := λp' => board[p']? = some ch
        let corners := Dir4.list.countP λd => ¬ok (d.transform' 1 0 p)
          ∧ (¬ok (d.transform' 0 1 p) ∨ ok (d.transform' 1 1 p))
        Dir4.list.filterMap
          (λd => (Rect.index? (d.advance' p)).filter (board[·] = ch))
          |> List.foldl
            (λ(seen, area, corners) p => if seen[p] = true
              then (seen, area, corners)
              else
                let (seen', area', corners') := region seen p ch
                (seen', area + area', corners + corners'))
            (seen.set p true, 1, corners)
    board.foldlIdx (λ(seen, sum) p ch => if seen[p] = true
      then (seen, sum)
      else let (seen', area, corners) := region seen p ch
        (seen', sum + area * corners))
      (Rect.mk false, 0)
      |> Prod.snd

def main : IO Unit := IO.main parser solution1 solution2
