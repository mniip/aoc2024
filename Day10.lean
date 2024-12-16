import Aoc2024
import Lean.Data.RBMap

section Parser
open Parser
def parser : Parser (SomeRect (Fin 10))
  := (digit.until (string "\n")).many.filterMap Rect.fromArray?
  where
    digit := anyChar.filterMap
      λ ch => if ch.toNat ≥ '0'.toNat
        then if p : ch.toNat - '0'.toNat < 10
          then some ⟨ch.toNat - '0'.toNat, p⟩
          else none
        else none
end Parser

def accumTrailheads (mempty : M) (mappend : M → M → M)
  (point : Fin width × Fin height → M)
  (board : Rect width height (Fin (n + 1)))
  : Rect width height M
  := Fin.foldr n (λi targets
    => Rect.tabulate λp => if board[p] = i.castSucc
      then
        Dir4.list.foldl
          (λacc d =>
            match targets[d.advance' p]? with
            | none => acc
            | some val => mappend acc val)
          mempty
      else mempty)
    (Rect.tabulate (λp => if board[p] = Fin.last _ then point p else mempty))

def solution1 : SomeRect (Fin 10) → Nat
  | ⟨_, _, board⟩ =>
    accumTrailheads
      (Lean.RBMap.empty (cmp:=lexOrd.compare))
      (Lean.RBMap.mergeBy default)
      (Lean.RBMap.empty.insert · ())
      board
    |> (·.foldl (λsum targets => sum + targets.size) 0)

def solution2 : SomeRect (Fin 10) → Nat
  | ⟨_, _, board⟩ =>
    accumTrailheads 0 (· + ·) (λ_ => 1) board
    |> (·.foldl (· + ·) 0)

def main : IO Unit := IO.main parser solution1 solution2
