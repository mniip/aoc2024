import Aoc2024

section Parser
open Parser
def parser : Parser (Array (Nat × Nat) × Nat)
  := Prod.mk <$> (Prod.mk <$> digit <*> digit).many <*> digit <* string "\n"
  where
    digit := anyChar.satisfies Char.isDigit <&> λc => c.toNat - '0'.toNat
end Parser

def solution1 : Array (Nat × Nat) × Nat → Nat
  | (arr, last₀) =>
    let rec
      go (off total : Nat)
        (hole : Nat) (i j : Fin (arr.size + 1)) (last : Nat)
        : Nat
        := if hole = 0
          then if p : i < j
            then
              let (len, hole') := arr[i]
              let i' : Fin (arr.size + 1) := (i.natAdd 1).castLT $ by
                obtain ⟨i, _⟩ := i
                obtain ⟨j, _⟩ := j
                simp only [Fin.mk_lt_mk] at p
                apply Nat.lt_of_le_of_lt
                . dsimp only [Fin.natAdd_mk]
                  rw [Nat.add_comm 1 i]
                  apply Nat.succ_le.mpr
                  exact p
                . assumption
              go (off + len) (total + weight i off len)
                hole' i' j last
            else total + weight j off last
          else if last = 0
            then if p : i < j
              then
                let j' := j.pred $ by
                  obtain ⟨i, _⟩ := i
                  obtain ⟨j, _⟩ := j
                  apply Fin.val_ne_iff.mp
                  apply Nat.not_eq_zero_of_lt p
                let (last', _) := arr[j']
                go off total hole i (j'.castLE (by simp)) last'
              else total
            else if last > hole
              then go (off + hole) (total + weight j off hole)
                0 i j (last - hole)
              else go (off + last) (total + weight j off last)
                (hole - last) i j 0
      termination_by (j.val - i.val, hole)
    go 0 0 0 0 (Fin.last _) last₀
  where
    weight id off len := id * (off * len + len * (len - 1) / 2)

structure Hole where
  off : Nat
  len : Nat

structure File where
  id : Nat
  off : Nat
  len : Nat

def solution2 : Array (Nat × Nat) × Nat → Nat
  | (arr, last) =>
    let holes₀ := (arr.mapM (m:=StateM Nat)
      (λ(file, hole) off =>
        ( { off := off + file
          , len := hole
          : Hole
          }
        , off + file + hole
        ))).run' 0
    let files := (arr.mapM (m:=StateM (Nat × Nat))
      (λ(file, hole) (id, off) =>
        ( { id := id
          , off := off
          , len := file
          : File
          }
        , id + 1
        , off + file + hole
        ))).run (0, 0)
      |> λ(files', id₀, off₀) => files'.push
        { id := id₀
        , off := off₀
        , len := last
        }
    files.foldr
      (λfile (total, holes) => match findHole holes file with
        | some (off, holes')
          => (total + weight { file with off := off }, holes')
        | none => (total + weight file, holes))
      (0, holes₀)
    |> Prod.fst
  where
    weight file
      := file.id * (file.off * file.len + file.len * (file.len - 1) / 2)
    findHole (holes : Array Hole) (file : File) :=
      let rec go i := if p : i < holes.size
        then let hole := holes[i]
          if hole.off ≥ file.off
          then none
          else if hole.len < file.len
            then go (i + 1)
            else if hole.len = file.len
              then some (hole.off, holes.eraseIdx i)
              else some
                ( hole.off
                , holes.set ⟨i, p⟩
                  { off := hole.off + file.len
                  , len := hole.len - file.len
                  }
                )
        else none
      go 0

def main : IO Unit := IO.main parser solution1 solution2
