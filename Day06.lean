import Aoc2024
import Lean.Data.RBMap

section Parser
open Parser
def parser : Parser (Array (Array Bool) × Nat × Nat)
  := board
  where
    line := ((anyChar.satisfies (· != '\n')).many <* string "\n")
      <&> λchars => (chars.map (· == '#'), chars.findIdx? (· == '^'))
    board := do
      let lines ← line.many
      match (lines.map Prod.fst, ·, ·)
        <$> (lines.findSome? (λ(_, m) => m))
        <*> (lines.findIdx? (λ(_, m) => m.isSome))
      with
      | none => default
      | some res => pure res
end Parser

inductive Dir where
  | right
  | down
  | left
  | up
  deriving Ord

def Dir.cw : Dir → Dir
  | right => down
  | down => left
  | left => up
  | up => right

def Dir.delta : Dir → Int × Int
  | right => (1, 0)
  | down => (0, 1)
  | left => (-1, 0)
  | up => (0, -1)

def step : Array (Array Bool) → (Dir × Nat × Nat) → Option (Dir × Nat × Nat)
  | board, (d, x, y) => do
      let (Δx, Δy) := d.delta
      let x' ← (x + Δx).toNat'
      let y' ← (y + Δy).toNat'
      let row ← board[y']?
      let cell ← row[x']?
      if cell
      then pure (d.cw, x, y)
      else pure (d, x', y')

partial def numVisited
  : Array (Array Bool) → (Dir × Nat × Nat) → Option (Unit → Nat)
  | board, p₀ => go board p₀
    (Lean.RBMap.empty (cmp:=(@lexOrd _ _ _ lexOrd).compare))
  where
    go board p seen :=
      let seen' := seen.insert p ()
      if (seen.find? p).isSome
      then none
      else match step board p with
        | some p' => go board p' seen'
        | none => some λ_ => seen'.fold (λm (_, x, y) _ => m.insert (x, y) Unit)
          (Lean.RBMap.empty (cmp:=lexOrd.compare))
          |> Lean.RBMap.size

def solution1 : Array (Array Bool) × Nat × Nat → Nat
  | (board, x₀, y₀) => (numVisited board (Dir.up, x₀, y₀)).get! ()

def Array.forOnce (f : α → β × List β) (xs : Array α) : Array β × List (Array β)
  := if _ : xs.isEmpty
    then (Array.empty, [])
    else
      have p : xs.size - 1 < xs.size := match xs with
        | ⟨[]⟩ => by contradiction
        | ⟨_ :: _⟩ => by
          simp only
            [ size_toArray
            , List.length_cons
            , Nat.add_one_sub_one
            , Nat.lt_add_one
            ]
      have h : xs.back?.isSome := by rw
        [ Array.back?.eq_1
        , Array.get?_eq_toList_get?
        , List.get?_eq_get p
        ] <;> rfl
      match Array.forOnce f xs.pop, f (xs.back?.get h) with
      | (olds, news), (old, new)
        => (olds.push old, olds.push <$> new ++ (·.push old) <$> news)
  termination_by xs.size

def solution2 : Array (Array Bool) × Nat × Nat → Nat
  | (board, x₀, y₀) => board
    |> Array.forOnce (Array.forOnce λ
      | false => (false, [true])
      | true => (true, []))
    |> Prod.snd
    |> List.countP (λboard' => (numVisited board' (Dir.up, x₀, y₀)).isNone)

def main : IO Unit := IO.main parser solution1 solution2
