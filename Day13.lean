import Aoc2024

abbrev Input := Array ((Int × Int) × (Int × Int) × (Int × Int))

section Parser
open Parser
def parser : Parser Input := (whitespace *> machine).many
  where
    machine := (·, ·, ·)
      <$> (string "Button A: X+" *> Prod.mk <$> int
        <* string ", Y+" <*> int <* string "\n")
      <*> (string "Button B: X+" *> Prod.mk <$> int
        <* string ", Y+" <*> int <* string "\n")
      <*> (string "Prize: X=" *> Prod.mk <$> int
        <* string ", Y=" <*> int <* string "\n")
end Parser

inductive LinSolution
  | unique (e : Int) (f : Int)
  | line (e : Int) (f : Int) (δe : Int) (δf : Int)
  | plane
  | none
  deriving Repr

def extended_gcd (r s t r' s' t' : Int) : Int × Int × Int :=
  if r = 0
  then (r', s', t')
  else let q := r' / r
    extended_gcd (r' % r) (s' - q * s) (t' - q * t) r s t
  termination_by ((decide (r.natAbs < r'.natAbs)).not.toNat, r.natAbs)
  decreasing_by
    have dec : (r' % r).natAbs < r.natAbs := by
      cases Int.lt_or_gt_of_ne (by assumption : r ≠ 0)
      . rw [← Int.emod_neg, ← Int.natAbs_neg r]
        apply Int.natAbs_lt_natAbs_of_nonneg_of_lt
        . apply Int.emod_nonneg; apply Int.neg_ne_zero.mpr; assumption
        . apply Int.emod_lt_of_pos; apply Int.neg_pos_of_neg; assumption
      . apply Int.natAbs_lt_natAbs_of_nonneg_of_lt
        . apply Int.emod_nonneg; assumption
        . apply Int.emod_lt_of_pos; assumption
    if r.natAbs < r'.natAbs
    then rw [decide_eq_true, decide_eq_true] <;> decreasing_tactic
    else rw [decide_eq_true, decide_eq_false] <;> decreasing_tactic

def linsolve (a b c d x y : Int) : LinSolution :=
  let det := a * d - b * c
  if det ≠ 0
  then if (x * d - b * y) % det = 0 ∧ (a * y - x * c) % det = 0
    then .unique  ((x * d - b * y) / det) ((a * y - x * c) / det)
    else .none
  else if a * y - x * c = 0
    then if a ≠ 0 ∨ b ≠ 0
      then linear a b x
      else if c ≠ 0 ∨ d ≠ 0
        then linear c d y
        else .plane
    else .none
  where
    linear a b x := let (gcd, e₀, f₀) := extended_gcd a 1 0 b 0 1
      if x % gcd = 0
      then let x₀ := x / gcd
        .line (e₀ * x₀) (f₀ * x₀) (-b / gcd) (a / gcd)
      else .none

inductive PosSolution
  | unique (e : Nat) (f : Nat)
  | ray (e : Nat) (f : Nat)
  | segment (e₁ : Nat) (f₁ : Nat) (e₂ : Nat) (f₂ : Nat)
  | plane
  | none
  deriving Repr

def possolve : LinSolution -> PosSolution
  | .unique e f => match Prod.mk <$> e.toNat' <*> f.toNat' with
    | some (e, f) => .unique e f
    | none => .none
  | .line e₀ f₀ δe δf =>
    let ray d := PosSolution.ray (e₀ + d * δe).toNat (f₀ + d * δf).toNat
    let segment d₁ d₂ := if d₁ ≤ d₂
      then PosSolution.segment
        (e₀ + d₁ * δe).toNat (f₀ + d₁ * δf).toNat
        (e₀ + d₂ * δe).toNat (f₀ + d₂ * δf).toNat
      else PosSolution.none
    match compare δe 0, compare δf 0 with
    | .lt, .lt => ray $ min (e₀.fdiv (-δe)) (f₀.fdiv (-δf))
    | .lt, .eq => if f₀ ≥ 0 then ray $ e₀.fdiv (-δe) else .none
    | .lt, .gt => segment (-(f₀.fdiv δf)) (e₀.fdiv (-δe))
    | .eq, .lt => if e₀ ≥ 0 then ray $ f₀.fdiv (-δf) else .none
    | .eq, .eq => .none
    | .eq, .gt => if e₀ ≥ 0 then ray $ -(f₀.fdiv δf) else .none
    | .gt, .lt => segment (f₀.fdiv (-δf)) (-(e₀.fdiv δe))
    | .gt, .eq => if f₀ ≥ 0 then ray $ -(e₀.fdiv δe) else .none
    | .gt, .gt => ray $ -min (e₀.fdiv δe) (f₀.fdiv δe)
  | .plane => .plane
  | .none => .none

def scoring
  | ((a, c), (b, d), (x, y)) => match possolve $ linsolve a b c d x y with
    | .unique e f => 3 * e + f
    | .none => 0
    | .plane => 0
    | .ray e f => 3 * e + f
    | .segment e₁ f₁ e₂ f₂ => min (3 * e₁ + f₁) (3 * e₂ + f₂)

def solution1 : Input → Nat
  := Array.foldl (λsum m => sum + scoring m) 0

def solution2 : Input → Int
  := Array.foldl (λsum (u, v, (x, y))
    => sum + scoring (u, v, (x + 10000000000000, y + 10000000000000))) 0

def main : IO Unit := IO.main parser solution1 solution2
