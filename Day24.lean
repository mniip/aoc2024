import Aoc2024

inductive Op where
  | and
  | or
  | xor
  deriving BEq

section Parser
open Parser
def parser
  : Parser (Array (String × Bool) × Array (String × Op × String × String))
  := Prod.mk <$> wire.many <* string "\n" <*> node.many
  where
    ident := (anyChar.satisfies Char.isAlphanum).many1
      <&> (String.mk ∘ Array.toList ∘ Subtype.val)
    op := Functor.mapConst .and (string "AND")
      <|> Functor.mapConst .or (string "OR")
      <|> Functor.mapConst .xor (string "XOR")
    bool := Functor.mapConst false (string "0")
      <|> Functor.mapConst true (string "1")
    wire := Prod.mk <$> ident <* string ": " <*> bool <* string "\n"
    node := (·, ·, ·, ·)
      <$> ident
      <* string " "
      <*> op
      <* string " "
      <*> ident
      <* string " -> "
      <*> ident
      <* string "\n"
end Parser

partial def solution1
  : Array (String × Bool) × Array (String × Op × String × String) → Nat
  | (wires, nodes) =>
    let rec circuit := Lean.RBMap.empty (cmp:=compare)
      |> wires.foldl
        (λm (w, b) => m.insert w $ Thunk.mk λ_ => b)
      |> nodes.foldl
        (λm (i₁, op, i₂, o) => m.insert o $ Thunk.mk λ_ =>
          let x := (circuit.find? i₁).elim false Thunk.get
          let y := (circuit.find? i₂).elim false Thunk.get
          match op with
          | .and => x && y
          | .or => x || y
          | .xor => xor x y)
    let zs := circuit.toList.filter (λ(name, _) => name.startsWith "z")
      |> (·.mergeSort λ(name₁, _) (name₂, _) => name₁ ≥ name₂)
      |> List.map λ(_, thunk) => thunk.get
    zs.foldl (λn b => 2 * n + b.toNat) 0

def adder
  : List (α × α × α) × α
    → Array ((Nat ⊕ α) × Op × (Nat ⊕ α) × (Nat ⊕ α))
  | (wires, lastCarry) =>
    let rec go
      | i, none, arr, (x, y, z) :: ws =>
        let arr := arr.push (.inr x, .xor, .inr y, .inr z)
        let arr := arr.push (.inr x, .and, .inr y, .inl i)
        go (i + 1) (some i) arr ws
      | i, some carry, arr, (x, y, z) :: ws@(_ :: _) =>
        let arr := arr.push (.inr x, .xor, .inr y, .inl i)
        let arr := arr.push (.inl i, .xor, .inl carry, .inr z)
        let arr := arr.push (.inl i, .and, .inl carry, .inl (i + 1))
        let arr := arr.push (.inr x, .and, .inr y, .inl (i + 2))
        let arr := arr.push (.inl (i + 1), .or, .inl (i + 2), .inl (i + 3))
        go (i + 4) (some (i + 3)) arr ws
      | i, some carry, arr, [(x, y, z)] =>
        let arr := arr.push (.inr x, .xor, .inr y, .inl i)
        let arr := arr.push (.inl i, .xor, .inl carry, .inr z)
        let arr := arr.push (.inl i, .and, .inl carry, .inl (i + 1))
        let arr := arr.push (.inr x, .and, .inr y, .inl (i + 2))
        let arr := arr.push (.inl (i + 1), .or, .inl (i + 2), .inr lastCarry)
        arr
      | _, _, _, [] => default
    go (0 : Nat) none #[] wires

inductive Nondet (α : Type) : Type where
  | nil : Nondet α
  | cons : α → (Unit → Nondet α) → Nondet α

def Nondet.orElse (xs : Nondet α) (k : Unit → Nondet α) : Nondet α
  := match xs with
    | .nil => k ()
    | .cons x k' => .cons x λ_ => (k' ()).orElse k

instance : OrElse (Nondet α) where orElse := Nondet.orElse

def Nondet.bind (xs : Nondet α) (f : α → Nondet β) : Nondet β
  := match xs with
    | .nil => .nil
    | .cons x k => f x <|> (k ()).bind f

instance : Monad Nondet where
  pure x := .cons x λ_ => .nil
  bind := Nondet.bind

structure MatchState (α : Type) [Ord α] where
  pending : Lean.RBMap Int α compare
  confirmed : Lean.RBMap Int α compare
  swapped : Lean.RBMap α α compare

def MatchM α [Ord α] := StateT (MatchState α) Nondet

instance [Ord α] : OrElse (MatchM α β) where
  orElse f g s := OrElse.orElse (f s) (λ_ => g () s)

instance [Ord α] : Monad (MatchM α)
  := inferInstanceAs (Monad (StateT (MatchState α) Nondet))

def matchInput [BEq α] [Ord α] : (Nat ⊕ α) → α → MatchM α Unit
  | .inr name, name', state => if name == name'
    then pure ((), state)
    else .nil
  | .inl i, name', state => match state.pending.find? i with
    | some name => if name != name'
      then
        pure
        ( ()
        , { pending := state.pending.erase i
          , confirmed := state.confirmed.insert i name'
          , swapped := (state.swapped.insert name name').insert name' name
          }
        )
      else .nil
    | none => match state.confirmed.find? i with
      | some name => if name == name'
        then pure ((), state)
        else .nil
      | none => .nil

def matchOutput [BEq α] [Ord α] : (Nat ⊕ α) → α → MatchM α Unit
  | .inr name, name', state => match state.swapped.find? name with
    | some name'' => if name'' == name
      then pure ((), state)
      else .nil
    | none => if name == name'
      then pure ((), state)
      else match state.swapped.find? name' with
        | some _ => .nil
        | none =>
          pure
          ( ()
          , { state
            with swapped := (state.swapped.insert name name').insert name' name
            }
          )
  | .inl i, name', state => match state.swapped.find? name' with
    | some name => pure
      ( ()
      , { state with confirmed := state.confirmed.insert i name }
      )
    | none => .cons
      ((), { state with confirmed := state.confirmed.insert i name' })
      λ_ => pure ((), { state with pending := state.pending.insert i name' })

def matchGraphs [Ord α] [BEq α] (graph : Array (α × Op × α × α))
  (template : Array ((Nat ⊕ α) × Op × (Nat ⊕ α) × (Nat ⊕ α)))
  : Option (List (α × α)) :=
    let rec go i unnamed : MatchM α Unit := if _ : i < template.size
      then do
        let (i₁, op, i₂, o) := template[i]
        let name : α ← unnamed.fold
          (λrs o' (i₁', op', i₂') => if op == op'
            then rs <|> do
              (matchInput i₁ i₁' *> matchInput i₂ i₂' *> matchOutput o o')
                <|> (matchInput i₁ i₂' *> matchInput i₂ i₁' *> matchOutput o o')
              pure o'
            else rs)
          (λ_ => Nondet.nil)
        go (i + 1) (unnamed.erase name)
      else pure ()
    let g₀ := graph.foldl
      (λm (i₁, op, i₂, o) => m.insert o (i₁, op, i₂))
      (Lean.RBMap.empty (cmp:=compare))
    let s₀ : MatchState α :=
      { pending := Lean.RBMap.empty
      , confirmed := Lean.RBMap.empty
      , swapped := Lean.RBMap.empty
      }
    match StateT.run (go 0 g₀) s₀ with
    | .nil => none
    | .cons (_, s) _ => some s.swapped.toList

def solution2
  : Array (String × Bool) × Array (String × Op × String × String) → String
  | (_, graph) =>
    let sz := (graph.size + 3) / 5
    let vars := List.range sz
      |> List.map (λn => s!"{n / 10}{n % 10}")
      |> List.map (λs => ("x" ++ s, "y" ++ s, "z" ++ s))
      |> (·, s!"z{sz / 10}{sz % 10}")
    match matchGraphs graph (adder vars) with
    | some swaps => swaps.map Prod.fst
      |> List.mergeSort
      |> ",".intercalate
    | none => ""

def main : IO Unit := IO.main parser solution1 solution2
