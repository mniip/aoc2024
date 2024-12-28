import Aoc2024

inductive Op where
  | and
  | or
  | xor

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

def solution2
  : Array (String × Bool) × Array (String × Op × String × String) → String
  := default

def main : IO Unit := IO.main parser solution1 solution2
