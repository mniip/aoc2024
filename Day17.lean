import Aoc2024

structure Input where
  a : Nat
  b : Nat
  c : Nat
  program : Array (Fin 8)

section Parser
open Parser
def parser : Parser Input := Input.mk
  <$> (string "Register A: " *> nat <* string "\n")
  <*> (string "Register B: " *> nat <* string "\n")
  <*> (string "Register C: " *> nat <* string "\n")
  <*> (string "\nProgram: "
    *> ((string ",").optional *> fin8).many <* string "\n")
  where
    fin8 := nat.filterMap λn => if p : n < 8 then some ⟨n, p⟩ else none
end Parser

structure State where
  ip : Nat
  a : Nat
  b : Nat
  c : Nat

def step (s : State) (prog : Array (Fin 8)) : Option (State × Option (Fin 8))
  := do
    let literal : Fin 8 → Nat := λx => x
    let combo : Fin 8 → Option Nat
      | 0 => some 0
      | 1 => some 1
      | 2 => some 2
      | 3 => some 3
      | 4 => some s.a
      | 5 => some s.b
      | 6 => some s.c
      | 7 => none
    let insn ← prog[s.ip]?
    let op ← prog[s.ip + 1]?
    let s := { s with ip := s.ip + 2 }
    match insn with
    | 0 =>
      let val ← combo op
      some ({ s with a := s.a >>> val }, none)
    | 1 => some ({ s with b := s.b ^^^ literal op }, none)
    | 2 =>
      let val ← combo op
      some ({ s with b := val % 8 }, none)
    | 3 =>
      if s.a = 0
      then some (s, none)
      else some ({ s with ip := literal op }, none)
    | 4 => some ({ s with b := s.b ^^^ s.c }, none)
    | 5 =>
      let val ← combo op
      some (s, some ⟨val % 8, Nat.mod_lt _ (by decide)⟩)
    | 6 =>
      let val ← combo op
      some ({ s with b := s.a >>> val }, none)
    | 7 =>
      let val ← combo op
      some ({ s with c := s.a >>> val }, none)

partial def run (s : State) (prog : Array (Fin 8)) : Array (Fin 8) :=
  let rec go s arr := match step s prog with
    | none => arr
    | some (s, none) => go s arr
    | some (s, some n) => go s (arr.push n)
  go s #[]

def solution1 (input : Input) : String
  := run { ip := 0, a := input.a, b := input.b, c := input.c } input.program
    |> Array.toList
    |> List.map toString
    |> String.intercalate ","

partial def runAgainst (s : State) (prog : Array (Fin 8)) (out : Array (Fin 8))
  : Bool :=
  let rec go s i := match step s prog with
    | none => i = out.size
    | some (s, none) => go s i
    | some (s, some n) => out[i]? = some n ∧ go s (i + 1)
  go s 0

partial def solution2 (input : Input) : Nat := match input.program with
  | #[2, 4, 1, k₁, 7, 5, 0, 3, 1, k₂, 4, 7, 5, 5, 3, 0] =>
    let rec go a : List (Fin 8) → Option Nat
      | [] => some a
      | x :: xs => (List.range 8).findSome? λb =>
        let a := a <<< 3 ||| b
        if (b ^^^ a >>> (b ^^^ k₁)) % 8 = x ^^^ k₁ ^^^ k₂
        then go a xs
        else none
    (go 0 input.program.toList.reverse).getD 0
  | _ => default

def main : IO Unit := IO.main parser solution1 solution2
