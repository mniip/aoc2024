import Aoc2024

section Parser
open Parser
def parser : Parser (Array (Array Nat))
  := ((whitespace *> nat).until (string "\n")).many
end Parser

inductive Directed1 (α : Type) where
  | empty
  | one (value : α)
  | failed
def Directed1.push (pred : α → α → Bool) : Directed1 α → α → Directed1 α
  | empty, x => one x
  | one l, x => if pred l x
    then one x
    else failed
  | failed, _ => failed

abbrev Check1 α := Directed1 α × Directed1 α
def Check1.init : Check1 α := (.empty, .empty)
def Check1.push (pred : α → α → Bool) : Check1 α → α  → Check1 α
  | (u, d), x => (u.push pred x, d.push (flip pred) x)
def Check1.ok : Check1 α → Bool
  | (.failed, .failed) => false
  | _ => true

inductive Directed2 (α : Type) where
  | skipped (_ : Directed1 α)
  | one (value : α)
  | two (last last' : α)
def Directed2.push (pred : α → α → Bool) : Directed2 α → α → Directed2 α
  | one l, x => two l x
  | two l' l, x => match pred l' l, pred l' x || pred l x with
    | true, true => two l x
    | true, false => skipped (.one l)
    | false, true => skipped (.one x)
    | false, false => skipped .failed
  | skipped .empty, x => one x
  | skipped s, x => skipped (s.push pred x)

abbrev Check2 α := Directed2 α × Directed2 α
def Check2.init : Check2 α := (.skipped .empty, .skipped .empty)
def Check2.push (pred : α → α → Bool) : Check2 α → α → Check2 α
  | (u, d), x => (u.push pred x, d.push (flip pred) x)
def Check2.ok : Check2 α → Bool
  | (.skipped .failed, .skipped .failed) => false
  | _ => true

def solution1 : Array (Array Nat) → Nat
  | input => input.toList.countP
    $ Check1.ok ∘ Array.foldl (Check1.push pred) Check1.init
  where pred a b := a + 1 ≤ b && b ≤ a + 3

def solution2 : Array (Array Nat) → Nat
  | input => input.toList.countP
    $ Check2.ok ∘ Array.foldl (Check2.push pred) Check2.init
  where pred a b := a + 1 ≤ b && b ≤ a + 3

def main : IO Unit := IO.main parser solution1 solution2
