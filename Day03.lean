import Aoc2024

inductive Insn where
  | Mul : Int → Int → Insn
  | Do : Insn
  | Dont : Insn

section Parser
open Parser
def parser : Parser (Array Insn)
  := ((some <$> insn).orElse (Functor.mapConst none anyChar)).foldlMany
    (λa m => m.elim a a.push)
    Array.empty
  where
    insn :=
      Parser.orElse
        (string "mul(" *> Insn.Mul <$> int <* string "," <*> int <* string ")")
        $ Parser.orElse
          (Functor.mapConst Insn.Do $ string "do()")
          (Functor.mapConst Insn.Dont $ string "don't()")
end Parser

def solution1 : Array Insn → Int
  | input => input.foldl
    λ
      | acc, .Mul x y => acc + x * y
      | acc, _ => acc
    0

def solution2 : Array Insn → Int
  | input => Prod.snd $ input.foldl
    λ
      | (true, acc), .Mul x y => (true, acc + x * y)
      | (false, acc), .Mul _ _ => (false, acc)
      | (_, acc), .Do => (true, acc)
      | (_, acc), .Dont => (false, acc)
    (true, 0)

def main : IO Unit := IO.main parser solution1 solution2
