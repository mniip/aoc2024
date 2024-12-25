import Aoc2024

section Parser
open Parser
def parser : Parser (Array (Array Char) × Array (Array Char))
  := Prod.mk
    <$> ((string ", ").optional *> (anyChar.satisfies Char.isAlpha).many1
      <&> Subtype.val).many
    <* string "\n\n"
    <*> (anyChar.until (string "\n")).many

end Parser

def advance (buf : Array Char) (i : Fin (buf.size + 1)) (txt : Array Char)
  : Option (Fin (buf.size + 1)) :=
    let rec go j (p : i + j < buf.size + 1) := if _ : j < txt.size
      then if q : i + j < buf.size
        then if txt[j] = buf[i + j]
          then go (j + 1)
            $ by simp only [← Nat.add_assoc, Nat.add_lt_add_iff_right, q]
          else none
        else none
      else some ⟨i + j, p⟩
    go 0 $ by simp only [Nat.add_zero, Fin.is_lt]

def solution1 : Array (Array Char) × Array (Array Char) → Nat
  | (patterns, targets) => targets.toList.countP λtarget =>
    let _ : Append Unit := ⟨default⟩
    (Dijkstra.empty.init (α:=Fin (target.size + 1)) ⟨0, 0, ()⟩).until
      (· = Fin.last _)
      (λe => patterns.toList.filterMap
        λpat => (advance target e.into pat).map (⟨·, pat.size, ()⟩))
    |> Option.isSome

def solution2 : Array (Array Char) × Array (Array Char) → Nat
  | (patterns, targets) => List.sum $ targets.toList.map λtarget =>
    let _ : Append Nat := ⟨Nat.add⟩
    (Dijkstra.empty.init (α:=Fin (target.size + 1)) ⟨0, 0, 1⟩).until
      (· = Fin.last _)
      (λe => patterns.toList.filterMap
        λpat => (advance target e.into pat).map (⟨·, pat.size, e.link⟩))
    |> (·.elim 0 (·.1.link))


def main : IO Unit := IO.main parser solution1 solution2
