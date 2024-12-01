def Parser α
  := (b : ByteArray) → Fin (b.size + 1) → Option (α × Fin (b.size + 1))

instance : Monad Parser where
  pure x := λ_ n => (x, n)
  bind k m := λb n => match k b n with
    | none => none
    | some (x, n') => m x b n'

def Parser.eof : Parser Unit
  := λb n => if n == b.size then some ((), n) else none

def Parser.parse (p : Parser α) : ByteArray → Option α
  := λb => Prod.fst <$> (p <* eof) b 0

def Parser.anyChar : Parser Char
  := λb n => do
    let ch ← String.utf8DecodeChar? b n
    let n' := n + ch.utf8Size
    if p : n' < b.size + 1 then some (ch, ⟨n', p⟩) else none

def Parser.bytes (bytes : ByteArray) : Parser Unit
  := λb n => if p : n + bytes.size < b.size + 1
    then
      let rec
        go (i : Nat) : Option (Unit × Fin (b.size + 1))
          := if _ : i < bytes.size
            then if b[n + i] == bytes[i]
              then go (i + 1)
              else none
            else some ((), ⟨n + bytes.size, p⟩)
      go 0
    else none

def Parser.string (s : String) : Parser Unit := bytes s.toUTF8

def Parser.optional (p : Parser α) : Parser (Option α)
  := λb n => match p b n with
    | none => some (none, n)
    | some (x, n') => some (some x, n')

def Parser.satisfies (pred : α → Bool) (p : Parser α) : Parser α
  := λb n => do
    let (x, n') ← p b n
    if pred x then some (x, n') else none

instance : Inhabited (Parser α) where
  default := λ_ _ => none

partial def Parser.foldlMany (f : α → β → α) (init : α) (p : Parser β)
  : Parser α
  := λb n => match p b n with
    | none => some (init, n)
    | some (x, n') => foldlMany f (f init x) p b n'

def Parser.foldlMany1 (f : α → β → α) (init : β → α) (p : Parser β)
  : Parser α
  := λb n => match p b n with
    | none => none
    | some (x, n') => foldlMany f (init x) p b n'

def Parser.many (p : Parser α) : Parser (Array α)
  := p.foldlMany Array.push #[]

private abbrev List1 α := { xs : List α // xs ≠ [] }

def Parser.many1 (p : Parser α) : Parser { xs : Array α // xs ≠ #[] }
  := p.foldlMany1 (α:={ xs : Array α // _ })
    (λ⟨xs, _⟩ x => ⟨xs.push x, by intro p; injection p; simp at *⟩)
    (λx => ⟨#[x], by intro p; injection p; contradiction⟩)

def Parser.nat : Parser Nat
  := (anyChar.satisfies Char.isDigit).foldlMany1
    (λn c => n * 10 + (c.toNat - '0'.toNat))
    (λc => c.toNat - '0'.toNat)

def Parser.int : Parser Int
  := do
    let sign ← (string "-").optional
    let signify := match sign with
      | none => Int.ofNat
      | some _ => Int.neg ∘ Int.ofNat
    signify <$> nat

def Parser.whitespace : Parser Unit
  := (anyChar.satisfies Char.isWhitespace).foldlMany default default
