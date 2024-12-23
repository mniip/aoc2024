def Parser α
  := (b : ByteArray)
    → (i : {i // i ≤ b.size})
    → Option (α × {j // i.val ≤ j ∧ j ≤ b.size})

instance : Monad Parser where
  pure x := λ_ ⟨n, q⟩ => some (x, ⟨n, ⟨Nat.le_refl _, q⟩⟩)
  bind k m := λb ⟨n, q⟩ => match k b ⟨n, q⟩ with
    | none => none
    | some (x, ⟨n', ⟨p', q'⟩⟩) => match m x b ⟨n', q'⟩ with
      | none => none
      | some (y, ⟨n'', ⟨p'', q''⟩⟩)
        => some (y, ⟨n'', ⟨Nat.le_trans p' p'', q''⟩⟩)

def Parser.eof : Parser Unit
  := λb ⟨n, q⟩ => if n == b.size
    then some ((), ⟨n, ⟨Nat.le_refl _, q⟩⟩)
    else none

def Parser.parse (p : Parser α) : ByteArray → Option α
  := λb => Prod.fst <$> (p <* eof) b ⟨0, Nat.zero_le _⟩

def Parser.anyChar : Parser Char
  := λb ⟨n, _⟩ => do
    let ch ← String.utf8DecodeChar? b n
    let n' := n + ch.utf8Size
    if q : n' ≤ b.size
    then some (ch, ⟨n', ⟨Nat.le_add_right _ _, q⟩⟩)
    else none

def Parser.bytes (bytes : ByteArray) : Parser Unit
  := λb n => if q : n + bytes.size ≤ b.size
    then
      let rec
        go (i : Nat) := if _ : i < bytes.size
          then if b[n + i] == bytes[i]
            then go (i + 1)
            else none
          else some ((), ⟨n + bytes.size, ⟨Nat.le_add_right _ _, q⟩⟩)
      go 0
    else none

def Parser.string (s : String) : Parser Unit := bytes s.toUTF8

instance : OrElse (Parser α) where
  orElse p q := λb n => match p b n with
    | some (x, n') => some (x, n')
    | none => q () b n

def Parser.optional (p : Parser α) : Parser (Option α)
  := some <$> p <|> pure none

def Parser.filterMap (f : α → Option β) (p : Parser α) : Parser β
  := λb n => do
    let (x, n') ← p b n
    (f x).map (·, n')

def Parser.satisfies (pred : α → Bool) (p : Parser α) : Parser α
  := λb n => do
    let (x, n') ← p b n
    if pred x then some (x, n') else none

instance : Inhabited (Parser α) where
  default := λ_ _ => none

partial def Parser.loop (p : α → Parser (Sum β α)) (init : α) : Parser β
  := p init >>= λ
    | .inl y => pure y
    | .inr x => loop p x

def Parser.until (p : Parser α) (q : Parser β) : Parser (Array α)
  := Parser.loop
    (λxs => Functor.mapConst (.inl xs) q <|> (.inr ∘ xs.push) <$> p)
    Array.empty

def Parser.foldlMany (f : α → β → α) (init : α) (p : Parser β)
  : Parser α
  := Parser.loop (λx => (.inr ∘ f x) <$> p <|> pure (.inl x)) init

def Parser.foldlMany1 (f : α → β → α) (init : β → α) (p : Parser β)
  : Parser α
  := (init <$> p) >>= p.foldlMany f

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
