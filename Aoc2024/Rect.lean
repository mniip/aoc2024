def Rect (width : Nat) (height : Nat) (α : Type) : Type :=
  { rows : Array { cells : Array α // cells.size = width }
  // rows.size = height
  }

abbrev SomeRect α := (w : Nat) × (h : Nat) × Rect w h α

def Rect.fromArray? : Array (Array α) → Option (SomeRect α)
  | arr => if _ : arr.size > 0
    then
      let width := arr[0].size
      arr.mapM (λrow => if p : row.size = width
        then some ⟨row, p⟩
        else none)
      <&> λrows => ⟨width, rows.size, ⟨rows, rfl⟩⟩
    else some ⟨0, 0, ⟨#[], rfl⟩⟩

def Rect.mk : α → Rect width height α
  | x =>
    ⟨ Array.mkArray height ⟨Array.mkArray width x, Array.size_mkArray ..⟩
    , Array.size_mkArray ..
    ⟩

def Rect.tabulate (f : Fin width × Fin height → α) : Rect width height α :=
 ⟨ Array.ofFn λy => ⟨Array.ofFn λx => f (x, y), Array.size_ofFn ..⟩
 , Array.size_ofFn ..
 ⟩

def Rect.toArray (r : Rect width height α) : Array (Array α)
  := r.val.map Subtype.val

def Rect.get (r : Rect width height α) : Fin width × Fin height → α
  | (⟨x, _⟩, ⟨y, _⟩) =>
    let ⟨rows, _⟩ := r
    let ⟨cells, _⟩ := rows[y]
    cells[x]

instance : GetElem (Rect width height α) (Fin width × Fin height) α
  λ_ _ => True where
  getElem r i _ := r.get i

instance : GetElem (Rect width height α) (Nat × Nat) α
  λ_ (x, y) => x < width ∧ y < height where
  getElem r | (x, y), ⟨p, q⟩ => r.get (⟨x, p⟩, ⟨y, q⟩)

instance : GetElem (Rect width height α) (Int × Int) α
  λ_ (x, y) => x ≥ 0 ∧ x < width ∧ y ≥ 0 ∧ y < height where
  getElem r
    | (x, y), ⟨e, p, f, q⟩ => r.get
      ( ⟨x.toNat, (Int.toNat_lt e).mpr p⟩
      , ⟨y.toNat, (Int.toNat_lt f).mpr q⟩
      )

def Rect.index? : Int × Int → Option (Fin width × Fin height)
  | (x, y) => do
    let x' ← x.toNat'
    let y' ← y.toNat'
    if p : x' < width
    then
      if q : y' < height
      then some (⟨x', p⟩, ⟨y', q⟩)
      else none
    else none

def Rect.get? (r : Rect width height α) : Int × Int → Option α
  | p => r.get <$> index? p

def Rect.getD (r : Rect width height α) : Int × Int → (dflt : α) → α
  | p, dflt => (index? p).elim dflt r.get

def Rect.set (r : Rect width height α)
  : Fin width × Fin height → α → Rect width height α
  | (⟨x, p⟩, ⟨y, _⟩), v =>
    ⟨ r.val.modify y λ⟨row, e⟩ =>
      ⟨row.set ⟨x, e ▸ p⟩ v, by rw [Array.size_set, e]⟩
    , by rw [Array.size_modify, r.property]
    ⟩

def Rect.setD (r : Rect width height α) : Int × Int → α → Rect width height α
  | (x, y), v => match Prod.mk <$> x.toNat' <*> y.toNat' with
    | some (x', y') =>
      ⟨ r.val.modify y' λ⟨row, e⟩ =>
        ⟨row.setD x' v, by rw [Array.size_setD, e]⟩
      , by rw [Array.size_modify, r.property]
      ⟩
    | none => r

def Rect.map (f : α → β) (r : Rect width height α) : Rect width height β :=
  ⟨ r.val.map λ⟨row, e⟩ => ⟨row.map f, by rw [Array.size_map, e]⟩
  , by rw [Array.size_map, r.property]
  ⟩

instance : Functor (Rect width height) where
  map := Rect.map

def Rect.mapIdx (r : Rect width height α) (f : Fin width × Fin height → α → β)
  : Rect width height β :=
  ⟨ r.val.mapFinIdx λy ⟨row, e⟩ =>
    ⟨ row.mapFinIdx λx v => f (e ▸ x, r.property ▸ y) v
    , by rw [Array.size_mapFinIdx, e]
    ⟩
  , by rw [Array.size_mapFinIdx, r.property]
  ⟩

def Rect.foldl (r : Rect width height α) : (β → α → β) → β → β
  | f => r.val.foldl (λz row => row.val.foldl f z)

def Rect.foldlIdx (r : Rect width height α)
  : (β → Fin width × Fin height → α → β) → β → β
  | f => Fin.foldl height
    (λz y => Fin.foldl width (λz x => f z (x, y) $ r.get (x, y)) z)

def Rect.foldr (r : Rect width height α) : (α → β → β) → β → β
  | f => r.val.foldr (λrow => row.val.foldr f)

def Rect.foldrIdx (r : Rect width height α)
  : (Fin width × Fin height → α → β → β) → β → β
  | f => Fin.foldr height
    (λy => Fin.foldr width (λx => f (x, y) $ r.get (x, y)))

instance [Inhabited α] : Inhabited (Rect width height α) where
  default := Rect.mk default

instance : Inhabited (Rect 0 height α) where
  default := ⟨Array.mkArray height ⟨Array.empty, rfl⟩, Array.size_mkArray ..⟩

instance : Inhabited (Rect width 0 α) where
  default := ⟨Array.empty, rfl⟩

def Rect.findIdx? (pred : α → Bool) (r : Rect width height α)
  : Option (Fin width × Fin height) :=
  let rec goY y := if q : y < height
    then
      let ⟨row, _⟩ := r.val[y]'(r.property.symm ▸ q)
      let rec goX x := if p : x < width
        then if pred row[x]
          then some (⟨x, p⟩, ⟨y, q⟩)
          else goX (x + 1)
        else none
      (goX 0).orElse λ_ => goY (y + 1)
    else none
  goY 0
