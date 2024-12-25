import Lean.Data.RBMap

def PQueue (α β : Type) [Ord α] : Type
  := Lean.RBMap α { bs : List β // bs ≠ [] } compare

def PQueue.empty [Ord α] : PQueue α β := Lean.RBMap.empty

def PQueue.push [Ord α] (k : α) (v : β) (q : PQueue α β) : PQueue α β
  := match q.find? k with
    | none => q.insert k ⟨[v], List.cons_ne_nil _ _⟩
    | some ⟨vs, _⟩ => q.insert k ⟨v :: vs, List.cons_ne_nil _ _⟩

def PQueue.pop [Ord α] (q : PQueue α β) : Option (α × β × PQueue α β)
  := q.min.map λ(k, ⟨v :: vs, _⟩) => match vs with
    | [] => (k, v, q.erase k)
    | vs'@e:(_ :: _) => (k, v, q.insert k ⟨vs', e ▸ List.cons_ne_nil _ _⟩)

def PQueue.remove [Ord α] [BEq β] (q : PQueue α β) (k : α) (v : β) : PQueue α β
  := match ((q.find? k).elim [] Subtype.val).erase v with
    | [] => q.erase k
    | vs@e:(_ :: _) => q.insert k ⟨vs, e ▸ List.cons_ne_nil _ _⟩

structure Dijkstra (α β ω : Type) [Ord α] [Ord ω]
  where
  pending : Lean.RBMap α (Option (ω × β)) compare
  queue : PQueue ω α

def Dijkstra.empty [Ord α] [Ord ω] : Dijkstra α β ω :=
  { pending := Lean.RBMap.empty
  , queue := PQueue.empty
  }

structure Dijkstra.Edge (α β ω : Type) : Type where
  into : α
  weight : ω
  link : β

def Dijkstra.init [Ord α] [Append β] [Ord ω]
  (e : Edge α β ω) (d : Dijkstra α β ω)
  : Dijkstra α β ω :=
    match d.pending.find? e.into with
    | none =>
      { pending := d.pending.insert e.into (some (e.weight, e.link))
      , queue := d.queue.push e.weight e.into
      }
    | some none => d
    | some (some (w, l)) => match compare e.weight w with
      | .lt =>
        let _ : BEq α := Ord.toBEq inferInstance
        { pending := d.pending.insert e.into (some (e.weight, e.link))
        , queue := (d.queue.remove w e.into).push e.weight e.into
        }
      | .eq =>
        { pending := d.pending.insert e.into (some (w, e.link ++ l))
        , queue := d.queue
        }
      | .gt => d

def Dijkstra.step [Ord α] [Append β] [Ord ω] [Add ω] (d : Dijkstra α β ω)
  : Option (Edge α β ω × (List (Edge α β ω) → Dijkstra α β ω))
  := d.queue.pop.bind λ(_, v, queue) =>
    (d.pending.find? v).join.map λ⟨w, b⟩ =>
      ( ⟨v, w, b⟩
      , λes => es.foldl
        (λd e => d.init { e with weight := w + e.weight })
        { pending := d.pending.insert v none
        , queue := queue
        }
      )

partial def Dijkstra.until [Ord α] [Append β] [Ord ω] [Add ω]
  (d : Dijkstra α β ω) (pred : α → Bool) (adj : Edge α β ω → List (Edge α β ω))
  : Option {e : Edge α β ω // pred e.into} :=
    let rec
      go d := match d.step with
      | none => none
      | some (e, k) => if p : pred e.into
        then some ⟨e, p⟩
        else go (k (adj e))
    go d

partial def Dijkstra.foldUntil [Ord α] [Append β] [Ord ω] [Add ω]
  (d : Dijkstra α β ω) (pred : α → Bool) (adj : Edge α β ω → List (Edge α β ω))
  (f : σ → (e : Edge α β ω) → pred e.into = false → σ)
  (g : σ → (e : Edge α β ω) → pred e.into = true → Dijkstra α β ω → τ)
  (h : σ → Dijkstra α β ω → τ)
  (s₀ : σ) : τ :=
    let rec
      go [Nonempty τ] d s  := match d.step with
      | none => h s d
      | some (e, k) => if p : pred e.into
        then g s e p d
        else go (k (adj e)) (f s e (eq_false_of_ne_true p))
    @go ⟨h s₀ d⟩ d s₀

def Dijkstra.fold [Ord α] [Append β] [Ord ω] [Add ω]
  (d : Dijkstra α β ω) (adj : Edge α β ω → List (Edge α β ω))
  (f : σ → Edge α β ω → σ) (s₀ : σ) : σ :=
    d.foldUntil (λ_ => false) adj (λs e _ => f s e)
      (λ_ _ _ => by contradiction) (λs _ => s) s₀
