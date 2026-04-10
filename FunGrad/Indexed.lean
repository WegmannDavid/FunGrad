
class Index (I : Type) : Type 1 where
  iter {α : Type} : (I → α → α) → α → α

def sum [Index I] [Zero α] [Add α] (f : I → α) : α :=
  Index.iter (λ i a => a + f i) 0

instance UnitIsIndex : Index Unit where
  iter _ a := a

instance FinIsIndex (n : Nat) : Index (Fin n) where
  iter f a := (List.finRange n).foldl (λ a i => f i a) a

instance SumIsIndex (I₁ I₂ : Type) [Index I₁] [Index I₂] : Index (I₁ ⊕ I₂) where
  iter f a := Index.iter (λ i₁ => f (Sum.inl i₁)) (Index.iter (λ i₂ => f (Sum.inr i₂)) a)

instance ProdIsIndex (I₁ I₂ : Type) [Index I₁] [Index I₂] : Index (I₁ × I₂) where
  iter f a := Index.iter (λ i₁ b => Index.iter (λ i₂ => f (i₁, i₂)) b) a

class Indexed (C : Type) (I V : outParam Type) extends Index I where
  get : C → I → V
  ofFn : (I → V) → C

instance GetElemIndexed [Indexed C I V] : GetElem C I V (fun _ _ => true) where
  getElem c i _ := Indexed.get c i

instance SelfIsIndexed (C : Type) : Indexed C Unit C where
  get c _ := c
  ofFn f := f ()

instance VectorIsIndexed : Indexed (Vector α n) (Fin n) α where
  get v i := v.get i
  ofFn f := Vector.ofFn f

instance ProductIsIndexed [Indexed C₁ I₁ V] [Indexed C₂ I₂ V] : Indexed (C₁ × C₂) (I₁ ⊕ I₂) V where
  get c i := i.elim (λ i₁ => Indexed.get c.1 i₁) (λ i₂ => Indexed.get c.2 i₂)
  ofFn f := (Indexed.ofFn (λ i₁ => f (Sum.inl i₁)), Indexed.ofFn (λ i₂ => f (Sum.inr i₂)))

instance RecursiveIsIndex [Indexed C₂ I₂ C₁] [Indexed C₁ I₁ V] : Indexed C₂ (I₁ × I₂) V where
  get c i := Indexed.get (Indexed.get c i.2) i.1
  ofFn f := Indexed.ofFn (λ i₂ => Indexed.ofFn (λ i₁ => f (i₁, i₂)))

class HasDefaultIndexed I extends Index I where
  default : Type →  Type
  default_is_indexed V : Indexed (default V) I V := by exact inferInstance

instance DefaultIndexedIsIndexed [default : HasDefaultIndexed I] : Indexed (HasDefaultIndexed.default I V) I V := default.default_is_indexed V

instance VectorIsDefaultForFin (n : Nat) : HasDefaultIndexed (Fin n) where
  default V := Vector V n

instance ApplicativeDefaultForProd (I₁ I₂ : Type)
    [HasDefaultIndexed I₂]
    [HasDefaultIndexed I₁] : HasDefaultIndexed (I₁ × I₂) where
  default V := HasDefaultIndexed.default I₂ ((HasDefaultIndexed.default I₁ V))
  default_is_indexed _ := RecursiveIsIndex

abbrev Matrix (n m : Nat) (α : Type) : Type := HasDefaultIndexed.default (Fin n × Fin m) α

instance MatrixVectorMultiplication {n m : Nat} [Zero α] [Add α] [Mul α] : HMul (Matrix n m α) (Vector α m) (Vector α n) where
  hMul M v := Indexed.ofFn (λ i => sum (λ (j : Fin m) => M[(i, j)] * v[j]))
