import FunGrad.Indexed

structure FSpace where
  S : Type
  I : Type
  indexed : Indexed S I Float

abbrev T (X : Type) (_ : X) := X

class HasComputableDerivative [Indexed A I Float] [Indexed B J Float] (f : A → B) where
  D : (x : A) → T A x → T B (f x)

instance Compose {f : A → B} {g : B → C}
  [Indexed A I Float] [Indexed B J Float] [Indexed C K Float]
  [Df : HasComputableDerivative f] [Dg : HasComputableDerivative g] :
    HasComputableDerivative (g ∘ f) where
  D x := (Dg.D (f x)) ∘ (Df.D x)


structure ParameterizedDifferentialMap (P A B) [Indexed P I Float] [Indexed A J Float] [Indexed B K Float] where
  I : P → A → B
  Dp : ∀ a : A, HasComputableDerivative (λ p ↦ I p a)
  Da : ∀ p : P, HasComputableDerivative (I p)

def parameterizedCompose {A B C : Type}
  [Indexed P I Float] [Indexed Q J Float] [Indexed A K Float] [Indexed B L Float] [Indexed C M Float]
  (g : ParameterizedDifferentialMap Q B C) (f : ParameterizedDifferentialMap P A B) : ParameterizedDifferentialMap (P × Q) A C where
  I := λ ⟨p, q⟩ a => g.I q (f.I p a)
  Dp := λ a => sorry
  Da := λ p => sorry
