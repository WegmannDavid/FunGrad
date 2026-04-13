import Mathlib

open scoped BigOperators

/-!
# DiffMap: Bundled differentiable maps

We bundle a function `f`, its derivative `deriv`, and a proof `has_deriv` that `deriv`
is indeed the Fréchet derivative of `f` at every point.

The `has_deriv` field is `Prop`-valued, so it is computationally irrelevant —
Lean erases it during compilation, and the data fields `f` and `deriv` remain computable.
-/

/-- A helper to convert an `IsLinearMap` witness into a `ContinuousLinearMap`,
    using finite-dimensionality of Euclidean space. -/
noncomputable def IsLinearMap.toCLM {n m : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : IsLinearMap ℝ g) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap (IsLinearMap.mk' g hg)

@[simp]
lemma IsLinearMap.toCLM_apply {n m : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : IsLinearMap ℝ g)
    (x : EuclideanSpace ℝ (Fin n)) :
    IsLinearMap.toCLM g hg x = g x := by
      exact PiLp.ext (congrFun rfl)

structure DiffMap (n m : ℕ) where
  f : EuclideanSpace K (Fin n) → EuclideanSpace K (Fin m)
  deriv : (x : EuclideanSpace K (Fin n)) → (EuclideanSpace K (Fin n) → EuclideanSpace K (Fin m))
  deriv_linear : ∀ x, IsLinearMap ℝ (@deriv ℝ x)
  has_deriv : ∀ x, HasFDerivAt f (IsLinearMap.toCLM (deriv x) (deriv_linear x)) x

instance (n m : ℕ) : CoeFun (DiffMap n m) (fun _ => EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) where
  coe f := f.f

lemma IsLinearMap.comp_isLinear {R : Type*} [CommSemiring R]
    {E : Type*} [AddCommMonoid E] [Module R E]
    {F : Type*} [AddCommMonoid F] [Module R F]
    {G : Type*} [AddCommMonoid G] [Module R G]
    {g : F → G} {f : E → F}
    (hg : IsLinearMap R g) (hf : IsLinearMap R f) :
    IsLinearMap R (g ∘ f) := by
      constructor <;> intros <;> simp +decide [ hg.map_add, hg.map_smul, hf.map_add, hf.map_smul ]

lemma IsLinearMap.toCLM_comp {n m k : ℕ}
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hg : IsLinearMap ℝ g) (hf : IsLinearMap ℝ f) :
    (IsLinearMap.toCLM g hg).comp (IsLinearMap.toCLM f hf) =
    IsLinearMap.toCLM (g ∘ f) (hg.comp_isLinear hf) := by
      exact ContinuousLinearMap.ext fun x => by simp +decide [IsLinearMap.toCLM_apply]

/-- Composition of differentiable maps, implementing the chain rule.
    This is computable: both `f` and `deriv` are data, and the proof field is erased. -/
def DiffMap.comp {n m k : ℕ} (g : DiffMap m k) (f : DiffMap n m) : DiffMap n k where
  f := g.f ∘ f.f
  deriv x := g.deriv (f.f x) ∘ f.deriv x
  deriv_linear x := (g.deriv_linear (f.f x)).comp_isLinear (f.deriv_linear x)
  has_deriv x := by
    have hf := f.has_deriv x
    have hg := g.has_deriv (f.f x)
    have hcomp := hg.comp x hf
    rw [IsLinearMap.toCLM_comp] at hcomp
    exact hcomp

def DiffMap.id {n} : DiffMap n n where
  f x := x
  deriv x := sorry
