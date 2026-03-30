import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Bicategory.Basic

structure Learner (A B : Type) : Type 1 where
  P : Type
  I : P → A → B
  U : P → A → B → P
  r : P → A → B → A

def idLearner (A : Type) : Learner A A where
  P := Unit
  I := λ _ a => a
  U := λ _ _ _ => ()
  r := λ _ _ a => a

def learnerComp {A B C : Type} : Learner A B → Learner B C → Learner A C :=
  λ ⟨ P, I, U, r ⟩ ⟨ Q, J, V, s ⟩ ↦
  ⟨ P × Q,
    λ ⟨p, q⟩ a => J q (I p a),
    λ ⟨p, q⟩ a c => ⟨ U p a (s q (I p a) c), V q (I p a) c ⟩,
    λ ⟨p, q⟩ a c => r p a (s q (I p a) c) ⟩

structure learnerMorphism {A B : Type} (L M : Learner A B) where
  f : L.P → M.P
  U : M.I (f p) a = L.I p a := by simp[learnerComp, idLearner]
  r : M.r (f p) a c = L.r p a c := by simp[learnerComp, idLearner]

def learnerMorphismId {A B : Type} (L : Learner A B) : learnerMorphism L L where
  f := id

def learnerMorphismComp {A B : Type} {L M N : Learner A B} (f : learnerMorphism L M) (g : learnerMorphism M N) : learnerMorphism L N where
  f := g.f ∘ f.f
  U := by simp [f.U, g.U]
  r := by simp [f.r, g.r]

instance LearnHomCategory {A B : Type} : CategoryTheory.Category (Learner A B) where
  Hom f g := learnerMorphism f g
  id f := learnerMorphismId f
  comp α β := learnerMorphismComp α β



def whiskerLeft {A B C : Type} (f : Learner A B) {g h : Learner B C} (η : g ⟶ h) : learnerComp f g ⟶ learnerComp f h :=
 { f := λ ⟨p, q⟩ => ⟨p, η.f q⟩
   U := by intro p; cases p; cases η; simp[learnerComp]; grind
   r := by cases f; cases g; cases h; cases η; simp[learnerComp]; grind }

def whiskerRight {A B C : Type} {f g : Learner A B} (η : f ⟶ g) (h : Learner B C) : learnerComp f h ⟶ learnerComp g h :=
  { f := λ ⟨p, q⟩ => ⟨η.f p, q⟩
    U := by intro p; cases p; cases η; simp[learnerComp]; grind
    r := by cases f; cases g; cases h; cases η; simp[learnerComp]; grind }

def leftUnitor {A B : Type} (f : Learner A B) : learnerComp (idLearner A) f ≅ f :=
  { hom := { f := λ ⟨_, p⟩ => p }
    inv := { f := λ p => ⟨(), p⟩ } }

def rightUnitor {A B : Type} (f : Learner A B) : learnerComp f (idLearner B) ≅ f :=
  { hom := { f := λ ⟨p, _⟩ => p }
    inv := { f := λ p => ⟨p, ()⟩ } }

def associator (f : Learner A B) (g : Learner B C) (h : Learner C D) :
  learnerComp (learnerComp f g) h ≅ learnerComp f (learnerComp g h) :=
  { hom := { f := λ ⟨⟨p, q⟩, r⟩ => ⟨p, ⟨q, r⟩⟩ }
    inv := { f := λ ⟨p, ⟨q, r⟩⟩ => ⟨⟨p, q⟩, r⟩ } }


instance Learn : CategoryTheory.Bicategory Type where
  Hom := Learner
  id := λ A => idLearner A
  comp := λ f g => learnerComp f g
  homCategory := λ A B => LearnHomCategory
  associator := associator
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
