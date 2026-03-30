import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Bicategory.Basic

structure Paramorphism (A B : Type) : Type 1 where
  P : Type
  I : P → A → B

def paraComp {A B C : Type} (f : Paramorphism A B) (g : Paramorphism B C) : Paramorphism A C where
  P := f.P × g.P
  I := λ ⟨p, q⟩ a => g.I q (f.I p a)



instance ParamHomCategory : CategoryTheory.Category (Paramorphism A B) where
  Hom f g := f.P → g.P
  id f := λ p => p
  comp α β := β ∘ α

def whiskerLeft {A B C : Type} (f : Paramorphism A B) {g h : Paramorphism B C} (η : g ⟶ h) : paraComp f g ⟶ paraComp f h :=
  λ ⟨p, q⟩ => ⟨p, η q⟩

def whiskerRight {A B C : Type} {f g : Paramorphism A B} (η : f ⟶ g) (h : Paramorphism B C) : paraComp f h ⟶ paraComp g h :=
  λ ⟨p, q⟩ => ⟨η p, q⟩

def leftUnitor {A B : Type} (f : Paramorphism A B) : paraComp { P := Unit, I := λ _ a => a } f ≅ f :=
  { hom := λ ⟨_, p⟩ => p
    inv := λ p => ⟨(), p⟩ }

def rightUnitor {A B : Type} (f : Paramorphism A B) : paraComp f { P := Unit, I := λ _ a => a } ≅ f :=
  { hom := λ ⟨p, _⟩ => p
    inv := λ p => ⟨p, ()⟩ }

def associator (f : Paramorphism A B) (g : Paramorphism B C) (h : Paramorphism C D) :
paraComp (paraComp f g) h ≅ paraComp f (paraComp g h) :=
  { hom := λ ⟨⟨p, q⟩, r⟩ => ⟨p, ⟨q, r⟩⟩
    inv := λ ⟨p, ⟨q, r⟩⟩ => ⟨⟨p, q⟩, r⟩ }


instance Param : CategoryTheory.Bicategory Type where
  Hom := Paramorphism
  id := λ A => { P := Unit, I := λ _ a => a }
  comp := λ f g => { P := f.P × g.P, I := λ ⟨p, q⟩ a => g.I q (f.I p a) }
  homCategory := λ A B => ParamHomCategory
  associator := associator
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
