import FunGrad.Diff
import FunGrad.Learn

class error_map where
  cmp : Float → Float → Float
  d_cmp : ∀ x, HasComputableDerivative (cmp x)
  d_cmp_inv : Float → Float → Float

def Backprop (ε : Float) (e : error_map)
  [Indexed P I Float] [Indexed A J Float] [Indexed B K Float]
  (f : ParameterizedDifferentialMap P A B) :
    Learner A B :=

  let E b : ParameterizedDifferentialMap P A Float := sorry
  { P := P
    I := f.I
    U := λ p a b => p - ε * (E b).Dp a p
    r := λ p a b => _ }
