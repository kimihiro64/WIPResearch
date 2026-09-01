import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RobinBV.NumberField.Definitions.RobinCriterion

/-!
# Colossally abundant objectives for ideals

The ideal CA objective is the ideal-divisor sum divided by the
`(1 + epsilon)` power of absolute norm. It is written as ideal abundancy
divided by the `epsilon` power so that its local factors are explicit.
-/

namespace RobinBV.NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The CA objective `sigma_K(I) / Norm(I)^(1 + epsilon)`. -/
noncomputable def idealCAObjective
    (epsilon : Real)
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) : Real :=
  idealAbundancy K I /
    (Ideal.absNorm
      (I : Ideal (_root_.NumberField.RingOfIntegers K)) : Real) ^ epsilon

/-- The contribution of exponent `e` at a prime ideal of absolute norm `q`
to the ideal CA objective. -/
noncomputable def idealCALocalFactor
    (epsilon : Real) (q e : Nat) : Real :=
  ((Finset.univ.sum fun j : Fin (e + 1) => (q : Real) ^ j.val) /
      (q : Real) ^ e) /
    (((q : Real) ^ e) ^ epsilon)

/-- The CA objective attached to an exponent profile on a fixed finite set of
prime ideals. -/
noncomputable def idealCAProfileObjective
    (epsilon : Real)
    (S : Finset (Ideal (_root_.NumberField.RingOfIntegers K)))
    (exponent : Ideal (_root_.NumberField.RingOfIntegers K) -> Nat) : Real :=
  S.prod fun P =>
    idealCALocalFactor epsilon (Ideal.absNorm P) (exponent P)

/-- A nonzero integral ideal globally maximizes the CA objective at the given
parameter. -/
def IsColossallyAbundantIdeal
    (epsilon : Real)
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) : Prop :=
  forall J : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K)),
    idealCAObjective K epsilon J <= idealCAObjective K epsilon I

end RobinBV.NumberField
