import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Candidate Robin inequality for ideals

The definitions below isolate a precise ideal-theoretic inequality while
leaving the analytic identifications explicit. In particular, `kappa` is an
input until it is connected to the residue of the Dedekind zeta function, and
`dedekindERH` is an input until a formal zero statement is available.
-/

namespace RobinBV.NumberField

open scoped BigOperators

variable (K : Type*) [Field K] [NumberField K]

/-- Integral ideals of norm at most `B`, as a finite set. -/
noncomputable def idealsUpToNorm (B : Nat) :
    Finset (Ideal (NumberField.RingOfIntegers K)) :=
  (Ideal.finite_setOfPred_absNorm_le B).toFinset

/-- Sum of the norms of all integral ideal divisors of a nonzero ideal. -/
noncomputable def idealDivisorSum
    (I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K))) : Nat :=
  by
    classical
    exact
      ∑ J ∈ idealsUpToNorm K
          (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K))),
        if J ∣ (I : Ideal (NumberField.RingOfIntegers K)) then Ideal.absNorm J else 0

/-- Ideal abundancy `sigma_K(I) / Norm(I)`. -/
noncomputable def idealAbundancy
    (I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K))) : Real :=
  idealDivisorSum K I / Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K))

/-- Candidate eventual Robin bound with an explicit residue constant. -/
def EventualIdealRobinBound (kappa : Real) : Prop :=
  ∃ X : Nat,
    ∀ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)),
    X < Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) →
      (idealDivisorSum K I : Real) <
        Real.exp Real.eulerMascheroniConstant * kappa *
          Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) *
            Real.log (Real.log (Ideal.absNorm
              (I : Ideal (NumberField.RingOfIntegers K)) : Real))

/-- Eventual ideal Robin bound with a correction at the critical ERH scale.
The correction in abundancy is `C / sqrt(log Norm(I))`, hence the divisor-sum
correction is `C * Norm(I) / sqrt(log Norm(I))`. -/
def EventualIdealRobinBoundWithCriticalCorrection
    (kappa correction : Real) : Prop :=
  Exists fun X : Nat =>
    forall I : nonZeroDivisors
        (Ideal (NumberField.RingOfIntegers K)),
      X < Ideal.absNorm
          (I : Ideal (NumberField.RingOfIntegers K)) ->
        (idealDivisorSum K I : Real) <
          Real.exp Real.eulerMascheroniConstant * kappa *
              Ideal.absNorm
                (I : Ideal (NumberField.RingOfIntegers K)) *
              Real.log (Real.log (Ideal.absNorm
                (I : Ideal (NumberField.RingOfIntegers K)) : Real)) +
            correction * Ideal.absNorm
              (I : Ideal (NumberField.RingOfIntegers K)) /
                Real.sqrt (Real.log (Ideal.absNorm
                  (I : Ideal (NumberField.RingOfIntegers K)) : Real))

/-- There is a nonnegative field-dependent correction for which the eventual
critical-scale ideal Robin bound holds. -/
def CriticalScaleIdealRobinBound (kappa : Real) : Prop :=
  Exists fun correction : Real =>
    And (0 <= correction)
      (EventualIdealRobinBoundWithCriticalCorrection K kappa correction)

/-- `K` has degree two over the rationals. -/
def IsQuadratic : Prop := Module.finrank Rat K = 2

/--
Schema for the critical-scale quadratic-field Robin criterion.

This is a research target, not a proved equivalence. The two analytic inputs
are parameters so that no unavailable Dedekind-zeta residue or zero predicate
is hidden inside the definition. The bare exact bound remains available as
`EventualIdealRobinBound`; the criterion uses the field-dependent correction
suggested by the critical-line error scale.
-/
def QuadraticRobinCriterion (dedekindERH : Prop) (kappa : Real) : Prop :=
  IsQuadratic K -> (dedekindERH <-> CriticalScaleIdealRobinBound K kappa)

end RobinBV.NumberField
