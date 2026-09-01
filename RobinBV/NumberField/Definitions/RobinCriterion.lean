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

/-- `K` has degree two over the rationals. -/
def IsQuadratic : Prop := Module.finrank Rat K = 2

/--
Schema for the candidate quadratic-field Robin criterion.

This is a research target, not a proved equivalence. The two analytic inputs
are parameters so that no unavailable Dedekind-zeta residue or zero predicate
is hidden inside the definition.
-/
def QuadraticRobinCriterion (dedekindERH : Prop) (kappa : Real) : Prop :=
  IsQuadratic K → (dedekindERH ↔ EventualIdealRobinBound K kappa)

end RobinBV.NumberField
