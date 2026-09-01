import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Finite mass layer decomposition

This Mathlib-only statement is the abstract finite partition used by the CA
prime-exponent decomposition. The project-specific event model and its
application remain behind `Solution.lean`.
-/

namespace RobinBV

open UniqueFactorizationMonoid

/-- A finite mass splits exactly into layer one and all remaining layers. -/
theorem ca_mass_layer_decomposition
    {alpha : Type*} [DecidableEq alpha]
    (events : Finset alpha) (layer : alpha -> Nat) (mass : alpha -> Real) :
    (∑ e ∈ events, mass e) =
      (∑ e ∈ events.filter (fun e => layer e = 1), mass e) +
        ∑ e ∈ events.filter (fun e => layer e ≠ 1), mass e := by
  sorry

/-- A nonzero integral ideal is reconstructed from its distinct normalized
prime factors and their multiplicities. -/
theorem ideal_eq_prod_primeFactors_pow
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : Not (I = 0)) :
    I =
      (normalizedFactors I).toFinset.prod
        (fun P => P ^ (normalizedFactors I).count P) := by
  sorry

/-- Absolute norm transports the canonical prime-ideal exponent profile to
an exact product of prime-ideal norms. -/
theorem ideal_absNorm_eq_prod_primeFactors_pow
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : Not (I = 0)) :
    Ideal.absNorm I =
      (normalizedFactors I).toFinset.prod
        (fun P => Ideal.absNorm P ^ (normalizedFactors I).count P) := by
  sorry

/-- Every ideal in the canonical support has rational-prime-power absolute
norm. -/
theorem ideal_primeFactor_norm_is_primePower
    {K : Type*} [Field K] [NumberField K]
    {I P : Ideal (NumberField.RingOfIntegers K)}
    (hP : 0 < Multiset.count P (normalizedFactors I)) :
    Exists fun p : Nat =>
      Exists fun n : Nat =>
        0 < n /\
          Membership.mem P (p : NumberField.RingOfIntegers K) /\
            Nat.Prime p /\ Ideal.absNorm P = p ^ n := by
  sorry

end RobinBV
