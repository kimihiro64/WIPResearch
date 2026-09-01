import RobinBV

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

open UniqueFactorizationMonoid

theorem RobinBV.ca_mass_layer_decomposition
    {alpha : Type*} [DecidableEq alpha]
    (events : Finset alpha) (layer : alpha -> Nat) (mass : alpha -> Real) :
    (∑ e ∈ events, mass e) =
      (∑ e ∈ events.filter (fun e => layer e = 1), mass e) +
        ∑ e ∈ events.filter (fun e => layer e ≠ 1), mass e := by
  rw [Finset.sum_filter_add_sum_filter_not]

theorem RobinBV.ideal_eq_prod_primeFactors_pow
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : Not (I = 0)) :
    I =
      (normalizedFactors I).toFinset.prod
        (fun P => P ^ (normalizedFactors I).count P) := by
  exact Ideal.eq_prod_primeFactors_pow I hI

theorem RobinBV.ideal_absNorm_eq_prod_primeFactors_pow
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : Not (I = 0)) :
    Ideal.absNorm I =
      (normalizedFactors I).toFinset.prod
        (fun P => Ideal.absNorm P ^ (normalizedFactors I).count P) := by
  exact Ideal.absNorm_eq_prod_primeFactors_pow I hI

theorem RobinBV.ideal_primeFactor_norm_is_primePower
    {K : Type*} [Field K] [NumberField K]
    {I P : Ideal (NumberField.RingOfIntegers K)}
    (hP : 0 < Multiset.count P (normalizedFactors I)) :
    Exists fun p : Nat =>
      Exists fun n : Nat =>
        0 < n /\
          Membership.mem P (p : NumberField.RingOfIntegers K) /\
            Nat.Prime p /\ Ideal.absNorm P = p ^ n := by
  exact Ideal.exists_prime_and_absNorm_eq_pow_of_count_pos hP
