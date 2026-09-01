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

theorem RobinBV.ideal_divisor_norm_sum_eq_prod_geometric
    {K : Type*} [Field K] [NumberField K]
    (I : nonZeroDivisors
      (Ideal (NumberField.RingOfIntegers K)))
    [DecidablePred (fun J : Ideal (NumberField.RingOfIntegers K) =>
      Dvd.dvd J (I : Ideal (NumberField.RingOfIntegers K)))] :
    Finset.sum
        (Ideal.finite_setOfPred_absNorm_le
          (Ideal.absNorm
            (I : Ideal (NumberField.RingOfIntegers K)))).toFinset
        (fun J =>
          if Dvd.dvd J (I : Ideal (NumberField.RingOfIntegers K)) then
            Ideal.absNorm J
          else 0) =
      Finset.univ.prod
        (fun P : {P : Ideal (NumberField.RingOfIntegers K) //
            Membership.mem
              (normalizedFactors
                (I : Ideal (NumberField.RingOfIntegers K))).toFinset P} =>
          Finset.univ.sum
            (fun j : Fin (Multiset.count P.val
                (normalizedFactors
                  (I : Ideal (NumberField.RingOfIntegers K))) + 1) =>
              Ideal.absNorm P.val ^ j.val)) := by
  classical
  have h := RobinBV.NumberField.idealDivisorSum_eq_prod_geometric I
  unfold RobinBV.NumberField.idealDivisorSum
    RobinBV.NumberField.idealsUpToNorm at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro J _hJ
  by_cases hDvd : Dvd.dvd J
      (I : Ideal (NumberField.RingOfIntegers K))
  next => simp [hDvd]
  next => simp [hDvd]

theorem RobinBV.ideal_abundancy_eq_prod_local
    {K : Type*} [Field K] [NumberField K]
    (I : nonZeroDivisors
      (Ideal (NumberField.RingOfIntegers K)))
    [DecidablePred (fun J : Ideal (NumberField.RingOfIntegers K) =>
      Dvd.dvd J (I : Ideal (NumberField.RingOfIntegers K)))] :
    ((Finset.sum
        (Ideal.finite_setOfPred_absNorm_le
          (Ideal.absNorm
            (I : Ideal (NumberField.RingOfIntegers K)))).toFinset
        (fun J =>
          if Dvd.dvd J (I : Ideal (NumberField.RingOfIntegers K)) then
            Ideal.absNorm J
          else 0) : Nat) : Real) /
        (Ideal.absNorm
          (I : Ideal (NumberField.RingOfIntegers K)) : Real) =
      Finset.univ.prod
        (fun P : {P : Ideal (NumberField.RingOfIntegers K) //
            Membership.mem
              (normalizedFactors
                (I : Ideal (NumberField.RingOfIntegers K))).toFinset P} =>
          (Finset.univ.sum
            (fun j : Fin (Multiset.count P.val
                (normalizedFactors
                  (I : Ideal (NumberField.RingOfIntegers K))) + 1) =>
              (Ideal.absNorm P.val : Real) ^ j.val)) /
            ((Ideal.absNorm P.val : Real) ^
              Multiset.count P.val
                (normalizedFactors
                  (I : Ideal (NumberField.RingOfIntegers K))))) := by
  classical
  have h := RobinBV.NumberField.idealAbundancy_eq_prod_local I
  unfold RobinBV.NumberField.idealAbundancy
    RobinBV.NumberField.idealDivisorSum
    RobinBV.NumberField.idealsUpToNorm at h
  convert h using 1
  apply congrArg (fun x : Real => x /
    (Ideal.absNorm
      (I : Ideal (NumberField.RingOfIntegers K)) : Real))
  apply congrArg (fun n : Nat => (n : Real))
  apply Finset.sum_congr rfl
  intro J _hJ
  by_cases hDvd : Dvd.dvd J
      (I : Ideal (NumberField.RingOfIntegers K))
  next => simp [hDvd]
  next => simp [hDvd]
