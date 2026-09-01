/-
Copyright (c) 2026 The RobinBV Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RobinBV Authors
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Prime-factor profiles of integral ideals

This file records the distinct-factor form of unique factorization for
nonzero integral ideals of a number field. It also transports that form
through the absolute norm and identifies the norm of every occurring prime
ideal as a rational-prime power.
-/

@[expose] public section

open UniqueFactorizationMonoid

namespace Ideal

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- A nonzero integral ideal is the product of its distinct prime factors
raised to their multiplicities. -/
theorem eq_prod_primeFactors_pow
    (I : Ideal (RingOfIntegers K)) (hI : Not (I = 0)) :
    I =
      (normalizedFactors I).toFinset.prod
        (fun P => P ^ (normalizedFactors I).count P) := by
  calc
    I = (normalizedFactors I).prod :=
      (Ideal.prod_normalizedFactors_eq_self hI).symm
    _ = (normalizedFactors I).toFinset.prod
        (fun P => P ^ (normalizedFactors I).count P) :=
      Finset.prod_multiset_count (normalizedFactors I)

/-- The absolute norm of a nonzero integral ideal is the product of the
norms of its distinct prime factors raised to their multiplicities. -/
theorem absNorm_eq_prod_primeFactors_pow
    (I : Ideal (RingOfIntegers K)) (hI : Not (I = 0)) :
    absNorm I =
      (normalizedFactors I).toFinset.prod
        (fun P => absNorm P ^ (normalizedFactors I).count P) := by
  calc
    absNorm I = absNorm (normalizedFactors I).prod := by
      rw [Ideal.prod_normalizedFactors_eq_self hI]
    _ = ((normalizedFactors I).map absNorm).prod :=
      map_multiset_prod absNorm (normalizedFactors I)
    _ = (normalizedFactors I).toFinset.prod
        (fun P => absNorm P ^ (normalizedFactors I).count P) :=
      Finset.prod_multiset_map_count (normalizedFactors I) absNorm

/-- Every prime ideal occurring in the normalized factorization of an
integral ideal has rational-prime-power absolute norm. -/
theorem exists_prime_and_absNorm_eq_pow_of_count_pos
    {I P : Ideal (RingOfIntegers K)}
    (hP : 0 < Multiset.count P (normalizedFactors I)) :
    Exists fun p : Nat =>
      Exists fun n : Nat =>
        0 < n /\
          Membership.mem P (p : RingOfIntegers K) /\
            Nat.Prime p /\ absNorm P = p ^ n := by
  have hPrime : Prime P :=
    prime_of_normalized_factor P (Multiset.count_pos.mp hP)
  let _ : P.IsMaximal :=
    (isPrime_of_prime hPrime).isMaximal hPrime.ne_zero
  exact exists_prime_and_absNorm_eq_pow P

end Ideal
