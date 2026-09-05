/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.Primorial
import RobinBV.Mathlib.NumberTheory.PrimePow.FiniteSum

/-!
# Full finite sums supported on prime powers

A prime-power-supported additive weight can be reindexed over every
prime below the cutoff and all its admitted positive exponents. The
primorial specializes the complete finite noncoprime reindexing theorem.
-/

set_option autoImplicit false

namespace Nat

/-- Reindex a complete finite prime-power-supported sum by its prime
base and every admitted positive exponent, including cutoff zero. -/
theorem sum_eq_sum_primesLE_sum_pow
    {R : Type*} [AddCommMonoid R] (f : Nat -> R)
    (hSupport : forall n : Nat, Not (IsPrimePow n) -> f n = 0) (x : Nat) :
    Finset.sum (Finset.Icc 1 x) f =
      Finset.sum (Nat.primesLE x) (fun p =>
        Finset.sum (Finset.Icc 1 (Nat.log p x)) (fun k => f (p ^ k))) := by
  classical
  have hCut : Finset.sum (Finset.Icc 1 x) f =
      Finset.sum (Finset.Icc 1 x) (fun n => if Nat.Coprime n (primorial x) then 0 else f n) := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hCoprime : Nat.Coprime n (primorial x)
    next =>
      rw [if_pos hCoprime]
      apply hSupport
      intro hPrimePow
      choose p k hp hk hPow using (isPrimePow_nat_iff n).1 hPrimePow
      have hDvd : Dvd.dvd p n := by
        rw [<- hPow]
        exact dvd_pow_self p hk.ne'
      have hpLe : p <= x := (Nat.le_of_dvd (by have h := (Finset.mem_Icc.mp hn).1; omega) hDvd).trans
        (Finset.mem_Icc.mp hn).2
      exact (hp.coprime_iff_not_dvd.mp (hCoprime.of_dvd_left hDvd)) (hp.dvd_primorial_iff.mpr hpLe)
    next =>
      rw [if_neg hCoprime]
  rw [hCut, Nat.sum_nonCoprime_eq_sum_primeFactors_sum_pow f hSupport (primorial_ne_zero x) x,
    primeFactors_primorial]

end Nat
