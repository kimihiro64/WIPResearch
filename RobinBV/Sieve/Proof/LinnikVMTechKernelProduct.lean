/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.FejerKernel
import RobinBV.Sieve.Proof.LinnikOrdinaryBlock

/-!
# Kernel-product consumer for Vinogradov's technical estimate

Theorem 24.7 produces one symmetric coefficient sum for every polynomial
degree.  This module substitutes the complete Lemma 24.6 range estimate into
each factor and then into their finite product.  Thus the rational
approximation losses remain explicit before the Holder exponents are applied.
-/

open Complex

theorem finiteFejerKernel_two_pi_le_linnikReciprocalSquareKernel
    (H : Nat) (hH : 0 < H) (x : Real) :
    finiteFejerKernel H (2 * Real.pi * x) <=
      linnikReciprocalSquareKernel (H : Real) x := by
  let eps : Real := x - (round x : Real)
  let d : Real := linnikNearestIntDist x
  have hd : d = abs eps := by rfl
  have hdle : d <= 1 / 2 := linnikNearestIntDist_le_half x
  have hperiod :
      finiteFejerKernel H (2 * Real.pi * x) =
        finiteFejerKernel H (2 * Real.pi * eps) := by
    have hp := (finiteFejerKernel_periodic H).sub_int_mul_eq
      (x := 2 * Real.pi * x) (round x)
    calc
      finiteFejerKernel H (2 * Real.pi * x) =
          finiteFejerKernel H
            (2 * Real.pi * x - (round x : Real) * (2 * Real.pi)) := hp.symm
      _ = finiteFejerKernel H (2 * Real.pi * eps) := by
        congr 1
        simp only [eps]
        ring
  have habs :
      finiteFejerKernel H (2 * Real.pi * eps) =
        finiteFejerKernel H (2 * Real.pi * d) := by
    rw [hd]
    by_cases heps : 0 <= eps
    next =>
      rw [abs_of_nonneg heps]
    next =>
      have hepsNeg : eps < 0 := lt_of_not_ge heps
      rw [abs_of_neg hepsNeg]
      have harg : 2 * Real.pi * eps =
          -(2 * Real.pi * (-eps)) := by ring
      rw [harg, finiteFejerKernel_neg]
  rw [hperiod, habs]
  by_cases hd0 : d = 0
  next =>
    rw [linnikReciprocalSquareKernel, if_pos]
    next => exact finiteFejerKernel_le_card H (2 * Real.pi * d)
    next => simpa [d] using hd0
  next =>
    have hdPos : 0 < d := lt_of_le_of_ne (linnikNearestIntDist_nonneg x)
      (Ne.symm hd0)
    have hHReal : 0 < (H : Real) := by exact_mod_cast hH
    have htPos : 0 < 2 * Real.pi * d := by positivity
    have htLe : 2 * Real.pi * d <= Real.pi := by
      nlinarith [Real.pi_pos]
    have hspace := finiteFejerKernel_le_spacing H
      (2 * Real.pi * d) htPos htLe
    rw [linnikReciprocalSquareKernel, if_neg]
    next =>
      apply le_min
      next => exact finiteFejerKernel_le_card H (2 * Real.pi * d)
      next =>
        calc
          finiteFejerKernel H (2 * Real.pi * d) <=
              Real.pi ^ 2 /
                ((H : Real) * (2 * Real.pi * d) ^ 2) := hspace
          _ = 1 / (4 * (H : Real) * d ^ 2) := by
            field_simp
            ring
          _ <= 1 / ((H : Real) * d ^ 2) := by
            apply one_div_le_one_div_of_le
            next => positivity
            next => nlinarith [sq_nonneg d]
    next =>
      simpa [d] using hd0

theorem linnik_symmetric_kernel_envelope_le
    (Y alpha theta : Real) (a q G : Nat)
    (hY : 0 < Y) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (htheta : abs theta <= 1)
    (halpha : alpha = (a : Real) / q + theta / (q : Real) ^ 2) :
    2 * Finset.sum (Finset.range (G + 1)) (fun n =>
      linnikReciprocalSquareKernel Y ((n : Real) * alpha)) <=
      48 * ((((G + 1 : Nat) : Real) * Y) / q + (G + 1) + Y + q) := by
  have h := linnik_ordinary_range_kernel_sum_le
    Y alpha theta a q (G + 1) hY hq hcop htheta halpha
  norm_num only [Nat.cast_add, Nat.cast_one] at h
  norm_num only [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem linnik_kernel_product_envelope_le
    {I : Type*} (s : Finset I)
    (Y alpha theta : I -> Real) (a q G : I -> Nat)
    (hY : forall i, Membership.mem s i -> 0 < Y i)
    (hq : forall i, Membership.mem s i -> 0 < q i)
    (hcop : forall i, Membership.mem s i -> Nat.Coprime (a i) (q i))
    (htheta : forall i, Membership.mem s i -> abs (theta i) <= 1)
    (halpha : forall i, Membership.mem s i ->
      alpha i = (a i : Real) / q i + theta i / (q i : Real) ^ 2) :
    Finset.prod s (fun i =>
      2 * Finset.sum (Finset.range (G i + 1)) (fun n =>
        linnikReciprocalSquareKernel (Y i) ((n : Real) * alpha i))) <=
      Finset.prod s (fun i =>
        48 * (((((G i + 1 : Nat) : Real) * Y i) / q i) +
          (G i + 1) + Y i + q i)) := by
  apply Finset.prod_le_prod
  next =>
    intro i hi
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro n hn
    exact linnikReciprocalSquareKernel_nonneg
      (Y i) ((n : Real) * alpha i) (hY i hi).le
  next =>
    intro i hi
    exact linnik_symmetric_kernel_envelope_le
      (Y i) (alpha i) (theta i) (a i) (q i) (G i)
      (hY i hi) (hq i hi) (hcop i hi) (htheta i hi) (halpha i hi)
