/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.Coprime.Lemmas
import RobinBV.Mathlib.Analysis.SpecialFunctions.Log.GeometricTail
import RobinBV.Mathlib.NumberTheory.PrimePow.FiniteSum
import RobinBV.Mathlib.NumberTheory.PrimePow.LogCutoff

/-!
# Finite and geometric prime-power corrections for Dirichlet characters

The exact finite Mangoldt correction is paired with the complete local
geometric-logarithm remainder at a prime. Both statements retain the actual
character value, including zero and the resonant value one.

The pointwise conductor identity adapts
BombieriVinogradov.DirichletCharacter.natCast_sub_primitiveCharacter_eq
at commit 1ed555f755ef71491890143de49f2f3fdb9d8c7e (Apache-2.0).
The candidate has no dependency on that project.
-/

set_option autoImplicit false

namespace DirichletCharacter

noncomputable section

/-- At a noncoprime argument changing level removes the full primitive value;
at a coprime argument it preserves that value exactly. -/
theorem natCast_sub_primitiveCharacter_eq {N : Nat}
    (chi : DirichletCharacter Complex N) (n : Nat) :
    chi (n : ZMod N) - chi.primitiveCharacter (n : ZMod chi.conductor) =
      if Nat.Coprime n N then 0 else -chi.primitiveCharacter (n : ZMod chi.conductor) := by
  by_cases h : Nat.Coprime n N
  case pos =>
    rw [if_pos h]
    have hInt := chi.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr h)
    have hNat : chi.primitiveCharacter (n : ZMod chi.conductor) = chi (n : ZMod N) := by
      simpa only [Int.cast_natCast] using hInt
    rw [hNat, sub_self]
  case neg =>
    rw [if_neg h]
    have hZero : chi (n : ZMod N) = 0 :=
      chi.map_nonunit (fun hUnit => h ((ZMod.isUnit_iff_coprime n N).mp hUnit))
    rw [hZero, zero_sub]

/-- Complete finite Mangoldt conductor correction, expressed only with
Dirichlet characters and their canonical inducing primitive character. -/
theorem sum_vonMangoldt_mul_sub_primitive_eq
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (x : Nat) :
    Finset.sum (Finset.Icc 1 x) (fun n =>
      (ArithmeticFunction.vonMangoldt n : Complex) *
        (chi (n : ZMod N) - chi.primitiveCharacter (n : ZMod chi.conductor))) =
      -Finset.sum N.primeFactors (fun p =>
        (Real.log p : Complex) * Finset.sum (Finset.Icc 1 (Nat.log p x))
          (fun k => chi.primitiveCharacter (p : ZMod chi.conductor) ^ k)) := by
  classical
  let f : Nat -> Complex := fun n =>
    (ArithmeticFunction.vonMangoldt n : Complex) *
      chi.primitiveCharacter (n : ZMod chi.conductor)
  have hSupport : forall n : Nat, Not (IsPrimePow n) -> f n = 0 := by
    intro n hn
    dsimp only [f]
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
    simp
  have hPoint (n : Nat) :
      (ArithmeticFunction.vonMangoldt n : Complex) *
        (chi (n : ZMod N) - chi.primitiveCharacter (n : ZMod chi.conductor)) =
      -(if Nat.Coprime n N then 0 else f n) := by
    rw [natCast_sub_primitiveCharacter_eq]
    by_cases hn : Nat.Coprime n N
    case pos =>
      rw [if_pos hn, if_pos hn]
      simp
    case neg =>
      rw [if_neg hn, if_neg hn]
      exact mul_neg _ _
  simp_rw [hPoint]
  rw [Finset.sum_neg_distrib,
    Nat.sum_nonCoprime_eq_sum_primeFactors_sum_pow f hSupport (NeZero.ne N) x]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hpPrime := (Nat.mem_primeFactors.mp hp).1
  have hkNe : Not (k = 0) := by have h := (Finset.mem_Icc.mp hk).1; omega
  dsimp only [f]
  rw [ArithmeticFunction.vonMangoldt_apply_pow hkNe,
    ArithmeticFunction.vonMangoldt_apply_prime hpPrime, Nat.cast_pow, map_pow]

/-- Dividing a character value by a prime puts the local ratio strictly
inside the unit disk, including nonunit character arguments. -/
theorem norm_primeRatio_lt_one
    {N : Nat} (chi : DirichletCharacter Complex N) {p : Nat} (hp : Nat.Prime p) :
    norm (chi (p : ZMod N) / (p : Complex)) < 1 := by
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hInvPos : 0 < Inv.inv (p : Real) := inv_pos.mpr hpPos
  have hMul : Inv.inv (p : Real) * (p : Real) = 1 := by field_simp [hpPos.ne']
  have hInv : Inv.inv (p : Real) < 1 := by nlinarith
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right (chi.norm_le_one _) hpPos.le).trans_lt
    (by simpa only [one_div] using hInv)

/-- The exact shifted local tail at a prime with the genuine character
Euler denominator. The cutoff-position remainder is not discarded. -/
theorem primePowerGeometricTail_identity
    {N : Nat} (chi : DirichletCharacter Complex N) {p : Nat} (hp : Nat.Prime p)
    (K : Nat) {u : Real} (hu0 : 0 <= u) (hu1 : u <= 1) :
    (((K : Real) + u : Real) : Complex) *
        Complex.shiftedGeometricLogTail (chi (p : ZMod N) / (p : Complex)) K =
      chi (p : ZMod N) / ((p : Complex) - chi (p : ZMod N)) -
        Complex.shiftedGeometricLogRemainder (chi (p : ZMod N) / (p : Complex)) K u := by
  rw [Complex.shiftedGeometricLogTail_identity (chi.norm_primeRatio_lt_one hp) K hu0 hu1]
  congr 1
  have hpNe : Not ((p : Complex) = 0) := by exact_mod_cast hp.ne_zero
  have hDen : Not ((p : Complex) - chi (p : ZMod N) = 0) := by
    intro h
    have hEq : chi (p : ZMod N) = (p : Complex) := (sub_eq_zero.mp h).symm
    have hNorm := chi.norm_le_one (p : ZMod N)
    rw [hEq, Complex.norm_natCast] at hNorm
    have hOne : (1 : Real) < p := by exact_mod_cast hp.one_lt
    linarith
  field_simp [hpNe, hDen]

/-- Full prime-power Chebyshev contribution at a real cutoff. -/
def primePowerChebyshevStep {N : Nat} (chi : DirichletCharacter Complex N)
    (p : Nat) (t : Real) : Complex :=
  (Real.log p : Complex) * Finset.sum (Finset.Icc 1 (Nat.log p (Nat.floor t)))
    (fun k => chi (p : ZMod N) ^ k)

/-- Resonance counts exactly character value one; zero and every other
character value contribute zero to the logarithmic main term. -/
def primePowerResonance {N : Nat} (chi : DirichletCharacter Complex N) (p : Nat) : Nat := by
  classical
  exact if chi (p : ZMod N) = 1 then 1 else 0

/-- An explicit constant for the complete prime-power step error, retaining
the nonresonant character denominator. -/
def primePowerStepErrorBound {N : Nat} (chi : DirichletCharacter Complex N) (p : Nat) : Real := by
  classical
  exact if chi (p : ZMod N) = 1 then Real.log p
    else 2 * Real.log p * norm (chi (p : ZMod N)) / norm (1 - chi (p : ZMod N))

theorem primePowerStepErrorBound_nonneg
    {N : Nat} (chi : DirichletCharacter Complex N) {p : Nat} (hp : Nat.Prime p) :
    0 <= chi.primePowerStepErrorBound p := by
  classical
  have hLog : 0 <= Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  unfold primePowerStepErrorBound
  split_ifs <;> positivity

/-- Removing exactly the resonant logarithm leaves a uniformly bounded
error for the complete prime-power step, with no ERH hypothesis. -/
theorem norm_primePowerChebyshevStep_sub_resonance_log_le
    {N : Nat} (chi : DirichletCharacter Complex N) {p : Nat} (hp : Nat.Prime p)
    {t : Real} (ht : 1 <= t) :
    norm (chi.primePowerChebyshevStep p t -
      (chi.primePowerResonance p : Complex) * (Real.log t : Complex)) <=
        chi.primePowerStepErrorBound p := by
  classical
  have hLog : 0 <= Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  by_cases hRes : chi (p : ZMod N) = 1
  case pos =>
    have hGap := Nat.log_sub_log_floor_mul_log_bounds hp.one_lt ht
    have hExpression : chi.primePowerChebyshevStep p t -
        (chi.primePowerResonance p : Complex) * (Real.log t : Complex) =
        (((Nat.log p (Nat.floor t) : Real) * Real.log p - Real.log t : Real) : Complex) := by
      simp [primePowerChebyshevStep, primePowerResonance, hRes]
      ring
    rw [hExpression, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith [hGap.1])]
    simp only [primePowerStepErrorBound, if_pos hRes]
    linarith [hGap.2]
  case neg =>
    simp only [primePowerResonance, if_neg hRes, Nat.cast_zero, zero_mul, sub_zero,
      primePowerChebyshevStep, primePowerStepErrorBound]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLog]
    calc
      _ <= Real.log p * (2 * norm (chi (p : ZMod N)) / norm (1 - chi (p : ZMod N))) :=
        mul_le_mul_of_nonneg_left
          (Complex.norm_sum_pow_Icc_one_le hRes (chi.norm_le_one _) _) hLog
      _ = _ := by ring

end

end DirichletCharacter
