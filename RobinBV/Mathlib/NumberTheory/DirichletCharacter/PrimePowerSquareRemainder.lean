/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimePowerRemainder
import RobinBV.Mathlib.NumberTheory.PrimePow.TotalSum

/-!
# Complete square-layer extraction from character Chebyshev sums

The full Mangoldt sum is reindexed by every prime and admitted exponent.
After the prime and square terms, the entire remaining contribution has
the elementary third-root logarithmic bound, uniformly in the character.
-/

set_option autoImplicit false

namespace DirichletCharacter

noncomputable section

/-- The complete character-weighted Mangoldt sum is the sum of every
prime's entire positive-power contribution, with no cutoff restriction. -/
theorem sum_vonMangoldt_eq_sum_primePowerHigherStep_zero
    {N : Nat} (chi : DirichletCharacter Complex N) (t : Real) :
    Finset.sum (Finset.Icc 1 (Nat.floor t)) (fun n =>
      (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod N)) =
      Finset.sum (Nat.primesLE (Nat.floor t)) (fun p => chi.primePowerHigherStep p 0 t) := by
  classical
  let f : Nat -> Complex := fun n => (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod N)
  have hSupport : forall n : Nat, Not (IsPrimePow n) -> f n = 0 := by
    intro n hn
    dsimp only [f]
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
    simp
  change Finset.sum (Finset.Icc 1 (Nat.floor t)) f = _
  rw [Nat.sum_eq_sum_primesLE_sum_pow f hSupport]
  apply Finset.sum_congr rfl
  intro p hp
  unfold primePowerHigherStep
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkNe : Not (k = 0) := by have h := (Finset.mem_Icc.mp hk).1; omega
  dsimp only [f]
  rw [ArithmeticFunction.vonMangoldt_apply_pow hkNe,
    ArithmeticFunction.vonMangoldt_apply_prime (Nat.mem_primesLE.mp hp).2, Nat.cast_pow, map_pow]

/-- Exact prime, square and entire higher-power decomposition. The
square uses the squared character, including its values at nonunits. -/
theorem sum_vonMangoldt_eq_prime_add_square_add_higher
    {N : Nat} (chi : DirichletCharacter Complex N) {t : Real} (ht : 1 <= t) :
    Finset.sum (Finset.Icc 1 (Nat.floor t)) (fun n =>
      (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod N)) =
      chi.primeChebyshevSum (Nat.floor t) +
        (chi ^ 2).primeChebyshevSum (Nat.floor (t ^ (Inv.inv (2 : Real)))) +
          Finset.sum (Nat.primesLE (Nat.floor t)) (fun p => chi.primePowerHigherStep p 2 t) := by
  have hRoot : t ^ (Inv.inv (2 : Real)) <= t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ht
      (show Inv.inv (2 : Real) <= 1 by norm_num)
  have hFloor : Nat.floor (t ^ (Inv.inv (2 : Real))) <= Nat.floor t := Nat.floor_mono hRoot
  have hFirst := chi.sum_primePowerHigherStep_eq_primeMoment_add_higher (Nat.floor t) 0 ht
  have hSecond := chi.sum_primePowerHigherStep_eq_primeMoment_add_higher (Nat.floor t) 1 ht
  simp only [Nat.zero_add, Nat.cast_one, inv_one, Real.rpow_one, min_self, pow_one] at hFirst
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hSecond
  simp only [one_div, min_eq_right hFloor] at hSecond
  rw [chi.sum_vonMangoldt_eq_sum_primePowerHigherStep_zero t, hFirst, hSecond]
  ring

/-- The full error after removing the prime and square layers has a
third-root logarithmic bound for all characters and every real cutoff >=1. -/
theorem norm_sum_vonMangoldt_sub_prime_sub_square_le
    {N : Nat} (chi : DirichletCharacter Complex N) {t : Real} (ht : 1 <= t) :
    norm (Finset.sum (Finset.Icc 1 (Nat.floor t)) (fun n =>
      (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod N)) -
        chi.primeChebyshevSum (Nat.floor t) -
          (chi ^ 2).primeChebyshevSum (Nat.floor (t ^ (Inv.inv (2 : Real))))) <=
      t ^ (Inv.inv (3 : Real)) * Real.log t := by
  rw [chi.sum_vonMangoldt_eq_prime_add_square_add_higher ht]
  have hIdentity (a b c : Complex) : a + b + c - a - b = c := by ring
  rw [hIdentity]
  simpa only [Nat.reduceAdd, Nat.cast_ofNat] using
    chi.norm_sum_primePowerHigherStep_le_root_log (Nat.floor t) 2 ht

end

end DirichletCharacter
