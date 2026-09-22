/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMVTSharpGlobal

/-!
# Component estimates for the sharp Linnik VMVT coefficient

This module bounds the recurrence multiplier and collision allowance at their
source-sized exponential scales. It also supplies the elementary exponential
absorption lemma used by the coefficient induction.
-/

theorem linnikVMVTStepMultiplier_le_exp_six
    (k : Nat) (hk : 2 <= k) :
    linnikVMVTStepMultiplier k <=
      Real.exp (6 * (k : Real) ^ 2 * Real.log k) := by
  have hkPos : 0 < k := by omega
  have hkOne : 1 <= k := by omega
  have hk2Nat : 4 <= k ^ 2 := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ <= k ^ 2 := Nat.pow_le_pow_left hk 2
  have hband := linnikVMVT_band_base_le_power 0 k hk
  have h32 : 32 * (k ^ 3 + 1) ^ 2 <= k ^ 13 :=
    (le_max_right (max k 0) (32 * (k ^ 3 + 1) ^ 2)).trans hband
  have hpolyNat : 4 * (k ^ 3 + 1) ^ 2 <= k ^ 13 := by
    exact (Nat.mul_le_mul_right ((k ^ 3 + 1) ^ 2) (by norm_num)).trans h32
  have hpoly : 4 * ((k ^ 3 + 1 : Nat) : Real) ^ 2 <= (k : Real) ^ 13 := by
    exact_mod_cast hpolyNat
  have hkk : k <= k ^ 2 := by
    calc
      k = k * 1 := by ring
      _ <= k * k := Nat.mul_le_mul_left k hkOne
      _ = k ^ 2 := by ring
  have hfactNat : k.factorial <= k ^ (k ^ 2) :=
    (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_right hkPos hkk)
  have hfact : (k.factorial : Real) <= (k : Real) ^ (k ^ 2) := by
    exact_mod_cast hfactNat
  have hexpOne : Real.exp 1 <= (k : Real) ^ 2 := by
    have hsource := Real.exp_one_lt_d9
    have hk2 : (4 : Real) <= (k : Real) ^ 2 := by exact_mod_cast hk2Nat
    norm_num at hsource
    linarith
  have htwoNat : 2 ^ (k ^ 2) <= k ^ (k ^ 2) :=
    Nat.pow_le_pow_left hk (k ^ 2)
  have htwo : (2 : Real) ^ ((k : Real) ^ 2) <=
      (k : Real) ^ (k ^ 2) := by
    calc
      (2 : Real) ^ ((k : Real) ^ 2) =
          (2 : Real) ^ ((k ^ 2 : Nat) : Real) := by norm_cast
      _ = (2 : Real) ^ (k ^ 2 : Nat) := Real.rpow_natCast 2 (k ^ 2)
      _ <= (k : Real) ^ (k ^ 2 : Nat) := by exact_mod_cast htwoNat
  have hpowNat : k ^ (15 + 2 * k ^ 2) <= k ^ (6 * k ^ 2) := by
    apply Nat.pow_le_pow_right hkPos
    omega
  have hpow : (k : Real) ^ (15 + 2 * k ^ 2) <=
      (k : Real) ^ (6 * k ^ 2) := by exact_mod_cast hpowNat
  calc
    linnikVMVTStepMultiplier k =
        4 * ((k ^ 3 + 1 : Nat) : Real) ^ 2 *
          (k.factorial : Real) * Real.exp 1 *
            (2 : Real) ^ ((k : Real) ^ 2) := rfl
    _ <= (k : Real) ^ 13 * (k.factorial : Real) * Real.exp 1 *
        (2 : Real) ^ ((k : Real) ^ 2) := by
      gcongr
    _ <= (k : Real) ^ 13 * (k : Real) ^ (k ^ 2) * Real.exp 1 *
        (2 : Real) ^ ((k : Real) ^ 2) := by
      gcongr
    _ <= (k : Real) ^ 13 * (k : Real) ^ (k ^ 2) * (k : Real) ^ 2 *
        (2 : Real) ^ ((k : Real) ^ 2) := by
      gcongr
    _ <= (k : Real) ^ 13 * (k : Real) ^ (k ^ 2) * (k : Real) ^ 2 *
        (k : Real) ^ (k ^ 2) := by
      gcongr
    _ = (k : Real) ^ (15 + 2 * k ^ 2) := by ring
    _ <= (k : Real) ^ (6 * k ^ 2) := hpow
    _ = ((k ^ (6 * k ^ 2) : Nat) : Real) := by norm_cast
    _ = Real.exp (((6 * k ^ 2 : Nat) : Real) * Real.log k) :=
      nat_power_cast_eq_exp_for_linnikVMVT k (6 * k ^ 2) hkPos
    _ = Real.exp (6 * (k : Real) ^ 2 * Real.log k) := by
      congr 1
      push_cast
      ring

theorem linnikVMVTCollision_le_exp_three
    (k r : Nat) (hk : 2 <= k) :
    ((4 ^ (k * r) * k ^ (4 * (k * r)) : Nat) : Real) <=
      Real.exp (3 * (r : Real) * (k : Real) ^ 2 * Real.log k) := by
  have hkPos : 0 < k := by omega
  have hk2Nat : 4 <= k ^ 2 := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ <= k ^ 2 := Nat.pow_le_pow_left hk 2
  have hfour : 4 ^ (k * r) <= k ^ (2 * (k * r)) := by
    calc
      4 ^ (k * r) <= (k ^ 2) ^ (k * r) :=
        Nat.pow_le_pow_left hk2Nat (k * r)
      _ = k ^ (2 * (k * r)) := by ring
  have hprod : 4 ^ (k * r) * k ^ (4 * (k * r)) <=
      k ^ (6 * k * r) := by
    calc
      4 ^ (k * r) * k ^ (4 * (k * r)) <=
          k ^ (2 * (k * r)) * k ^ (4 * (k * r)) :=
        Nat.mul_le_mul_right _ hfour
      _ = k ^ (6 * k * r) := by ring
  have h2k : 2 * k <= k * k := Nat.mul_le_mul_right k hk
  have h6k : 6 * k <= 3 * k ^ 2 := by
    calc
      6 * k = 3 * (2 * k) := by ring
      _ <= 3 * (k * k) := Nat.mul_le_mul_left 3 h2k
      _ = 3 * k ^ 2 := by ring
  have hexp : 6 * k * r <= 3 * r * k ^ 2 := by
    calc
      6 * k * r <= (3 * k ^ 2) * r := Nat.mul_le_mul_right r h6k
      _ = 3 * r * k ^ 2 := by ring
  have hnat : 4 ^ (k * r) * k ^ (4 * (k * r)) <=
      k ^ (3 * r * k ^ 2) :=
    hprod.trans (Nat.pow_le_pow_right hkPos hexp)
  calc
    ((4 ^ (k * r) * k ^ (4 * (k * r)) : Nat) : Real) <=
        ((k ^ (3 * r * k ^ 2) : Nat) : Real) := by exact_mod_cast hnat
    _ = Real.exp (((3 * r * k ^ 2 : Nat) : Real) * Real.log k) :=
      nat_power_cast_eq_exp_for_linnikVMVT k (3 * r * k ^ 2) hkPos
    _ = Real.exp (3 * (r : Real) * (k : Real) ^ 2 * Real.log k) := by
      congr 1
      push_cast
      ring

theorem three_mul_exp_sub_le_exp
    (K T : Real) (hthree : 3 <= Real.exp K) :
    3 * Real.exp (T - K) <= Real.exp T := by
  calc
    3 * Real.exp (T - K) <= Real.exp (T - K) * Real.exp K :=
      by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hthree (Real.exp_pos (T - K)).le
    _ = Real.exp ((T - K) + K) := (Real.exp_add _ _).symm
    _ = Real.exp T := by
      congr 1
      ring
