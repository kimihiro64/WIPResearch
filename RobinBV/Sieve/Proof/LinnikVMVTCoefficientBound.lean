/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMVTCoefficientComponents

/-!
# Exponential bound for the sharp Linnik VMVT coefficient

This module inducts over the explicit sharp recurrence using the separately
compiled component estimates. The resulting coefficient has exponent linear in
the induction level, with no quadratic loss in `r`.
-/

theorem linnikVMVTSharpCoefficient_le_exp
    (Y0 k s : Nat) (hk : 2 <= k) :
    linnikVMVTSharpCoefficient Y0 k s <=
      Real.exp (((max 13 Y0 : Real) + 8) * ((s + 1 : Nat) : Real) *
        (k : Real) ^ 2 * Real.log k) := by
  have hkPos : 0 < k := by omega
  have hkOne : 1 <= k := by omega
  have hlogk : 0 <= Real.log (k : Real) :=
    (Real.log_pos (by exact_mod_cast hk)).le
  have hK : 0 <= (k : Real) ^ 2 * Real.log k := mul_nonneg (by positivity) hlogk
  have hA : (1 : Real) <= (max 13 Y0 : Real) + 8 := by
    have h13 : (13 : Real) <= (max 13 Y0 : Real) := by exact_mod_cast le_max_left 13 Y0
    linarith
  have hfour : 4 <= k ^ 2 := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ <= k ^ 2 := Nat.pow_le_pow_left hk 2
  have hk2 : 2 <= k ^ 2 := by omega
  have hthreeNat : 3 <= k ^ (k ^ 2) := by
    calc
      3 <= 4 := by norm_num
      _ <= k ^ 2 := hfour
      _ <= k ^ (k ^ 2) := Nat.pow_le_pow_right hkPos hk2
  have hthree : (3 : Real) <= Real.exp ((k : Real) ^ 2 * Real.log k) := by
    calc
      (3 : Real) <= ((k ^ (k ^ 2) : Nat) : Real) := by exact_mod_cast hthreeNat
      _ = Real.exp (((k ^ 2 : Nat) : Real) * Real.log k) :=
        nat_power_cast_eq_exp_for_linnikVMVT k (k ^ 2) hkPos
      _ = Real.exp ((k : Real) ^ 2 * Real.log k) := by norm_cast
  induction s with
  | zero =>
      have hkk : k <= k ^ 2 := by
        calc
          k = k * 1 := by ring
          _ <= k * k := Nat.mul_le_mul_left k hkOne
          _ = k ^ 2 := by ring
      have hfactNat : k.factorial <= k ^ (k ^ 2) :=
        (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_right hkPos hkk)
      have hfact : (k.factorial : Real) <= Real.exp
          ((k : Real) ^ 2 * Real.log k) := by
        calc
          (k.factorial : Real) <= ((k ^ (k ^ 2) : Nat) : Real) := by
            exact_mod_cast hfactNat
          _ = Real.exp (((k ^ 2 : Nat) : Real) * Real.log k) :=
            nat_power_cast_eq_exp_for_linnikVMVT k (k ^ 2) hkPos
          _ = Real.exp ((k : Real) ^ 2 * Real.log k) := by norm_cast
      rw [linnikVMVTSharpCoefficient_zero]
      apply hfact.trans
      apply Real.exp_le_exp.mpr
      have hscale := mul_le_mul_of_nonneg_right hA hK
      norm_num
      nlinarith
  | succ s ih =>
      let K : Real := (k : Real) ^ 2 * Real.log k
      let A : Real := (max 13 Y0 : Real) + 8
      let T : Real := A * ((s + 2 : Nat) : Real) * K
      have hK0 : 0 <= K := by simpa only [K] using hK
      have hA13 : (13 : Real) <= A := by
        simp only [A]
        have h13 : (13 : Real) <= (max 13 Y0 : Real) := by
          exact_mod_cast le_max_left 13 Y0
        linarith
      have hA7 : (7 : Real) <= A := le_trans (by norm_num) hA13
      have hM := linnikVMVTStepMultiplier_le_exp_six k hk
      have hM' : linnikVMVTStepMultiplier k <= Real.exp (6 * K) := by
        convert hM using 1 <;> simp only [K] <;> ring
      have ih' : linnikVMVTSharpCoefficient Y0 k s <=
          Real.exp (A * ((s + 1 : Nat) : Real) * K) := by
        convert ih using 1 <;> simp only [A, K] <;> ring
      have hMul : linnikVMVTStepMultiplier k *
          linnikVMVTSharpCoefficient Y0 k s <= Real.exp (T - K) := by
        calc
          linnikVMVTStepMultiplier k * linnikVMVTSharpCoefficient Y0 k s <=
              Real.exp (6 * K) * Real.exp
                (A * ((s + 1 : Nat) : Real) * K) := by
            exact mul_le_mul hM' ih'
              (linnikVMVTSharpCoefficient_nonneg Y0 k s) (by positivity)
          _ = Real.exp ((6 + A * ((s + 1 : Nat) : Real)) * K) := by
            rw [<- Real.exp_add]
            congr 1
            ring
          _ <= Real.exp (T - K) := by
            apply Real.exp_le_exp.mpr
            simp only [T]
            push_cast
            have hs : (0 : Real) <= (s : Real) := by positivity
            nlinarith [mul_le_mul_of_nonneg_right hA7 hK0]
      let R : Real := ((s + 2 : Nat) : Real)
      have hR : (1 : Real) <= R := by
        simp only [R]
        exact_mod_cast (by omega)
      have hCollision0 := linnikVMVTCollision_le_exp_three k (s + 2) hk
      have hCollision0' :
          ((4 ^ (k * (s + 2)) * k ^ (4 * (k * (s + 2))) : Nat) : Real) <=
            Real.exp (3 * R * K) := by
        convert hCollision0 using 1 <;> simp only [R, K] <;> ring
      have hCollision :
          ((4 ^ (k * (s + 2)) * k ^ (4 * (k * (s + 2))) : Nat) : Real) <=
            Real.exp (T - K) := by
        apply hCollision0'.trans
        apply Real.exp_le_exp.mpr
        change 3 * R * K <= A * R * K - K
        have hgap : (1 : Real) <= (A - 3) * R := by nlinarith
        have hgapK : K <= ((A - 3) * R) * K := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hgap hK0
        calc
          3 * R * K = A * R * K - ((A - 3) * R) * K := by ring
          _ <= A * R * K - K := sub_le_sub_left hgapK _
      have hSource : linnikVMVTSourceCost Y0 k (s + 2) <=
          Real.exp (T - K) := by
        rw [linnikVMVTSourceCost]
        apply Real.exp_le_exp.mpr
        have hgap : (1 : Real) <= 8 * R := by nlinarith
        have hgapK : K <= (8 * R) * K := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hgap hK0
        calc
          (max 13 Y0 : Real) * ((s + 2 : Nat) : Real) *
                (k : Real) ^ 2 * Real.log k =
              (max 13 Y0 : Real) * R * K := by
            simp only [R, K]
            ring
          _ = A * R * K - (8 * R) * K := by
            simp only [A]
            ring
          _ <= A * R * K - K := sub_le_sub_left hgapK _
          _ = T - K := by simp only [T, R]
      rw [linnikVMVTSharpCoefficient_succ]
      calc
        linnikVMVTStepMultiplier k * linnikVMVTSharpCoefficient Y0 k s +
              ((4 ^ (k * (s + 2)) * k ^ (4 * (k * (s + 2))) : Nat) : Real) +
                linnikVMVTSourceCost Y0 k (s + 2) <=
            Real.exp (T - K) + Real.exp (T - K) + Real.exp (T - K) :=
          _root_.add_le_add (_root_.add_le_add hMul hCollision) hSource
        _ = 3 * Real.exp (T - K) := by ring
        _ <= Real.exp T := three_mul_exp_sub_le_exp K T (by simpa only [K] using hthree)
        _ = Real.exp (((max 13 Y0 : Real) + 8) *
            (((s + 1) + 1 : Nat) : Real) * (k : Real) ^ 2 * Real.log k) := by
          simp only [T, A, K]
          congr 1
          push_cast
          ring
