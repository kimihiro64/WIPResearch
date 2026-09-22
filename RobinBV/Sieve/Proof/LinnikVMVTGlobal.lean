/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMVTAsymptotic

/-!
# Global Linnik VMVT coefficient induction

This module iterates the explicit prime-band recurrence. It combines the
diagonal base case, the large recurrence branch, and the trivial small-input
branch into one unconditional coefficient for every positive input.
-/

noncomputable def linnikVMVTCoefficient (Y0 k s : Nat) : Real :=
  Nat.rec (k.factorial : Real)
    (fun i A =>
      linnikVMVTStepMultiplier k * A +
        ((4 ^ (k * (i + 2)) * k ^ (4 * (k * (i + 2))) : Nat) : Real) +
          (linnikVMVTStepThreshold Y0 k (i + 1) : Real) ^
            (2 * k * (i + 2) : Nat)) s

@[simp] theorem linnikVMVTCoefficient_zero (Y0 k : Nat) :
    linnikVMVTCoefficient Y0 k 0 = (k.factorial : Real) := by
  rfl

@[simp] theorem linnikVMVTCoefficient_succ (Y0 k s : Nat) :
    linnikVMVTCoefficient Y0 k (s + 1) =
      linnikVMVTStepMultiplier k * linnikVMVTCoefficient Y0 k s +
        ((4 ^ (k * (s + 2)) * k ^ (4 * (k * (s + 2))) : Nat) : Real) +
          (linnikVMVTStepThreshold Y0 k (s + 1) : Real) ^
            (2 * k * (s + 2) : Nat) := by
  rfl

theorem linnikVMVTCoefficient_nonneg (Y0 k s : Nat) :
    0 <= linnikVMVTCoefficient Y0 k s := by
  induction s with
  | zero =>
      rw [linnikVMVTCoefficient_zero]
      exact_mod_cast Nat.zero_le k.factorial
  | succ s ih =>
      rw [linnikVMVTCoefficient_succ]
      have hm : 0 <= linnikVMVTStepMultiplier k := by
        simp only [linnikVMVTStepMultiplier]
        positivity
      exact add_nonneg (add_nonneg (mul_nonneg hm ih) (by positivity)) (by positivity)

/-- The exact recurrence and small branch give a global explicit coefficient. -/
theorem exists_linnikVMVT_global_coefficient :
    exists Y0 : Nat, forall r k X : Nat,
      0 < r -> 2 <= k -> 0 < X ->
      (Finset.vinogradovMeanValue k (k * r) X : Real) <=
        linnikVMVTCoefficient Y0 k (r - 1) *
          (X : Real) ^ linnikVMVTExponent k r := by
  choose Y0 hstep using exists_linnikVMVT_explicit_coefficient_step
  refine Exists.intro Y0 ?_
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro k X hr hk hX
      cases r with
      | zero => omega
      | succ s =>
          cases s with
          | zero =>
              have hnat := Finset.vinogradovMeanValue_le_diagonal_factorial k X
              have hreal :
                  (Finset.vinogradovMeanValue k k X : Real) <=
                    (X : Real) ^ k * (k.factorial : Real) := by
                exact_mod_cast hnat
              calc
                (Finset.vinogradovMeanValue k (k * 1) X : Real) <=
                    (X : Real) ^ k * (k.factorial : Real) := by
                  simpa only [Nat.mul_one] using hreal
                _ = linnikVMVTCoefficient Y0 k (1 - 1) *
                    (X : Real) ^ linnikVMVTExponent k 1 := by
                  rw [linnikVMVTExponent_one k (lt_of_lt_of_le (by norm_num) hk)]
                  rw [Real.rpow_natCast]
                  simp only [Nat.reduceSub, linnikVMVTCoefficient_zero]
                  ring
          | succ s =>
              have hkPos : 0 < k := lt_of_lt_of_le (by norm_num) hk
              have hsPos : 0 < s + 1 := by omega
              have hrPos : 0 < s + 2 := by omega
              have hindex : s + 1 + 1 = s + 2 := by omega
              rw [hindex]
              have hJ : forall p : Nat, 0 < p ->
                  p <= 2 * Nat.nthRoot k X ->
                  (Finset.vinogradovMeanValue k (k * (s + 1)) (1 + X / p) : Real) <=
                    linnikVMVTCoefficient Y0 k s *
                      (1 + (X : Real) / p) ^ linnikVMVTExponent k (s + 1) := by
                intro p hpPos hp
                have hXp : 0 < 1 + X / p := by
                  simpa only [Nat.one_add] using Nat.succ_pos (X / p)
                have hprev := ih (s + 1) (by omega) k (1 + X / p)
                  hsPos hk hXp
                have hprev' :
                    (Finset.vinogradovMeanValue k (k * (s + 1))
                      (1 + X / p) : Real) <=
                      linnikVMVTCoefficient Y0 k s *
                        ((1 + X / p : Nat) : Real) ^
                          linnikVMVTExponent k (s + 1) := by
                  simpa only [Nat.add_sub_cancel] using hprev
                have hbase : ((1 + X / p : Nat) : Real) <=
                    1 + (X : Real) / p := by
                  have hdiv : ((X / p : Nat) : Real) <=
                      (X : Real) / (p : Real) := Nat.cast_div_le
                  calc
                    ((1 + X / p : Nat) : Real) =
                        1 + ((X / p : Nat) : Real) := by
                      rw [Nat.cast_add, Nat.cast_one]
                    _ <= 1 + (X : Real) / p :=
                      _root_.add_le_add le_rfl hdiv
                have hpow :
                    ((1 + X / p : Nat) : Real) ^
                        linnikVMVTExponent k (s + 1) <=
                      (1 + (X : Real) / p) ^
                        linnikVMVTExponent k (s + 1) :=
                  Real.rpow_le_rpow (by positivity) hbase
                    (linnikVMVTExponent_nonneg k (s + 1) hkPos hsPos)
                exact hprev'.trans (mul_le_mul_of_nonneg_left hpow
                  (linnikVMVTCoefficient_nonneg Y0 k s))
              by_cases hlarge : linnikVMVTStepThreshold Y0 k (s + 1) <= X
              next =>
                have hlargeStep := hstep k (s + 1) X
                  (linnikVMVTCoefficient Y0 k s) hk hsPos
                  (linnikVMVTCoefficient_nonneg Y0 k s)
                  (linnikVMVTStepThreshold_band Y0 k (s + 1) X hlarge)
                  (linnikVMVTStepThreshold_scale Y0 k (s + 1) X hlarge) hJ
                calc
                  (Finset.vinogradovMeanValue k (k * (s + 2)) X : Real) <=
                      (4 * ((k ^ 3 + 1 : Nat) : Real) ^ 2 *
                          (k.factorial : Real) *
                          linnikVMVTCoefficient Y0 k s * Real.exp 1 *
                            (2 : Real) ^ ((k : Real) ^ 2) +
                        ((4 ^ (k * (s + 2)) *
                          k ^ (4 * (k * (s + 2))) : Nat) : Real)) *
                        (X : Real) ^ linnikVMVTExponent k (s + 2) := by
                    simpa only [Nat.add_assoc] using hlargeStep
                  _ <= linnikVMVTCoefficient Y0 k (s + 1) *
                      (X : Real) ^ linnikVMVTExponent k (s + 2) := by
                    apply mul_le_mul_of_nonneg_right
                    next =>
                      rw [linnikVMVTCoefficient_succ]
                      simp only [linnikVMVTStepMultiplier]
                      have hT : 0 <=
                          (linnikVMVTStepThreshold Y0 k (s + 1) : Real) ^
                            (2 * k * (s + 2) : Nat) := by positivity
                      nlinarith
                    next =>
                      positivity
              next =>
                have hsmall : X < linnikVMVTStepThreshold Y0 k (s + 1) :=
                  Nat.lt_of_not_ge hlarge
                have hsmallBound := linnikVMVT_small_argument_le
                  Y0 k (s + 1) (s + 2) X hkPos hrPos hX hsmall
                calc
                  (Finset.vinogradovMeanValue k (k * (s + 2)) X : Real) <=
                      (linnikVMVTStepThreshold Y0 k (s + 1) : Real) ^
                          (2 * k * (s + 2) : Nat) *
                        (X : Real) ^ linnikVMVTExponent k (s + 2) :=
                    hsmallBound
                  _ <= linnikVMVTCoefficient Y0 k (s + 1) *
                      (X : Real) ^ linnikVMVTExponent k (s + 2) := by
                    apply mul_le_mul_of_nonneg_right
                    next =>
                      rw [linnikVMVTCoefficient_succ]
                      have hA := linnikVMVTCoefficient_nonneg Y0 k s
                      have hM : 0 <= linnikVMVTStepMultiplier k := by
                        simp only [linnikVMVTStepMultiplier]
                        positivity
                      have hMA : 0 <= linnikVMVTStepMultiplier k *
                          linnikVMVTCoefficient Y0 k s := mul_nonneg hM hA
                      have hcollision : 0 <=
                          ((4 ^ (k * (s + 2)) *
                            k ^ (4 * (k * (s + 2))) : Nat) : Real) := by
                        positivity
                      nlinarith
                    next =>
                      positivity
