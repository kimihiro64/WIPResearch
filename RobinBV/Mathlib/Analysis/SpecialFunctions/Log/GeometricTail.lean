/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Shifted geometric logarithm tails with the complete secondary remainder

The leading geometric sum is separated exactly, not by discarding the
remaining denominators. A real position u between zero and one retains the
periodic information relevant when a cutoff lies between consecutive powers.
-/

set_option autoImplicit false

namespace Complex

noncomputable section

/-- The real ratio in the exact shifted-denominator remainder. -/
def geometricLogRemainderRatio (K : Nat) (u : Real) (n : Nat) : Real :=
  ((n : Real) + 1 - u) / ((K : Real) + (n : Real) + 1)

/-- Complete tail after extracting the first K powers. -/
def shiftedGeometricLogTail (w : Complex) (K : Nat) : Complex :=
  tsum (fun n : Nat => w ^ (n + 1) / (((K : Real) + (n : Real) + 1 : Real) : Complex))

/-- The full, still convergent, remainder carrying the cutoff position. -/
def shiftedGeometricLogRemainder (w : Complex) (K : Nat) (u : Real) : Complex :=
  tsum (fun n : Nat => w ^ (n + 1) * (geometricLogRemainderRatio K u n : Complex))

theorem geometricLogRemainderRatio_bounds
    (K n : Nat) {u : Real} (hu0 : 0 <= u) (hu1 : u <= 1) :
    And (0 <= geometricLogRemainderRatio K u n)
      (geometricLogRemainderRatio K u n <= 1) := by
  have hK : (0 : Real) <= K := Nat.cast_nonneg K
  have hn : (0 : Real) <= n := Nat.cast_nonneg n
  have hDen : 0 < (K : Real) + (n : Real) + 1 := by positivity
  have hNum : 0 <= (n : Real) + 1 - u := by linarith
  have hRatio : 0 <= geometricLogRemainderRatio K u n := div_nonneg hNum hDen.le
  have hEq : geometricLogRemainderRatio K u n * ((K : Real) + (n : Real) + 1) =
      (n : Real) + 1 - u := by
    unfold geometricLogRemainderRatio
    field_simp [hDen.ne']
  exact And.intro hRatio (by nlinarith)

theorem geometricLogRemainderRatio_le_div
    (K n : Nat) {u : Real} (hu0 : 0 <= u) (hu1 : u <= 1)
    (hPos : 0 < (K : Real) + u) :
    geometricLogRemainderRatio K u n <= ((n : Real) + 1) / ((K : Real) + u) := by
  have hn : (0 : Real) <= n := Nat.cast_nonneg n
  have hNum : 0 <= (n : Real) + 1 - u := by linarith
  calc
    _ <= ((n : Real) + 1 - u) / ((K : Real) + u) :=
      div_le_div_of_nonneg_left hNum hPos (by linarith)
    _ <= _ := div_le_div_of_nonneg_right (by linarith) hPos.le

theorem hasSum_geometric_succ
    {w : Complex} (hw : norm w < 1) :
    HasSum (fun n : Nat => w ^ (n + 1)) (w / (1 - w)) := by
  simpa only [pow_succ, div_eq_mul_inv, mul_comm] using
    (hasSum_geometric_of_norm_lt_one hw).mul_left w

theorem summable_shiftedGeometricLogTail
    {w : Complex} (hw : norm w < 1) (K : Nat) :
    Summable (fun n : Nat =>
      w ^ (n + 1) / (((K : Real) + (n : Real) + 1 : Real) : Complex)) := by
  have hr : norm (norm w) < 1 := by simpa only [norm_norm] using hw
  have hMajorant : Summable (fun n : Nat => norm w ^ (n + 1)) := by
    simpa only [pow_succ] using (summable_geometric_of_norm_lt_one hr).mul_right (norm w)
  apply hMajorant.of_norm_bounded
  intro n
  have hDen : 0 < (K : Real) + (n : Real) + 1 := by positivity
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDen]
  have hBound := div_le_div_of_nonneg_left
    (pow_nonneg (norm_nonneg w) (n + 1)) (show (0 : Real) < 1 by norm_num)
    (show 1 <= (K : Real) + (n : Real) + 1 by
      have hK : (0 : Real) <= K := Nat.cast_nonneg K
      have hn : (0 : Real) <= n := Nat.cast_nonneg n
      linarith)
  simpa only [div_one] using hBound

theorem summable_shiftedGeometricLogRemainder
    {w : Complex} (hw : norm w < 1) (K : Nat)
    {u : Real} (hu0 : 0 <= u) (hu1 : u <= 1) :
    Summable (fun n : Nat => w ^ (n + 1) * (geometricLogRemainderRatio K u n : Complex)) := by
  have hr : norm (norm w) < 1 := by simpa only [norm_norm] using hw
  have hMajorant : Summable (fun n : Nat => norm w ^ (n + 1)) := by
    simpa only [pow_succ] using (summable_geometric_of_norm_lt_one hr).mul_right (norm w)
  apply hMajorant.of_norm_bounded
  intro n
  have hRatio := geometricLogRemainderRatio_bounds K n hu0 hu1
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hRatio.1]
  exact (mul_le_mul_of_nonneg_left hRatio.2 (pow_nonneg (norm_nonneg w) _)).trans_eq (mul_one _)

/-- Exact secondary-term identity for the entire infinite tail. -/
theorem shiftedGeometricLogTail_identity
    {w : Complex} (hw : norm w < 1) (K : Nat)
    {u : Real} (hu0 : 0 <= u) (hu1 : u <= 1) :
    (((K : Real) + u : Real) : Complex) * shiftedGeometricLogTail w K =
      w / (1 - w) - shiftedGeometricLogRemainder w K u := by
  have hGeom := hasSum_geometric_succ hw
  have hRem := summable_shiftedGeometricLogRemainder hw K hu0 hu1
  unfold shiftedGeometricLogTail shiftedGeometricLogRemainder
  rw [<- tsum_mul_left, <- hGeom.tsum_eq, <- hGeom.summable.tsum_sub hRem]
  apply tsum_congr
  intro n
  have hDen : Not ((K : Complex) + (n : Complex) + 1 = 0) := by
    have hReal : Not ((K : Real) + (n : Real) + 1 = 0) := by positivity
    exact_mod_cast hReal
  unfold geometricLogRemainderRatio
  push_cast
  field_simp [hDen]
  ring

/-- The complete shifted remainder has an explicit inverse-cutoff bound. -/
theorem norm_shiftedGeometricLogRemainder_le
    {w : Complex} (hw : norm w < 1) (K : Nat)
    {u : Real} (hu0 : 0 <= u) (hu1 : u <= 1)
    (hPos : 0 < (K : Real) + u) :
    norm (shiftedGeometricLogRemainder w K u) <=
      norm w / (((K : Real) + u) * (1 - norm w) ^ 2) := by
  have hr : norm (norm w) < 1 := by simpa only [norm_norm] using hw
  have hWeighted : HasSum (fun n : Nat => (n : Real) * norm w ^ n)
      (norm w / (1 - norm w) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hShift : HasSum (fun n : Nat => ((n + 1 : Nat) : Real) * norm w ^ (n + 1))
      (norm w / (1 - norm w) ^ 2) := by
    apply (hasSum_nat_add_iff (f := fun n : Nat => (n : Real) * norm w ^ n) 1).2
    simpa using hWeighted
  have hBound : norm (shiftedGeometricLogRemainder w K u) <=
      (norm w / (1 - norm w) ^ 2) / ((K : Real) + u) := by
    apply tsum_of_norm_bounded (hShift.div_const ((K : Real) + u))
    intro n
    have hRatio := geometricLogRemainderRatio_bounds K n hu0 hu1
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hRatio.1]
    calc
      _ <= norm w ^ (n + 1) * (((n : Real) + 1) / ((K : Real) + u)) :=
        mul_le_mul_of_nonneg_left (geometricLogRemainderRatio_le_div K n hu0 hu1 hPos)
          (pow_nonneg (norm_nonneg w) _)
      _ = _ := by push_cast; ring
  refine hBound.trans_eq ?_
  rw [div_div, mul_comm ((1 - norm w) ^ 2) ((K : Real) + u)]

/-- For a nonnegative real ratio, the complete secondary remainder has
nonnegative real part. Its sign is proved from the exact summands. -/
theorem shiftedGeometricLogRemainder_re_nonneg
    {r : Real} (hr0 : 0 <= r) (hr1 : r < 1) (K : Nat)
    {u : Real} (hu0 : 0 <= u) (hu1 : u <= 1) :
    0 <= (shiftedGeometricLogRemainder (r : Complex) K u).re := by
  have hr : norm (r : Complex) < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hSummable := summable_shiftedGeometricLogRemainder hr K hu0 hu1
  rw [shiftedGeometricLogRemainder, Complex.re_tsum hSummable]
  apply tsum_nonneg
  intro n
  simp only [<- Complex.ofReal_pow, <- Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (pow_nonneg hr0 _) (geometricLogRemainderRatio_bounds K n hu0 hu1).1

end

end Complex
