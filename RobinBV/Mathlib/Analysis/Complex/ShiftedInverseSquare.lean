/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Shifted inverse-square masses on the critical line

The pointwise real-part identity and complete series identities retain the
shifted denominator. They apply to arbitrary summable point families; no
arithmetic zero or hypothesis is built into this reusable algebra.
-/

namespace Complex

noncomputable section

/-- A family of nonzero points with summable inverse-square weights is countable. -/
theorem countable_of_summable_inv_norm_sq {I : Type*} (rho : I -> Complex)
    (hRho : forall i, Not (rho i=0))
    (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2)) : Countable I := by
  have hSupport : Function.support (fun i => (Inv.inv (norm (rho i)))^2) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    simp [Function.mem_support, hRho i]
  have h := hWeight.countable_support
  rw [hSupport] at h
  exact Set.countable_univ_iff.mp h

/-- Moving a real center past one increases distance to the critical line. -/
theorem norm_le_norm_real_sub_of_re_eq_half {z : Complex} {a : Real} (ha : 1 <= a) (hz : z.re = 1 / 2) :
    norm z <= norm ((a : Complex) - z) := by
  have hNorm : norm z ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [<- Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hShift : norm ((a : Complex) - z) ^ 2 = (a-z.re)^2+z.im^2 := by
    rw [<- Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
    ring
  rw [hz] at hNorm hShift
  nlinarith [norm_nonneg z, norm_nonneg ((a : Complex)-z)]

/-- Real part of the two-pole coefficient as two positive inverse-square weights. -/
theorem re_real_div_mul_sub_of_re_eq_half {z : Complex} {a : Real} (ha : 1 <= a) (hz : z.re = 1 / 2) :
    ((a : Complex)/(z*((a : Complex)-z))).re =
      (a-1/2)*(Inv.inv (norm ((a : Complex)-z)))^2 +
        (1/2)*(Inv.inv (norm z))^2 := by
  have hZ : Not (z = 0) := by intro h; rw [h, Complex.zero_re] at hz; norm_num at hz
  have hAZ : Not ((a : Complex)-z = 0) := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re, hz] at hr
    linarith
  have hPartial : (a : Complex)/(z*((a : Complex)-z)) =
      Inv.inv z + Inv.inv ((a : Complex)-z) := by
    field_simp [hZ, hAZ]
    ring
  rw [hPartial, Complex.add_re, Complex.inv_re, Complex.inv_re]
  simp only [Complex.sub_re, Complex.ofReal_re, hz, Complex.normSq_eq_norm_sq]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- The shifted inverse distance is no larger than the distance from zero. -/
theorem inv_norm_real_sub_le_of_re_eq_half {z : Complex} {a : Real} (ha : 1 <= a) (hz : z.re = 1 / 2) :
    Inv.inv (norm ((a : Complex)-z)) <= Inv.inv (norm z) := by
  have hZ : Not (z = 0) := by intro h; rw [h, Complex.zero_re] at hz; norm_num at hz
  simpa only [one_div] using one_div_le_one_div_of_le (norm_pos_iff.mpr hZ)
    (norm_le_norm_real_sub_of_re_eq_half ha hz)

/-- Pointwise comparison of shifted and unshifted inverse-square weights. -/
theorem inv_norm_real_sub_sq_le_of_re_eq_half {z : Complex} {a : Real} (ha : 1 <= a) (hz : z.re = 1 / 2) :
    (Inv.inv (norm ((a : Complex)-z)))^2 <= (Inv.inv (norm z))^2 := by
  have h := inv_norm_real_sub_le_of_re_eq_half ha hz
  nlinarith [inv_nonneg.mpr (norm_nonneg ((a : Complex)-z)), inv_nonneg.mpr (norm_nonneg z)]

/-- A summable inverse-square majorant for the two-pole coefficient. -/
theorem norm_real_div_mul_sub_le_of_re_eq_half {z : Complex} {a : Real} (ha : 1 <= a) (hz : z.re = 1 / 2) :
    norm ((a : Complex)/(z*((a : Complex)-z))) <=
      a*(Inv.inv (norm z))^2 := by
  have ha0 : 0 <= a := by linarith
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
  calc
    _ = a * Inv.inv (norm z) * Inv.inv (norm ((a : Complex)-z)) := by ring
    _ <= a * Inv.inv (norm z) * Inv.inv (norm z) :=
      mul_le_mul_of_nonneg_left (inv_norm_real_sub_le_of_re_eq_half ha hz) (by positivity)
    _ = _ := by ring

/-- Summable unshifted mass dominates the full shifted mass. -/
theorem summable_inv_norm_real_sub_sq_of_re_eq_half
    {I : Type*} (z : I -> Complex) (hz : forall i, (z i).re = 1 / 2)
    (hZ : Summable (fun i => (Inv.inv (norm (z i)))^2))
    {a : Real} (ha : 1 <= a) :
    Summable (fun i => (Inv.inv (norm ((a : Complex)-z i)))^2) := by
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun i => inv_norm_real_sub_sq_le_of_re_eq_half ha (hz i)) hZ

/-- Complete shifted mass is bounded by complete unshifted mass. -/
theorem tsum_inv_norm_real_sub_sq_le_of_re_eq_half
    {I : Type*} (z : I -> Complex) (hz : forall i, (z i).re = 1 / 2)
    (hZ : Summable (fun i => (Inv.inv (norm (z i)))^2))
    {a : Real} (ha : 1 <= a) :
    tsum (fun i => (Inv.inv (norm ((a : Complex)-z i)))^2) <=
      tsum (fun i => (Inv.inv (norm (z i)))^2) := by
  exact (summable_inv_norm_real_sub_sq_of_re_eq_half z hz hZ ha).tsum_le_tsum
    (fun i => inv_norm_real_sub_sq_le_of_re_eq_half ha (hz i)) hZ

/-- The full two-pole coefficient series is absolutely convergent. -/
theorem summable_real_div_mul_sub_of_re_eq_half
    {I : Type*} (z : I -> Complex) (hz : forall i, (z i).re = 1 / 2)
    (hZ : Summable (fun i => (Inv.inv (norm (z i)))^2))
    {a : Real} (ha : 1 <= a) :
    Summable (fun i => (a : Complex)/(z i*((a : Complex)-z i))) := by
  apply (hZ.mul_left a).of_norm_bounded
  intro i
  exact norm_real_div_mul_sub_le_of_re_eq_half ha (hz i)

/-- Exact real part of the full two-pole sum in terms of both complete masses. -/
theorem re_tsum_real_div_mul_sub_of_re_eq_half
    {I : Type*} (z : I -> Complex) (hz : forall i, (z i).re = 1 / 2)
    (hZ : Summable (fun i => (Inv.inv (norm (z i)))^2))
    {a : Real} (ha : 1 <= a) :
    (tsum (fun i => (a : Complex)/(z i*((a : Complex)-z i)))).re =
      (a-1/2)*tsum (fun i => (Inv.inv (norm ((a : Complex)-z i)))^2) +
        (1/2)*tsum (fun i => (Inv.inv (norm (z i)))^2) := by
  have hM := summable_inv_norm_real_sub_sq_of_re_eq_half z hz hZ ha
  rw [Complex.re_tsum (summable_real_div_mul_sub_of_re_eq_half z hz hZ ha)]
  simp_rw [re_real_div_mul_sub_of_re_eq_half ha (hz _)]
  rw [(hM.mul_left (a-1/2)).tsum_add (hZ.mul_left (1/2)), tsum_mul_left, tsum_mul_left]

/-- Cauchy-Schwarz improves the complete absolute two-pole mass using both
unshifted and shifted inverse-square masses, with no finite truncation. -/
theorem tsum_norm_real_div_mul_sub_le_sqrt_of_re_eq_half
    {I : Type*} (z : I -> Complex) (hz : forall i, (z i).re = 1 / 2)
    (hZ : Summable (fun i => (Inv.inv (norm (z i)))^2))
    {a : Real} (ha : 1 <= a) :
    tsum (fun i => norm ((a : Complex)/(z i*((a : Complex)-z i)))) <=
      a * Real.sqrt (tsum (fun i => (Inv.inv (norm (z i)))^2) *
        tsum (fun i => (Inv.inv (norm ((a : Complex)-z i)))^2)) := by
  have ha0 : 0 <= a := by linarith
  have hM := summable_inv_norm_real_sub_sq_of_re_eq_half z hz hZ ha
  have hC : Summable (fun i => norm ((a : Complex)/(z i*((a : Complex)-z i)))) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => norm_real_div_mul_sub_le_of_re_eq_half ha (hz i)) (hZ.mul_left a)
  apply hC.tsum_le_of_sum_le
  intro s
  have hFinite := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun i => Inv.inv (norm (z i))) (fun i => Inv.inv (norm ((a : Complex)-z i)))
  have hZle := hZ.sum_le_tsum s (fun _ _ => sq_nonneg _)
  have hMle := hM.sum_le_tsum s (fun _ _ => sq_nonneg _)
  calc
    _ = a * s.sum (fun i => Inv.inv (norm (z i))*Inv.inv (norm ((a : Complex)-z i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
      ring
    _ <= a * (Real.sqrt (s.sum (fun i => (Inv.inv (norm (z i)))^2)) *
        Real.sqrt (s.sum (fun i => (Inv.inv (norm ((a : Complex)-z i)))^2))) :=
      mul_le_mul_of_nonneg_left hFinite ha0
    _ <= a * (Real.sqrt (tsum (fun i => (Inv.inv (norm (z i)))^2)) *
        Real.sqrt (tsum (fun i => (Inv.inv (norm ((a : Complex)-z i)))^2))) := by
      apply mul_le_mul_of_nonneg_left _ ha0
      exact mul_le_mul (Real.sqrt_le_sqrt hZle) (Real.sqrt_le_sqrt hMle)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (tsum_nonneg (fun _ => sq_nonneg _))]

/-- Exact squared two-pole coefficient as a difference of inverse-square
masses. The strict center hypothesis avoids the removable a=1 quotient. -/
theorem norm_real_div_mul_sub_sq_eq_of_re_eq_half
    {z : Complex} {a : Real} (ha : 1 < a) (hz : z.re=1/2) :
    norm ((a : Complex)/(z*((a : Complex)-z)))^2 =
      a/(a-1)*((Inv.inv (norm z))^2-(Inv.inv (norm ((a : Complex)-z)))^2) := by
  have hZ : Not (z=0) := by
    intro h
    rw [h, Complex.zero_re] at hz
    norm_num at hz
  have hAZ : Not ((a : Complex)-z=0) := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re, hz] at hr
    linarith
  have hNormZ : Not (norm z=0) := norm_ne_zero_iff.mpr hZ
  have hNormAZ : Not (norm ((a : Complex)-z)=0) := norm_ne_zero_iff.mpr hAZ
  have hA : Not (a-1=0) := by linarith
  have hShift : norm ((a : Complex)-z)^2 = norm z^2+a*(a-1) := by
    rw [<- Complex.normSq_eq_norm_sq, <- Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, hz]
    ring
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < a)]
  simp only [div_pow, mul_pow, inv_pow]
  field_simp [hNormZ, hNormAZ, hA]
  rw [hShift]
  ring

/-- The complete diagonal coefficient mass is exactly the difference
between the unshifted and shifted inverse-square masses. -/
theorem tsum_norm_real_div_mul_sub_sq_eq_of_re_eq_half
    {I : Type*} (rho : I -> Complex) (hRe : forall i, (rho i).re=1/2)
    (hZ : Summable (fun i => (Inv.inv (norm (rho i)))^2))
    {a : Real} (ha : 1 < a) :
    tsum (fun i => norm ((a : Complex)/(rho i*((a : Complex)-rho i)))^2) =
      a/(a-1)*(tsum (fun i => (Inv.inv (norm (rho i)))^2) -
        tsum (fun i => (Inv.inv (norm ((a : Complex)-rho i)))^2)) := by
  have hShift := summable_inv_norm_real_sub_sq_of_re_eq_half rho hRe hZ ha.le
  simp only [norm_real_div_mul_sub_sq_eq_of_re_eq_half ha (hRe _)]
  rw [tsum_mul_left, hZ.tsum_sub hShift]

end

end Complex
