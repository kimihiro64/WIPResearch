/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import Mathlib.Tactic.Linarith
import RobinBV.Mathlib.Analysis.Fourier.ExponentialCovariance

/-!
# Two-sided excursions from complete logarithmic moments

A bounded eventually real sequence with zero logarithmic mean and positive
second moment has recurrent excursions of both signs. The complete finite
prefix is handled by the sampled-mean bound, not discarded by assumption.
-/

set_option autoImplicit false

namespace Complex

open Filter

noncomputable section

/-- When the full sampled mean is zero, shifting by any complex constant
adds exactly its squared norm to the complete second-moment limit. -/
theorem tendsto_intervalMean_nat_floor_exp_shifted_square
    (u : Nat -> Complex) (z s : Complex)
    (hMean : Tendsto (intervalMean (fun t : Real => u (Nat.floor (Real.exp t))))
      atTop (nhds (0 : Complex)))
    (hSecond : Tendsto (intervalMean (fun t : Real =>
      u (Nat.floor (Real.exp t))*star (u (Nat.floor (Real.exp t))))) atTop (nhds s)) :
    Tendsto (intervalMean (fun t : Real =>
      (u (Nat.floor (Real.exp t))-z)*star (u (Nat.floor (Real.exp t))-z)))
      atTop (nhds (s+z*star z)) := by
  have h := ((hSecond.sub (hMean.mul_const (star z))).sub
    (hMean.star.const_mul z)).add_const (z*star z)
  simp only [zero_mul, star_zero, mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with T hT
  exact (intervalMean_nat_floor_exp_centered_square_eq u z hT.ne').symm

/-- Quantitative positive excursions follow from the complete zero mean,
second moment, eventual reality and eventual norm bound. -/
theorem frequently_re_gt_of_zero_mean_secondMoment
    (u : Nat -> Complex) {s : Complex} (B d : Real) (hB : 0 <= B) (hd : 0 <= d)
    (hReal : Filter.Eventually (fun n => (u n).im=0) atTop)
    (hBound : Filter.Eventually (fun n => norm (u n) <= B) atTop)
    (hMean : Tendsto (intervalMean (fun t : Real => u (Nat.floor (Real.exp t))))
      atTop (nhds (0 : Complex)))
    (hSecond : Tendsto (intervalMean (fun t : Real =>
      u (Nat.floor (Real.exp t))*star (u (Nat.floor (Real.exp t))))) atTop (nhds s))
    (hSmall : d^2+2*B*d < s.re) :
    Filter.Frequently (fun n => d < (u n).re) atTop := by
  by_contra hNot
  have hUpper : Filter.Eventually (fun n => (u n).re <= d) atTop := by
    simpa only [not_lt] using Filter.not_frequently.mp hNot
  have hShift := tendsto_intervalMean_nat_floor_exp_shifted_square u (-(B : Complex)) s hMean hSecond
  have hSquareBound : Filter.Eventually (fun n =>
      norm ((u n+(B : Complex))*star (u n+(B : Complex))) <= (B+d)^2) atTop := by
    filter_upwards [hReal, hBound, hUpper] with n hnReal hnBound hnUpper
    have hAbs : abs (u n).re <= B := (Complex.abs_re_le_norm _).trans hnBound
    have hLower : 0 <= (u n).re+B := by linarith [(abs_le.mp hAbs).1]
    have hEq : u n=((u n).re : Complex) := by
      apply Complex.ext
      next => rfl
      next => simpa only [Complex.ofReal_im] using hnReal
    have hShiftBound : norm (u n+(B : Complex)) <= B+d := by
      rw [hEq, <- Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLower]
      linarith
    rw [norm_mul, norm_star, pow_two]
    exact mul_le_mul hShiftBound hShiftBound (norm_nonneg _) (add_nonneg hB hd)
  have hLimit : Tendsto (intervalMean (fun t : Real =>
      (u (Nat.floor (Real.exp t))+(B : Complex))*star (u (Nat.floor (Real.exp t))+(B : Complex))))
      atTop (nhds (s+((B^2 : Real) : Complex))) := by
    have hConstant : (-(B : Complex))*star (-(B : Complex)) = ((B^2 : Real) : Complex) := by
      simp only [star_neg, Complex.star_def, Complex.conj_ofReal, neg_mul_neg,
        <- Complex.ofReal_mul, pow_two]
    rw [hConstant] at hShift
    simpa only [sub_neg_eq_add] using hShift
  have hLe := norm_le_of_tendsto_intervalMean_nat_floor_exp_of_eventually_norm_le
    (fun n => (u n+(B : Complex))*star (u n+(B : Complex))) (sq_nonneg (B+d)) hLimit hSquareBound
  have hReLe := (Complex.re_le_norm (s+((B^2 : Real) : Complex))).trans hLe
  simp only [Complex.add_re, Complex.ofReal_re] at hReLe
  nlinarith

/-- The same complete moment data force quantitative negative excursions. -/
theorem frequently_re_lt_neg_of_zero_mean_secondMoment
    (u : Nat -> Complex) {s : Complex} (B d : Real) (hB : 0 <= B) (hd : 0 <= d)
    (hReal : Filter.Eventually (fun n => (u n).im=0) atTop)
    (hBound : Filter.Eventually (fun n => norm (u n) <= B) atTop)
    (hMean : Tendsto (intervalMean (fun t : Real => u (Nat.floor (Real.exp t))))
      atTop (nhds (0 : Complex)))
    (hSecond : Tendsto (intervalMean (fun t : Real =>
      u (Nat.floor (Real.exp t))*star (u (Nat.floor (Real.exp t))))) atTop (nhds s))
    (hSmall : d^2+2*B*d < s.re) :
    Filter.Frequently (fun n => (u n).re < -d) atTop := by
  have hRealNeg : Filter.Eventually (fun n => (-u n).im=0) atTop := by
    simpa only [Complex.neg_im, neg_eq_zero] using hReal
  have hBoundNeg : Filter.Eventually (fun n => norm (-u n) <= B) atTop := by
    simpa only [norm_neg] using hBound
  have hMeanNeg : Tendsto (intervalMean (fun t : Real => -u (Nat.floor (Real.exp t))))
      atTop (nhds (0 : Complex)) := by
    have h := hMean.neg
    rw [neg_zero] at h
    apply h.congr'
    apply Filter.Eventually.of_forall
    intro T
    dsimp only
    unfold intervalMean
    rw [intervalIntegral.integral_neg]
    ring
  have hSecondNeg : Tendsto (intervalMean (fun t : Real =>
      (-u (Nat.floor (Real.exp t)))*star (-u (Nat.floor (Real.exp t))))) atTop (nhds s) := by
    simpa only [star_neg, neg_mul_neg] using hSecond
  have h := frequently_re_gt_of_zero_mean_secondMoment (fun n => -u n)
    B d hB hd hRealNeg hBoundNeg hMeanNeg hSecondNeg hSmall
  apply h.mono
  intro n hn
  simp only [Complex.neg_re] at hn
  linarith

/-- An asymptotically real bounded sequence inherits two signed excursions
from zero mean and positive second moment. Complete quadratic stability
transfers the moment to the real-part sequence before the sign argument. -/
theorem exists_signed_excursions_of_zero_mean_secondMoment
    (u : Nat -> Complex) {s : Complex} (B : Real) (hB : 0 <= B)
    (hIm : Tendsto (fun n => (u n).im) atTop (nhds (0 : Real)))
    (hBound : Filter.Eventually (fun n => norm (u n) <= B) atTop)
    (hMean : Tendsto (intervalMean (fun t : Real => u (Nat.floor (Real.exp t))))
      atTop (nhds (0 : Complex)))
    (hSecond : Tendsto (intervalMean (fun t : Real =>
      u (Nat.floor (Real.exp t))*star (u (Nat.floor (Real.exp t))))) atTop (nhds s))
    (hPos : 0 < s.re) :
    exists d : Real, And (0 < d) (And
      (Filter.Frequently (fun n => d < (u n).re) atTop)
      (Filter.Frequently (fun n => (u n).re < -d) atTop)) := by
  let v : Nat -> Complex := fun n => ((u n).re : Complex)
  have hError : Tendsto (fun n => u n-v n) atTop (nhds (0 : Complex)) := by
    have h := ((Complex.continuous_ofReal.tendsto (0 : Real)).comp hIm).mul_const Complex.I
    simp only [Complex.ofReal_zero, zero_mul] at h
    apply h.congr'
    apply Filter.Eventually.of_forall
    intro n
    dsimp only [v]
    apply Complex.ext <;> simp
  have hVBound : Filter.Eventually (fun n => norm (v n) <= B) atTop := by
    filter_upwards [hBound] with n hn
    dsimp only [v]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans hn
  have hVReal : Filter.Eventually (fun n => (v n).im=0) atTop :=
    Filter.Eventually.of_forall (fun n => rfl)
  have hErrorMean := tendsto_intervalMean_nat_floor_exp (fun n => u n-v n) hError
  have hVMean : Tendsto (intervalMean (fun t : Real => v (Nat.floor (Real.exp t))))
      atTop (nhds (0 : Complex)) := by
    have h := hMean.sub hErrorMean
    simp only [sub_zero] at h
    apply h.congr'
    apply Filter.Eventually.of_forall
    intro T
    dsimp only
    rw [intervalMean_nat_floor_exp_sub u v]
    ring
  have hSquareError := tendsto_mul_star_self_sub_of_tendsto_sub u v hError hVBound
  have hSquareErrorMean := tendsto_intervalMean_nat_floor_exp
    (fun n => u n*star (u n)-v n*star (v n)) hSquareError
  have hVSecond : Tendsto (intervalMean (fun t : Real =>
      v (Nat.floor (Real.exp t))*star (v (Nat.floor (Real.exp t))))) atTop (nhds s) := by
    have h := hSecond.sub hSquareErrorMean
    simp only [sub_zero] at h
    apply h.congr'
    apply Filter.Eventually.of_forall
    intro T
    dsimp only
    rw [intervalMean_nat_floor_exp_sub (fun n => u n*star (u n)) (fun n => v n*star (v n))]
    ring
  let d : Real := min 1 (s.re/(4*(B+1)))
  have hDen : 0 < 4*(B+1) := by positivity
  have hd : 0 < d := lt_min (by norm_num) (div_pos hPos hDen)
  have hSmall : d^2+2*B*d < s.re := by
    have hDOne : d <= 1 := min_le_left _ _
    have hDQuot : d <= s.re/(4*(B+1)) := min_le_right _ _
    have hEq : s.re/(4*(B+1))*(4*(B+1))=s.re := by field_simp
    have hBudget : d*(4*(B+1)) <= s.re :=
      (mul_le_mul_of_nonneg_right hDQuot hDen.le).trans_eq hEq
    nlinarith [mul_nonneg hB hd.le]
  have hPlus := frequently_re_gt_of_zero_mean_secondMoment v B d hB hd.le
    hVReal hVBound hVMean hVSecond hSmall
  have hMinus := frequently_re_lt_neg_of_zero_mean_secondMoment v B d hB hd.le
    hVReal hVBound hVMean hVSecond hSmall
  exact Exists.intro d (And.intro hd (And.intro hPlus hMinus))

end

end Complex
