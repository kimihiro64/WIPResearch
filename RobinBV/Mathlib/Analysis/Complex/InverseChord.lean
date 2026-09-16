/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.ReciprocalShift

/-!
# Inverse unit-circle chords

Exact inversion, monotonicity and explicit spacing bounds on the upper semicircle.
These finite estimates do not assume a prime-distribution theorem.
-/

set_option autoImplicit false

namespace Complex

noncomputable def inverseChordWeight (x : Real) : Complex :=
  { re := -(1/2), im := -(Real.cos (x/2)/(2*Real.sin (x/2))) }

private theorem ratio_le_of_cross {a b c d : Real} (hb : 0 < b) (hd : 0 < d)
    (h : a*d <= c*b) : a/b <= c/d := by
  have hm := mul_le_mul_of_nonneg_right h (show 0 <= 1/(b*d) by positivity)
  have hl : (a*d)*(1/(b*d)) = a/b := by field_simp [ne_of_gt hb, ne_of_gt hd]
  have hr : (c*b)*(1/(b*d)) = c/d := by field_simp [ne_of_gt hb, ne_of_gt hd]
  rwa [hl, hr] at hm

theorem inverseChordWeight_mul_exp_sub_one (x : Real) (hx : 0 < x) (hxp : x <= Real.pi) :
    inverseChordWeight x*(exp (I*(x : Complex))-1) = 1 := by
  have hp := Real.pi_pos
  have hspos := Real.sin_pos_of_pos_of_lt_pi (show 0 < x/2 by linarith)
    (show x/2 < Real.pi by linarith)
  have htwo : 2*(x/2) = x := by ring
  have hs : Real.sin x = 2*Real.sin (x/2)*Real.cos (x/2) := by
    simpa only [htwo] using Real.sin_two_mul (x/2)
  have hc : Real.cos x = 2*Real.cos (x/2)^2-1 := by
    simpa only [htwo] using Real.cos_two_mul (x/2)
  have hsq := Real.cos_sq_add_sin_sq (x/2)
  have hsqmul := congrArg (fun t : Real => Real.cos (x/2)*t) hsq
  have he : exp (I*(x : Complex)) = (Real.cos x : Complex)+(Real.sin x : Complex)*I := by
    rw [mul_comm I, exp_ofReal_mul_I]
  rw [he]
  apply Complex.ext
  all_goals simp only [inverseChordWeight, mul_re, mul_im, sub_re, sub_im,
    add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, one_re, one_im,
    mul_zero, add_zero, zero_add, sub_zero, mul_one]
  all_goals rw [hs, hc]
  all_goals field_simp [ne_of_gt hspos]
  all_goals nlinarith [hsqmul]

/-- Imaginary inverse-chord coordinates are increasing on the upper semicircle. -/
theorem inverseChordWeight_im_mono {x y : Real} (hx : 0 < x)
    (hxy : x <= y) (hy : y <= Real.pi) :
    (inverseChordWeight x).im <= (inverseChordWeight y).im := by
  have hp := Real.pi_pos
  have hsx := Real.sin_pos_of_pos_of_lt_pi (show 0 < x/2 by linarith)
    (show x/2 < Real.pi by linarith)
  have hsy := Real.sin_pos_of_pos_of_lt_pi (show 0 < y/2 by linarith)
    (show y/2 < Real.pi by linarith)
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 <= y/2-x/2 by linarith)
    (show y/2-x/2 <= Real.pi by linarith)
  rw [Real.sin_sub] at hs
  have hcross : Real.cos (y/2)*(2*Real.sin (x/2)) <=
      Real.cos (x/2)*(2*Real.sin (y/2)) := by nlinarith
  have hr := ratio_le_of_cross (show 0 < 2*Real.sin (y/2) by positivity)
    (show 0 < 2*Real.sin (x/2) by positivity) hcross
  exact neg_le_neg hr

/-- An explicit inverse spacing cost, with both endpoints of its domain retained. -/
theorem norm_inverseChordWeight_le (x : Real) (hx : 0 < x) (hxp : x <= Real.pi) :
    norm (inverseChordWeight x) <= Real.pi/(2*x) := by
  have hspos := Real.sin_pos_of_pos_of_lt_pi (show 0 < x/2 by linarith)
    (show x/2 < Real.pi by linarith [Real.pi_pos])
  have hn := congrArg norm (inverseChordWeight_mul_exp_sub_one x hx hxp)
  simp only [norm_mul, norm_one] at hn
  rw [norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_of_nonneg (show 0 <= 2*Real.sin (x/2) by positivity)] at hn
  have hl : x/Real.pi <= Real.sin (x/2) := by
    convert Real.mul_le_sin (show 0 <= x/2 by linarith)
      (show x/2 <= Real.pi/2 by linarith) using 1
    ring
  have hm := mul_le_mul_of_nonneg_left hl (show 0 <= 2*norm (inverseChordWeight x) by positivity)
  have hh : (2*norm (inverseChordWeight x))*(x/Real.pi) <= 1 := by nlinarith only [hn, hm]
  have hscale := mul_le_mul_of_nonneg_right hh Real.pi_pos.le
  have hc : ((2*norm (inverseChordWeight x))*(x/Real.pi))*Real.pi =
      (2*norm (inverseChordWeight x))*x := by field_simp [ne_of_gt Real.pi_pos]
  rw [hc, one_mul] at hscale
  have hq : (Real.pi/(2*x))*(2*x) = Real.pi := by field_simp [ne_of_gt hx]
  by_contra hgoal
  have hbad := mul_lt_mul_of_pos_right (lt_of_not_ge hgoal) (show 0 < 2*x by positivity)
  rw [hq] at hbad
  nlinarith only [hscale, hbad]

end Complex
