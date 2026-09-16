/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite Mellin fourth moments with complex exponents

The exact complex-power integral retains its zero-frequency case through
max(1,abs(s.im)). Finite fourth moments keep every coefficient and the full
quadruple domain, allowing the real parts of the exponents to vary.
No arithmetic zero-density or additive-energy estimate is assumed here.
-/

set_option autoImplicit false

open ComplexConjugate

namespace Complex

theorem norm_integral_cpow_le_frequency {a b : Real} (ha : 0 < a) (hab : a <= b)
    {s : Complex} (hs : 0 <= s.re) :
    norm (intervalIntegral (fun x : Real => (x : Complex)^s)
      a b MeasureTheory.volume) <=
      2*b^(s.re+1)/max 1 (abs s.im) := by
  have hb : 0 < b := ha.trans_le hab
  have hden : max 1 (abs s.im) <= norm (s+1) := by
    apply max_le
    next =>
      have h := re_le_norm (s+1)
      simp only [add_re, one_re] at h
      linarith
    next =>
      simpa only [add_im, one_im, add_zero] using abs_im_le_norm (s+1)
  have hden0 : 0 < max 1 (abs s.im) :=
    lt_of_lt_of_le (by norm_num : (0 : Real) < 1) (le_max_left _ _)
  have htop : norm ((b : Complex)^(s+1)-(a : Complex)^(s+1)) <=
      2*b^(s.re+1) := by
    calc
      _ <= norm ((b : Complex)^(s+1))+norm ((a : Complex)^(s+1)) := norm_sub_le _ _
      _ = b^(s.re+1)+a^(s.re+1) := by
        rw [norm_cpow_eq_rpow_re_of_pos hb, norm_cpow_eq_rpow_re_of_pos ha,
          add_re, one_re]
      _ <= _ := by
        have hpow := Real.rpow_le_rpow ha.le hab (by linarith : 0 <= s.re+1)
        linarith
  rw [_root_.integral_cpow (Or.inl (by linarith : -1 < s.re)), norm_div]
  calc
    _ <= (2*b^(s.re+1))/norm (s+1) :=
      div_le_div_of_nonneg_right htop (norm_nonneg _)
    _ <= _ :=
      div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hb.le _)) hden0 hden

theorem norm_integral_exp_log_le_frequency {a b : Real} (ha : 0 < a) (hab : a <= b)
    {s : Complex} (hs : 0 <= s.re) :
    norm (intervalIntegral (fun x : Real => exp (s*(Real.log x : Complex)))
      a b MeasureTheory.volume) <=
      2*b^(s.re+1)/max 1 (abs s.im) := by
  have heq : intervalIntegral (fun x : Real => exp (s*(Real.log x : Complex)))
      a b MeasureTheory.volume =
      intervalIntegral (fun x : Real => (x : Complex)^s) a b MeasureTheory.volume := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := ha.trans_le hx.1
    change exp (s*(Real.log x : Complex)) = (x : Complex)^s
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx0.ne'), <- ofReal_log hx0.le]
    congr 1
    ring
  rw [heq]
  exact norm_integral_cpow_le_frequency ha hab hs

theorem norm_integral_exp_log_dyadic_le {X sigma : Real} (hX : 1 <= X)
    (hsigma : sigma <= 1) {s : Complex} (hs0 : 0 <= s.re) (hs : s.re <= 4*sigma) :
    norm (intervalIntegral (fun y : Real => exp (s*(Real.log y : Complex)))
      (X/2) (8*X) MeasureTheory.volume) <=
      65536*X^(1+4*sigma)/max 1 (abs s.im) := by
  have hX0 : 0 < X := by linarith
  have hbase := norm_integral_exp_log_le_frequency
    (by linarith : 0 < X/2) (by linarith : X/2 <= 8*X) hs0
  have h8 : (8 : Real)^(s.re+1) <= 32768 := by
    calc
      _ <= (8 : Real)^((5 : Nat) : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num; linarith)
      _ = 32768 := by rw [Real.rpow_natCast]; norm_num
  have hpowX : X^(s.re+1) <= X^(1+4*sigma) :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hmain : 2*(8*X)^(s.re+1) <= 65536*X^(1+4*sigma) := by
    rw [Real.mul_rpow (by norm_num : (0 : Real) <= 8) hX0.le]
    have hmul := mul_le_mul h8 hpowX (Real.rpow_nonneg hX0.le (s.re+1))
      (by norm_num : (0 : Real) <= 32768)
    linarith
  exact hbase.trans (div_le_div_of_nonneg_right hmain
    ((by norm_num : (0 : Real) <= 1).trans (le_max_left _ _)))

theorem finite_mellin_norm_sq_expansion {I : Type*} (A : Finset I)
    (coefficient rho : I -> Complex) (t : Real) :
    ((norm (Finset.sum A (fun i => coefficient i*exp (rho i*(t : Complex))))^2 : Real) :
        Complex) =
      Finset.sum A (fun i => Finset.sum A (fun j =>
        (coefficient i*conj (coefficient j))*
          exp ((rho i+conj (rho j))*(t : Complex)))) := by
  rw [ofReal_pow, <- mul_conj', map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul, <- exp_conj]
  have he : conj (rho j*(t : Complex)) = conj (rho j)*(t : Complex) := by simp
  rw [he]
  calc
    _ = (coefficient i*conj (coefficient j))*
        (exp (rho i*(t : Complex))*exp (conj (rho j)*(t : Complex))) := by ring
    _ = _ := by
      rw [<- exp_add]
      congr 2
      ring

theorem finite_mellin_norm_fourth_expansion {I : Type*} (A : Finset I)
    (coefficient rho : I -> Complex) (t : Real) :
    ((norm (Finset.sum A (fun i => coefficient i*exp (rho i*(t : Complex))))^4 : Real) :
        Complex) =
      Finset.sum A (fun i => Finset.sum A (fun j =>
        Finset.sum A (fun k => Finset.sum A (fun l =>
          ((coefficient i*coefficient j)*conj (coefficient k*coefficient l))*
            exp ((rho i+rho j+conj (rho k+rho l))*(t : Complex)))))) := by
  classical
  have hsum : Finset.sum (SProd.sprod A A : Finset (Prod I I))
      (fun p => (coefficient p.1*coefficient p.2)*
        exp ((rho p.1+rho p.2)*(t : Complex))) =
      (Finset.sum A (fun i => coefficient i*exp (rho i*(t : Complex))))^2 := by
    rw [Finset.sum_product, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [show (rho i+rho j)*(t : Complex) =
      rho i*(t : Complex)+rho j*(t : Complex) by ring, exp_add]
    ring
  have h := finite_mellin_norm_sq_expansion (SProd.sprod A A : Finset (Prod I I))
    (fun p => coefficient p.1*coefficient p.2) (fun p => rho p.1+rho p.2) t
  rw [hsum, norm_pow] at h
  simpa only [<- pow_mul, Finset.sum_product] using h

theorem integral_norm_fourth_mellin_sum_le_frequency {I : Type*}
    (A : Finset I) (coefficient rho : I -> Complex)
    {X sigma : Real} (hX : 1 <= X) (hsigma : sigma <= 1)
    (hrho : forall i, (A : Set I) i -> 0 <= (rho i).re /\ (rho i).re <= sigma) :
    IntervalIntegrable (fun y : Real =>
      norm (Finset.sum A (fun i => coefficient i*exp (rho i*(Real.log y : Complex))))^4)
      MeasureTheory.volume (X/2) (8*X) /\
    intervalIntegral (fun y : Real =>
      norm (Finset.sum A (fun i => coefficient i*exp (rho i*(Real.log y : Complex))))^4)
      (X/2) (8*X) MeasureTheory.volume <=
      (65536*X^(1+4*sigma))*Finset.sum A (fun i => Finset.sum A (fun j =>
        Finset.sum A (fun k => Finset.sum A (fun l =>
          ((norm (coefficient i)*norm (coefficient j))*
            (norm (coefficient k)*norm (coefficient l))) /
              max 1 (abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im)))))) := by
  let q : I -> I -> I -> I -> Real -> Complex := fun i j k l y =>
    ((coefficient i*coefficient j)*conj (coefficient k*coefficient l))*
      exp ((rho i+rho j+conj (rho k+rho l))*(Real.log y : Complex))
  have hab : X/2 <= 8*X := by linarith
  have hlog : ContinuousOn Real.log (Set.uIcc (X/2) (8*X)) := by
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    have hy0 : 0 < y := by linarith [hy.1]
    exact (Real.hasDerivAt_log hy0.ne').continuousAt.continuousWithinAt
  have hEc (z : Complex) :
      ContinuousOn (fun y => exp (z*(Real.log y : Complex))) (Set.uIcc (X/2) (8*X)) :=
    continuous_exp.comp_continuousOn
      (continuousOn_const.mul (continuous_ofReal.comp_continuousOn hlog))
  have hqc (i j k l : I) : ContinuousOn (q i j k l) (Set.uIcc (X/2) (8*X)) :=
    continuousOn_const.mul (hEc _)
  have hC2 (i j : I) : ContinuousOn
      (fun y => Finset.sum A (fun k => Finset.sum A (fun l => q i j k l y)))
      (Set.uIcc (X/2) (8*X)) :=
    continuousOn_finsetSum A (fun k _ => continuousOn_finsetSum A (fun l _ => hqc i j k l))
  have hC3 (i : I) : ContinuousOn
      (fun y => Finset.sum A (fun j =>
        Finset.sum A (fun k => Finset.sum A (fun l => q i j k l y))))
      (Set.uIcc (X/2) (8*X)) :=
    continuousOn_finsetSum A (fun j _ => hC2 i j)
  have hFC : ContinuousOn (fun y => Finset.sum A (fun i =>
      coefficient i*exp (rho i*(Real.log y : Complex)))) (Set.uIcc (X/2) (8*X)) :=
    continuousOn_finsetSum A (fun i _ => continuousOn_const.mul (hEc (rho i)))
  have hFi : IntervalIntegrable (fun y : Real =>
      norm (Finset.sum A (fun i => coefficient i*exp (rho i*(Real.log y : Complex))))^4)
      MeasureTheory.volume (X/2) (8*X) := (hFC.norm.pow 4).intervalIntegrable
  have he : ((intervalIntegral (fun y : Real =>
      norm (Finset.sum A (fun i => coefficient i*exp (rho i*(Real.log y : Complex))))^4)
      (X/2) (8*X) MeasureTheory.volume : Real) : Complex) =
      Finset.sum A (fun i => Finset.sum A (fun j =>
        Finset.sum A (fun k => Finset.sum A (fun l =>
          ((coefficient i*coefficient j)*conj (coefficient k*coefficient l))*
            intervalIntegral (fun y : Real =>
              exp ((rho i+rho j+conj (rho k+rho l))*(Real.log y : Complex)))
              (X/2) (8*X) MeasureTheory.volume)))) := by
    rw [<- intervalIntegral.integral_ofReal]
    simp_rw [finite_mellin_norm_fourth_expansion]
    change intervalIntegral (fun y => Finset.sum A (fun i => Finset.sum A (fun j =>
      Finset.sum A (fun k => Finset.sum A (fun l => q i j k l y)))))
      (X/2) (8*X) MeasureTheory.volume = _
    rw [intervalIntegral.integral_finsetSum (fun i _ => (hC3 i).intervalIntegrable)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hC2 i j).intervalIntegrable)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_finsetSum (fun k _ =>
      (continuousOn_finsetSum A (fun l _ => hqc i j k l)).intervalIntegrable)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_finsetSum (fun l _ => (hqc i j k l).intervalIntegrable)]
    apply Finset.sum_congr rfl
    intro l hl
    exact intervalIntegral.integral_const_mul _ _
  have hn : 0 <= intervalIntegral (fun y : Real =>
      norm (Finset.sum A (fun i => coefficient i*exp (rho i*(Real.log y : Complex))))^4)
      (X/2) (8*X) MeasureTheory.volume :=
    intervalIntegral.integral_nonneg hab (fun y _ => pow_nonneg (norm_nonneg _) 4)
  refine And.intro hFi ?_
  calc
    _ = norm ((intervalIntegral (fun y : Real =>
        norm (Finset.sum A (fun i => coefficient i*exp (rho i*(Real.log y : Complex))))^4)
        (X/2) (8*X) MeasureTheory.volume : Real) : Complex) := by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
    _ = _ := congrArg norm he
    _ <= _ := by
      simp only [Finset.mul_sum]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro l hl
      have hs0 : 0 <= (rho i+rho j+conj (rho k+rho l)).re := by
        simp only [add_re, conj_re]
        linarith [(hrho i hi).1, (hrho j hj).1, (hrho k hk).1, (hrho l hl).1]
      have hs1 : (rho i+rho j+conj (rho k+rho l)).re <= 4*sigma := by
        simp only [add_re, conj_re]
        linarith [(hrho i hi).2, (hrho j hj).2, (hrho k hk).2, (hrho l hl).2]
      have hkernel := norm_integral_exp_log_dyadic_le hX hsigma hs0 hs1
      have him : (rho i+rho j+conj (rho k+rho l)).im =
          (rho i).im+(rho j).im-(rho k).im-(rho l).im := by
        simp only [add_im, conj_im]
        ring
      rw [him] at hkernel
      rw [norm_mul]
      calc
        _ <= norm ((coefficient i*coefficient j)*conj (coefficient k*coefficient l))*
            (65536*X^(1+4*sigma)/
              max 1 (abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im))) :=
          mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
        _ = _ := by
          rw [norm_mul, norm_mul, norm_conj, norm_mul]
          ring

end Complex
