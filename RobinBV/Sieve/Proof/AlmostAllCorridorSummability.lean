/- Copyright (c) 2026 Jonas Whidden. -/
import RobinBV.Sieve.Helpers.LogWindowTest
import RobinBV.Sieve.Helpers.SquareCorridorTest
import RobinBV.Sieve.Proof.ZetaWindowSummability
import Zeta23.WeilEF.Main

/-!
# Almost-all corridor summability

This module proves the compact support and summability hypotheses for the
inner and outer moving-square corridor kernels.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem almost_all_scaledLogWindowTest_contDiff {eta L c : Real} :
    ContDiff Real 2 (scaledLogWindowTest eta L c) := by
  have he (u : Real) :
      Complex.exp ((u : Complex)/2) = (Real.exp (u/2) : Complex) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  have hf : scaledLogWindowTest eta L c = fun u : Real =>
      ((Real.exp (u/2) * logWindowCutoff eta ((u-c)/L) : Real) : Complex) := by
    funext u
    simp only [scaledLogWindowTest, he, Complex.ofReal_mul]
  rw [hf]
  apply Complex.ofRealCLM.contDiff.comp
  unfold logWindowCutoff
  refine ContDiff.mul ?_ (ContDiff.mul ?_ ?_)
  all_goals fun_prop

theorem almost_all_scaledLogWindowTest_hasCompactSupport
    {eta L c : Real} (he : 0 < eta) (hL : 0 < L) :
    HasCompactSupport (scaledLogWindowTest eta L c) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := c) (b := c+L))
  intro u hu
  change Not (scaledLogWindowTest eta L c u = 0) at hu
  have hLi : 0 < Inv.inv L := inv_pos.mpr hL
  apply And.intro
  next =>
    by_contra h
    have huc : u-c < 0 := sub_neg.mpr (lt_of_not_ge h)
    have hv : (u-c)/L <= 0 := by
      rw [div_eq_mul_inv]
      exact mul_nonpos_of_nonpos_of_nonneg huc.le hLi.le
    have hz := logWindowCutoff_zero_left he hv
    exact hu (by simp only [scaledLogWindowTest, hz, mul_zero, Complex.ofReal_zero,
      Complex.exp_zero, zero_mul])
  next =>
    by_contra h
    have huc : L < u-c := by linarith [lt_of_not_ge h]
    have hmul : L * Inv.inv L < (u-c) * Inv.inv L :=
      mul_lt_mul_of_pos_right huc hLi
    have hone : L * Inv.inv L = 1 := by
      field_simp [hL.ne']
    have hv : 1 <= (u-c)/L := by
      rw [div_eq_mul_inv, <- hone]
      exact hmul.le
    have hz := logWindowCutoff_zero_right he hv
    exact hu (by simp only [scaledLogWindowTest, hz, mul_zero, Complex.ofReal_zero,
      Complex.exp_zero, zero_mul])

theorem square_corridor_inner_zero_sum_summable
    {theta eta x : Real} (htheta : 0 <= theta) (htheta2 : 2*theta < 1)
    (heta : 0 < eta) (hx : 0 < x) :
    Summable (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorInnerTest theta eta x)
          (Zeta23.gammaOf rho)) := by
  have hw : 0 < movingSquareLogWidth x := movingSquareLogWidth_pos hx
  have hL : 0 < (1-2*theta)*movingSquareLogWidth x := by
    have hfactor : 0 < 1-2*theta := by linarith
    positivity
  have hcont := almost_all_scaledLogWindowTest_contDiff
    (eta := eta) (L := (1-2*theta)*movingSquareLogWidth x)
    (c := Real.log x+theta*movingSquareLogWidth x)
  have hcomp := almost_all_scaledLogWindowTest_hasCompactSupport
    (eta := eta) (L := (1-2*theta)*movingSquareLogWidth x)
    (c := Real.log x+theta*movingSquareLogWidth x) heta hL
  simpa only [squareCorridorInnerTest] using
    (Zeta23.WeilEF.EF_lit_zetaZeroConfig
      (scaledLogWindowTest eta ((1-2*theta)*movingSquareLogWidth x)
        (Real.log x+theta*movingSquareLogWidth x)) hcont hcomp).1

theorem square_corridor_outer_zero_sum_summable
    {theta eta x : Real} (htheta : 0 <= theta)
    (heta : 0 < eta) (hx : 0 < x) :
    Summable (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf rho)) := by
  have hw : 0 < movingSquareLogWidth x := movingSquareLogWidth_pos hx
  have hL : 0 < (1+2*theta)*movingSquareLogWidth x := by positivity
  have hcont := almost_all_scaledLogWindowTest_contDiff
    (eta := eta) (L := (1+2*theta)*movingSquareLogWidth x)
    (c := Real.log x-theta*movingSquareLogWidth x)
  have hcomp := almost_all_scaledLogWindowTest_hasCompactSupport
    (eta := eta) (L := (1+2*theta)*movingSquareLogWidth x)
    (c := Real.log x-theta*movingSquareLogWidth x) heta hL
  simpa only [squareCorridorOuterTest] using
    (Zeta23.WeilEF.EF_lit_zetaZeroConfig
      (scaledLogWindowTest eta ((1+2*theta)*movingSquareLogWidth x)
        (Real.log x-theta*movingSquareLogWidth x)) hcont hcomp).1

end RobinBV.Sieve
