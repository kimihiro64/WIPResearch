/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import RobinBV.Sieve.Helpers.SquareIntervalMovingTest
import Zeta23.Defs

/-!
# Growing pole supply for the square-interval test

The two smooth transitions equal one throughout the inner core.
Nonnegativity on the complement retains the complete lower supply,
including the zero-width core endpoint. No zero estimate is used.
-/

set_option autoImplicit false

open MeasureTheory

namespace RobinBV.Sieve

theorem squareIntervalLogTest_pole_lower {n : Nat} (hn : 2 <= n)
    {w : Real} (hw : 0 < w)
    (hwidth : 2*w <= Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat)) :
    (n : Real)^2 * (Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat)-2*w) <=
      (Zeta23.paperFT (squareIntervalLogTest n w) (-Complex.I/2)).re := by
  let c : Real := Real.log (n*n : Nat)
  let d : Real := Real.log ((n+1)*(n+1) : Nat)
  let f : Real -> Real := fun u => (squareIntervalLogTest n w u).re * Real.exp (u/2)
  have hcont : Continuous f :=
    (Complex.continuous_re.comp (squareIntervalLogTest_contDiff n w).continuous).mul
      (Real.continuous_exp.comp (continuous_id.div_const 2))
  have hcomp : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := c) (b := d))
    intro u hu
    change Not (f u = 0) at hu
    apply And.intro
    next =>
      by_contra h
      have hz := squareIntervalLogTest_zero_left hw
        (show u <= Real.log (n*n : Nat) from le_of_lt (lt_of_not_ge h))
      exact hu (by dsimp [f]; rw [hz, Complex.zero_re, zero_mul])
    next =>
      by_contra h
      have hz := squareIntervalLogTest_zero_right hw
        (show Real.log ((n+1)*(n+1) : Nat) <= u from le_of_lt (lt_of_not_ge h))
      exact hu (by dsimp [f]; rw [hz, Complex.zero_re, zero_mul])
  have hf : Integrable f := hcont.integrable_of_hasCompactSupport hcomp
  have hnonneg (u : Real) : 0 <= f u := by
    dsimp [f, squareIntervalLogTest]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le
        (Real.smoothTransition.nonneg _)) (Real.smoothTransition.nonneg _))
      (Real.exp_pos _).le
  have hexp (u : Real) :
      Complex.exp (Complex.I*(-Complex.I/2)*(u : Complex)) =
        (Real.exp (u/2) : Complex) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hfun : (fun u : Real => squareIntervalLogTest n w u *
      Complex.exp (Complex.I*(-Complex.I/2)*(u : Complex))) =
      fun u : Real => (f u : Complex) := by
    funext u
    rw [hexp]
    dsimp [f, squareIntervalLogTest]
    push_cast
    rfl
  have hpole : (Zeta23.paperFT (squareIntervalLogTest n w) (-Complex.I/2)).re =
      MeasureTheory.integral MeasureTheory.volume f := by
    rw [Zeta23.paperFT, hfun, _root_.integral_complex_ofReal, Complex.ofReal_re]
  have hcd : c+w <= d-w := by dsimp [c, d]; linarith only [hwidth]
  have hcore (u : Real) (hu : Membership.mem (Set.Icc (c+w) (d-w)) u) :
      (n : Real)^2 <= f u := by
    have hleft : 1 <= (u-c)/w := (_root_.one_le_div hw).mpr (by linarith [hu.1])
    have hright : 1 <= (d-u)/w := (_root_.one_le_div hw).mpr (by linarith [hu.2])
    have h1 := Real.smoothTransition.one_of_one_le hleft
    have h2 := Real.smoothTransition.one_of_one_le hright
    have he : Real.exp (u/2)*Real.exp (u/2) = Real.exp u := by
      rw [<- Real.exp_add]
      congr 1
      ring
    have hfval : f u = Real.exp u := by
      dsimp [f, squareIntervalLogTest]
      change (Real.exp (u/2)*Real.smoothTransition ((u-c)/w)*
        Real.smoothTransition ((d-u)/w))*Real.exp (u/2) = Real.exp u
      rw [h1, h2, mul_one, mul_one, he]
    have hnpos : (0 : Real) < (n*n : Nat) := by
      exact_mod_cast (by nlinarith : 0 < n*n)
    have hbase : Real.exp c = (n : Real)^2 := by
      dsimp [c]
      rw [Real.exp_log hnpos]
      push_cast
      ring
    rw [hfval, <- hbase]
    exact Real.exp_le_exp.mpr (by linarith [hu.1])
  have hlocal : (n : Real)^2 * MeasureTheory.volume.real (Set.Icc (c+w) (d-w)) <=
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (c+w) (d-w))) f :=
    MeasureTheory.setIntegral_ge_of_const_le_real
      measurableSet_Icc isCompact_Icc.measure_lt_top.ne hcore hf.integrableOn
  have hglobal := MeasureTheory.setIntegral_le_integral
    (s := Set.Icc (c+w) (d-w)) hf (Filter.Eventually.of_forall hnonneg)
  rw [Real.volume_real_Icc_of_le hcd] at hlocal
  rw [hpole]
  calc
    _ = (n : Real)^2*((d-w)-(c+w)) := by dsimp [c, d]; ring
    _ <= _ := hlocal.trans hglobal

end RobinBV.Sieve
