/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Smooth logarithmic square-interval test

Regularity, compact support, endpoint vanishing and normalized arithmetic
weights are proved for the concrete product of two smooth transitions.
-/

set_option autoImplicit false

namespace RobinBV.Sieve


noncomputable def squareIntervalLogTest (n : Nat) (w u : Real) : Complex :=
  ((Real.exp (u/2) *
    Real.smoothTransition ((u-Real.log (n*n : Nat))/w) *
    Real.smoothTransition ((Real.log ((n+1)*(n+1) : Nat)-u)/w) : Real) : Complex)

theorem squareIntervalLogTest_contDiff (n : Nat) (w : Real) :
    ContDiff Real 2 (squareIntervalLogTest n w) := by
  unfold squareIntervalLogTest
  refine Complex.ofRealCLM.contDiff.comp ?_
  refine ContDiff.mul (ContDiff.mul ?_ ?_) ?_
  all_goals fun_prop

theorem squareIntervalLogTest_zero_left {n : Nat} {w u : Real}
    (hw : 0 < w) (hu : u <= Real.log (n*n : Nat)) :
    squareIntervalLogTest n w u = 0 := by
  have h : Real.smoothTransition ((u-Real.log (n*n : Nat))/w) = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) hw.le)
  simp only [squareIntervalLogTest, h, mul_zero, zero_mul, Complex.ofReal_zero]

theorem squareIntervalLogTest_zero_right {n : Nat} {w u : Real}
    (hw : 0 < w) (hu : Real.log ((n+1)*(n+1) : Nat) <= u) :
    squareIntervalLogTest n w u = 0 := by
  have h : Real.smoothTransition ((Real.log ((n+1)*(n+1) : Nat)-u)/w) = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) hw.le)
  simp only [squareIntervalLogTest, h, mul_zero, Complex.ofReal_zero]

theorem squareIntervalLogTest_hasCompactSupport {n : Nat} {w : Real}
    (hw : 0 < w) : HasCompactSupport (squareIntervalLogTest n w) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := Real.log (n*n : Nat))
      (b := Real.log ((n+1)*(n+1) : Nat)))
  intro u hu
  change Not (squareIntervalLogTest n w u = 0) at hu
  apply And.intro
  next =>
    by_contra h
    exact hu (squareIntervalLogTest_zero_left hw (le_of_lt (lt_of_not_ge h)))
  next =>
    by_contra h
    exact hu (squareIntervalLogTest_zero_right hw (le_of_lt (lt_of_not_ge h)))

theorem squareIntervalLogTest_negative {n : Nat} (hn : 2 <= n)
    {w : Real} (hw : 0 < w) (m : Nat) :
    squareIntervalLogTest n w (-Real.log m) = 0 := by
  have ha : 0 <= Real.log (n*n : Nat) :=
    Real.log_nonneg (by exact_mod_cast (by nlinarith : 1 <= n*n))
  have hm : 0 <= Real.log (m : Real) := by
    by_cases hm0 : m = 0
    next =>
      simp only [hm0, Nat.cast_zero, Real.log_zero, le_refl]
    next =>
      exact Real.log_nonneg (by exact_mod_cast (by omega : 1 <= m))
  exact squareIntervalLogTest_zero_left hw (by linarith)

theorem squareIntervalLogTest_arithmetic_support {n : Nat} (hn : 2 <= n)
    {w : Real} (hw : 0 < w) (m : Nat)
    (hm : Not (Membership.mem (Finset.Ioo (n*n) ((n+1)*(n+1))) m)) :
    squareIntervalLogTest n w (Real.log m) = 0 := by
  have ha : 0 <= Real.log (n*n : Nat) :=
    Real.log_nonneg (by exact_mod_cast (by nlinarith : 1 <= n*n))
  by_cases hm0 : m = 0
  next =>
    rw [hm0, Nat.cast_zero, Real.log_zero]
    exact squareIntervalLogTest_zero_left hw ha
  have hmpos : (0 : Real) < m := by exact_mod_cast (by omega : 0 < m)
  by_cases hsmall : m <= n*n
  next =>
    exact squareIntervalLogTest_zero_left hw
      (Real.log_le_log hmpos (by exact_mod_cast hsmall))
  next =>
    have hlarge : (n+1)*(n+1) <= m := by
      have hnot : Not (n*n < m /\ m < (n+1)*(n+1)) := by
        simpa only [Finset.mem_Ioo] using hm
      omega
    exact squareIntervalLogTest_zero_right hw
      (Real.log_le_log (by positivity) (by exact_mod_cast hlarge))

theorem squareIntervalLogTest_weight {n : Nat} (hn : 2 <= n)
    (w : Real) (m : Nat)
    (hm : Membership.mem (Finset.Ioo (n*n) ((n+1)*(n+1))) m) :
    0 <= (squareIntervalLogTest n w (Real.log m)).re / Real.sqrt m /\
      (squareIntervalLogTest n w (Real.log m)).re / Real.sqrt m <= 1 := by
  have hmnat : 0 < m := by have h := (Finset.mem_Ioo.mp hm).1; nlinarith
  have hmpos : (0 : Real) < m := by exact_mod_cast hmnat
  have hsqrt : Real.exp (Real.log m/2) = Real.sqrt m := by
    have hsq : Real.exp (Real.log m/2)^2 = (m : Real) := by
      calc
        _ = Real.exp (Real.log m/2 + Real.log m/2) := by
          rw [Real.exp_add]
          ring
        _ = Real.exp (Real.log m) := by congr 1; ring
        _ = (m : Real) := Real.exp_log hmpos
    have hs := Real.sq_sqrt hmpos.le
    have hpos := Real.exp_pos (Real.log m/2)
    have hspos := Real.sqrt_pos.mpr hmpos
    nlinarith
  have hval : (squareIntervalLogTest n w (Real.log m)).re / Real.sqrt m =
      Real.smoothTransition ((Real.log m-Real.log (n*n : Nat))/w) *
      Real.smoothTransition ((Real.log ((n+1)*(n+1) : Nat)-Real.log m)/w) := by
    simp only [squareIntervalLogTest, Complex.ofReal_re, hsqrt]
    field_simp [(Real.sqrt_pos.mpr hmpos).ne']
  rw [hval]
  apply And.intro
  next =>
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  next =>
    have h := mul_le_mul (Real.smoothTransition.le_one
        ((Real.log m-Real.log (n*n : Nat))/w))
        (Real.smoothTransition.le_one
          ((Real.log ((n+1)*(n+1) : Nat)-Real.log m)/w))
        (Real.smoothTransition.nonneg _) (by norm_num : (0 : Real) <= 1)
    simpa only [mul_one] using h

theorem squareIntervalLogTest_norm_le (n : Nat) (w u : Real) :
    norm (squareIntervalLogTest n w u) <= Real.exp (u/2) := by
  have h1 := Real.smoothTransition.nonneg ((u-Real.log (n*n : Nat))/w)
  have h2 := Real.smoothTransition.nonneg ((Real.log ((n+1)*(n+1) : Nat)-u)/w)
  have hb1 := Real.smoothTransition.le_one ((u-Real.log (n*n : Nat))/w)
  have hb2 := Real.smoothTransition.le_one ((Real.log ((n+1)*(n+1) : Nat)-u)/w)
  rw [squareIntervalLogTest, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le h1) h2)]
  calc
    _ <= (Real.exp (u/2)*1)*1 :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hb1 (Real.exp_pos _).le) hb2 h2 (by positivity)
    _ = _ := by ring

end RobinBV.Sieve
