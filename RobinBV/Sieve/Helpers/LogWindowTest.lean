/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.Deriv.Support
import RobinBV.Sieve.Helpers.SquareIntervalMovingTest

/-!
# Fixed profiles for logarithmic square windows

The unit profile is smooth and compactly supported. The exact square
logarithmic width lies in (0,1] for n>=2, and the existing square test
is identified with the scaled profile without changing its endpoints.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

noncomputable def logWindowCutoff (eta v : Real) : Real :=
  Real.smoothTransition (v/eta) * Real.smoothTransition ((1-v)/eta)

noncomputable def scaledLogWindowTest (eta L c u : Real) : Complex :=
  Complex.exp ((u : Complex)/2) * (logWindowCutoff eta ((u-c)/L) : Complex)

noncomputable def unitLogWindowTest (eta : Real) : Real -> Complex :=
  scaledLogWindowTest eta 1 0

theorem unitLogWindowTest_contDiff (eta : Real) :
    ContDiff Real 2 (unitLogWindowTest eta) := by
  have he (u : Real) :
      Complex.exp ((u : Complex)/2) = (Real.exp (u/2) : Complex) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  have hf : unitLogWindowTest eta = fun u : Real =>
      ((Real.exp (u/2)*logWindowCutoff eta u : Real) : Complex) := by
    funext u
    simp only [unitLogWindowTest, scaledLogWindowTest, sub_zero, div_one, he,
      Complex.ofReal_mul]
  rw [hf]
  apply Complex.ofRealCLM.contDiff.comp
  unfold logWindowCutoff
  refine ContDiff.mul ?_ (ContDiff.mul ?_ ?_)
  all_goals fun_prop

theorem logWindowCutoff_zero_left {eta v : Real} (he : 0 < eta) (hv : v <= 0) :
    logWindowCutoff eta v = 0 := by
  have h := Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg hv he.le)
  simp only [logWindowCutoff, h, zero_mul]

theorem logWindowCutoff_zero_right {eta v : Real} (he : 0 < eta) (hv : 1 <= v) :
    logWindowCutoff eta v = 0 := by
  have h := Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) he.le)
  simp only [logWindowCutoff, h, mul_zero]

theorem unitLogWindowTest_hasCompactSupport {eta : Real} (he : 0 < eta) :
    HasCompactSupport (unitLogWindowTest eta) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := (0 : Real)) (b := 1))
  intro u hu
  change Not (unitLogWindowTest eta u = 0) at hu
  apply And.intro
  next =>
    by_contra h
    have hz := logWindowCutoff_zero_left he (le_of_lt (lt_of_not_ge h))
    exact hu (by simp only [unitLogWindowTest, scaledLogWindowTest, sub_zero,
      div_one, hz, Complex.ofReal_zero, mul_zero])
  next =>
    by_contra h
    have hz := logWindowCutoff_zero_right he (le_of_lt (lt_of_not_ge h))
    exact hu (by simp only [unitLogWindowTest, scaledLogWindowTest, sub_zero,
      div_one, hz, Complex.ofReal_zero, mul_zero])

noncomputable def squareIntervalLogWidth (n : Nat) : Real :=
  Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat)

theorem squareIntervalLogWidth_pos {n : Nat} (hn : 2 <= n) :
    0 < squareIntervalLogWidth n := by
  apply sub_pos.mpr
  apply Real.log_lt_log
  next =>
    exact_mod_cast (by nlinarith : 0 < n*n)
  next =>
    exact_mod_cast (by nlinarith : n*n < (n+1)*(n+1))

theorem squareIntervalLogWidth_le_one {n : Nat} (hn : 2 <= n) :
    squareIntervalLogWidth n <= 1 := by
  have hn0 : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : (0 : Real) < (n : Real)+1 := by positivity
  have hwidth : squareIntervalLogWidth n =
      2*Real.log (((n : Real)+1)/(n : Real)) := by
    unfold squareIntervalLogWidth
    push_cast
    rw [Real.log_mul hnp.ne' hnp.ne', Real.log_mul hn0.ne' hn0.ne',
      Real.log_div hnp.ne' hn0.ne']
    ring
  have hfrac : ((n : Real)+1)/(n : Real)-1 = 1/(n : Real) := by
    field_simp [hn0.ne']
    ring
  have hb := Real.log_le_sub_one_of_pos (_root_.div_pos hnp hn0)
  rw [hfrac] at hb
  have hhalf := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2)
    (show (2 : Real) <= n by exact_mod_cast hn)
  rw [hwidth]
  linarith

theorem squareIntervalLogTest_eq_scaled {n : Nat} (hn : 2 <= n)
    {eta : Real} (he : 0 < eta) :
    squareIntervalLogTest n (eta*squareIntervalLogWidth n) =
      scaledLogWindowTest eta (squareIntervalLogWidth n) (Real.log (n*n : Nat)) := by
  funext u
  have hL := squareIntervalLogWidth_pos hn
  have hleft :
      (u-Real.log (n*n : Nat))/(eta*squareIntervalLogWidth n) =
        ((u-Real.log (n*n : Nat))/squareIntervalLogWidth n)/eta := by
    field_simp [he.ne', hL.ne']
  have hright :
      (Real.log ((n+1)*(n+1) : Nat)-u)/(eta*squareIntervalLogWidth n) =
        (1-(u-Real.log (n*n : Nat))/squareIntervalLogWidth n)/eta := by
    field_simp [he.ne', hL.ne'] <;> dsimp [squareIntervalLogWidth] <;> ring
  have hexp : Complex.exp ((u : Complex)/2) = (Real.exp (u/2) : Complex) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  rw [squareIntervalLogTest, scaledLogWindowTest, logWindowCutoff, hexp]
  rw [hleft, hright]
  push_cast
  ring

noncomputable def logWindowProfile (eta v : Real) : Complex :=
  (logWindowCutoff eta v : Complex)

theorem logWindowProfile_contDiff (eta : Real) :
    ContDiff Real 2 (logWindowProfile eta) := by
  have hreal : ContDiff Real 2 (fun v : Real => logWindowCutoff eta v) := by
    unfold logWindowCutoff
    refine ContDiff.mul ?_ ?_
    all_goals fun_prop
  exact Complex.ofRealCLM.contDiff.comp hreal

theorem logWindowProfile_hasCompactSupport {eta : Real} (he : 0 < eta) :
    HasCompactSupport (logWindowProfile eta) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := (0 : Real)) (b := 1))
  intro u hu
  change Not (logWindowProfile eta u = 0) at hu
  apply And.intro
  next =>
    by_contra h
    have hz := logWindowCutoff_zero_left he (le_of_lt (lt_of_not_ge h))
    exact hu (by simp only [logWindowProfile, hz, Complex.ofReal_zero])
  next =>
    by_contra h
    have hz := logWindowCutoff_zero_right he (le_of_lt (lt_of_not_ge h))
    exact hu (by simp only [logWindowProfile, hz, Complex.ofReal_zero])

theorem logWindowProfile_tsupport_subset {eta : Real} (he : 0 < eta) :
    Set.Subset (tsupport (logWindowProfile eta)) (Set.Icc (0 : Real) 1) := by
  apply closure_minimal ?_ isClosed_Icc
  intro v hv
  change Not (logWindowProfile eta v = 0) at hv
  apply And.intro
  next =>
    by_contra h
    have hz := logWindowCutoff_zero_left he (le_of_lt (lt_of_not_ge h))
    exact hv (by simp only [logWindowProfile, hz, Complex.ofReal_zero])
  next =>
    by_contra h
    have hz := logWindowCutoff_zero_right he (le_of_lt (lt_of_not_ge h))
    exact hv (by simp only [logWindowProfile, hz, Complex.ofReal_zero])

theorem logWindowProfile_second_tsupport_subset {eta : Real} (he : 0 < eta) :
    Set.Subset (tsupport (deriv (deriv (logWindowProfile eta))))
      (Set.Icc (0 : Real) 1) :=
  Set.Subset.trans (tsupport_deriv_subset (f := deriv (logWindowProfile eta)))
    (Set.Subset.trans (tsupport_deriv_subset (f := logWindowProfile eta))
      (logWindowProfile_tsupport_subset he))

theorem logWindowProfile_norm_le_one (eta v : Real) :
    norm (logWindowProfile eta v) <= 1 := by
  have ha0 := Real.smoothTransition.nonneg (v/eta)
  have ha1 := Real.smoothTransition.le_one (v/eta)
  have hb0 := Real.smoothTransition.nonneg ((1-v)/eta)
  have hb1 := Real.smoothTransition.le_one ((1-v)/eta)
  unfold logWindowProfile logWindowCutoff
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha0 hb0)]
  calc
    _ <= 1*Real.smoothTransition ((1-v)/eta) :=
      mul_le_mul_of_nonneg_right ha1 hb0
    _ <= 1 := by simpa only [one_mul] using hb1

theorem scaledLogWindowTest_contDiff (eta L c : Real) :
    ContDiff Real 2 (scaledLogWindowTest eta L c) := by
  have heq : (fun u : Real => Complex.exp ((u : Complex)/2)) =
      fun u : Real => (Real.exp (u/2) : Complex) := by
    funext u
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  change ContDiff Real 2 (fun u : Real =>
    Complex.exp ((u : Complex)/2)*logWindowProfile eta ((u-c)/L))
  refine ContDiff.mul ?_ ?_
  next =>
    rw [heq]
    exact Complex.ofRealCLM.contDiff.comp (by fun_prop :
      ContDiff Real 2 (fun u : Real => Real.exp (u/2)))
  next =>
    exact (logWindowProfile_contDiff eta).comp
      (by fun_prop : ContDiff Real 2 (fun u : Real => (u-c)/L))

theorem scaledLogWindowTest_hasCompactSupport {eta L : Real}
    (he : 0 < eta) (hL : 0 < L) (c : Real) :
    HasCompactSupport (scaledLogWindowTest eta L c) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := c) (b := c+L))
  intro u hu
  change Not (scaledLogWindowTest eta L c u = 0) at hu
  refine And.intro ?_ ?_
  next =>
    by_contra h
    have hz := logWindowCutoff_zero_left (v := (u-c)/L) he
      (div_nonpos_of_nonpos_of_nonneg (by linarith [lt_of_not_ge h]) hL.le)
    exact hu (by simp only [scaledLogWindowTest, hz, Complex.ofReal_zero, mul_zero])
  next =>
    by_contra h
    have hfrac : 1 <= (u-c)/L := by
      calc
        (1 : Real) = L/L := (div_self hL.ne').symm
        _ <= (u-c)/L := div_le_div_of_nonneg_right (by linarith [lt_of_not_ge h]) hL.le
    have hz := logWindowCutoff_zero_right he hfrac
    exact hu (by simp only [scaledLogWindowTest, hz, Complex.ofReal_zero, mul_zero])

end RobinBV.Sieve
