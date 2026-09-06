/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Cesaro means of absolutely convergent exponential series

Arbitrary real frequencies may accumulate at zero. The full mean tends to
the sum of the zero-frequency coefficients, not necessarily to zero.
-/

namespace Complex

open Filter MeasureTheory

noncomputable section

/-- Actual continuous Cesaro mean of one real-frequency exponential. -/
def exponentialMean (omega T : Real) : Complex :=
  Inv.inv (T : Complex) * intervalIntegral
    (fun t : Real => Complex.exp ((omega : Complex)*Complex.I*(t : Complex))) 0 T volume

/-- Frequency-independent bound for the full exponential mean. -/
theorem norm_exponentialMean_le_one (omega : Real) {T : Real} (hT : 0 < T) :
    norm (exponentialMean omega T) <= 1 := by
  have hExp (t : Real) : norm (Complex.exp ((omega : Complex)*Complex.I*(t : Complex))) = 1 := by
    rw [Complex.norm_exp]
    simp
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : Real)) (b := T) (C := (1 : Real)) (fun t _ => (hExp t).le)
  unfold exponentialMean
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  apply (mul_le_mul_of_nonneg_left hIntegral (inv_pos.mpr hT).le).trans_eq
  simp [abs_of_pos hT, hT.ne']

/-- Exact integral formula at every nonzero frequency. -/
theorem exponentialMean_eq_of_ne_zero {omega : Real} (hOmega : Not (omega=0)) (T : Real) :
    exponentialMean omega T = Inv.inv (T : Complex)*
      ((Complex.exp ((omega : Complex)*Complex.I*(T : Complex))-1)/((omega : Complex)*Complex.I)) := by
  have hC : Not ((omega : Complex)*Complex.I=0) :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hOmega) Complex.I_ne_zero
  unfold exponentialMean
  rw [integral_exp_mul_complex hC]
  simp

/-- The zero-frequency mean retains its constant contribution. -/
theorem exponentialMean_zero_frequency {T : Real} (hT : Not (T=0)) :
    exponentialMean 0 T = 1 := by
  simp [exponentialMean, hT]

/-- Quantitative decay for a fixed nonzero frequency; no uniform frequency gap is assumed. -/
theorem norm_exponentialMean_le_inv_mul {omega : Real} (hOmega : Not (omega=0))
    {T : Real} (hT : 0 < T) :
    norm (exponentialMean omega T) <= Inv.inv T*(2/norm ((omega : Complex)*Complex.I)) := by
  have hExp : norm (Complex.exp ((omega : Complex)*Complex.I*(T : Complex)))=1 := by
    rw [Complex.norm_exp]
    simp
  rw [exponentialMean_eq_of_ne_zero hOmega, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hT, norm_div]
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hT).le
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  simpa only [hExp, norm_one, one_add_one_eq_two] using
    norm_sub_le (Complex.exp ((omega : Complex)*Complex.I*(T : Complex))) 1

/-- Each exponential mean tends to its zero-frequency indicator. -/
theorem tendsto_exponentialMean (omega : Real) :
    Tendsto (exponentialMean omega) atTop (nhds (if omega=0 then (1 : Complex) else 0)) := by
  classical
  by_cases hOmega : omega=0
  next =>
    subst omega
    simp only [ite_true]
    apply (tendsto_const_nhds : Tendsto (fun _ : Real => (1 : Complex)) atTop (nhds 1)).congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with T hT
    exact (exponentialMean_zero_frequency hT.ne').symm
  next =>
    simp only [hOmega, ite_false]
    have hUpper : Tendsto (fun T : Real => Inv.inv T*(2/norm ((omega : Complex)*Complex.I)))
        atTop (nhds (0 : Real)) := by
      simpa only [zero_mul] using tendsto_inv_atTop_zero.mul_const (2/norm ((omega : Complex)*Complex.I))
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with T hT
    exact norm_exponentialMean_le_inv_mul hOmega hT

/-- Actual integral mean of the complete exponential series. -/
def exponentialSeriesMean {I : Type*} (c : I -> Complex) (omega : I -> Real) (T : Real) : Complex :=
  Inv.inv (T : Complex) * intervalIntegral
    (fun t : Real => tsum (fun i => c i * Complex.exp ((omega i : Complex)*Complex.I*(t : Complex))))
    0 T volume

/-- Full mean and complete series interchange under absolute summability. -/
theorem exponentialSeriesMean_eq_tsum {I : Type*} [Countable I]
    (c : I -> Complex) (omega : I -> Real) (hC : Summable (fun i => norm (c i))) (T : Real) :
    exponentialSeriesMean c omega T = tsum (fun i => c i * exponentialMean (omega i) T) := by
  have hNorm (i : I) (t : Real) :
      norm (c i*Complex.exp ((omega i : Complex)*Complex.I*(t : Complex)))=norm (c i) := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have hCont (i : I) : Continuous
      (fun t : Real => c i * Complex.exp ((omega i : Complex)*Complex.I*(t : Complex))) := by fun_prop
  have hSum (t : Real) : Summable
      (fun i => c i * Complex.exp ((omega i : Complex)*Complex.I*(t : Complex))) :=
    hC.of_norm_bounded (fun i => (hNorm i t).le)
  have hIntegral : HasSum (fun i => intervalIntegral
      (fun t : Real => c i*Complex.exp ((omega i : Complex)*Complex.I*(t : Complex))) 0 T volume)
      (intervalIntegral (fun t : Real => tsum
        (fun i => c i*Complex.exp ((omega i : Complex)*Complex.I*(t : Complex)))) 0 T volume) :=
    intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : Real)) (b := T)
    (fun i (_t : Real) => norm (c i))
    (fun i => (hCont i).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall (fun t _ => (hNorm i t).le))
    (Filter.Eventually.of_forall (fun _t _ => hC)) intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ => (hSum t).hasSum))
  unfold exponentialSeriesMean
  rw [<- hIntegral.tsum_eq, <- tsum_mul_left]
  apply tsum_congr
  intro i
  rw [intervalIntegral.integral_const_mul]
  unfold exponentialMean
  ring

/-- The full Cesaro mean is exactly the zero-frequency coefficient sum in the limit.
No noncentrality, frequency separation or independence hypothesis is used. -/
theorem tendsto_exponentialSeriesMean {I : Type*} [Countable I]
    (c : I -> Complex) (omega : I -> Real) (hC : Summable (fun i => norm (c i))) :
    Tendsto (exponentialSeriesMean c omega) atTop
      (nhds (tsum (fun i => if omega i=0 then c i else 0))) := by
  classical
  have hPoint (i : I) : Tendsto (fun T : Real => c i*exponentialMean (omega i) T) atTop
      (nhds (if omega i=0 then c i else 0)) := by
    simpa only [mul_ite, mul_one, mul_zero] using (tendsto_exponentialMean (omega i)).const_mul (c i)
  have hBound : Filter.Eventually (fun T : Real => forall i,
      norm (c i*exponentialMean (omega i) T) <= norm (c i)) atTop := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with T hT i
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_exponentialMean_le_one (omega i) hT) (norm_nonneg _)).trans_eq
      (mul_one _)
  have h := tendsto_tsum_of_dominated_convergence hC hPoint hBound
  apply h.congr'
  exact Filter.Eventually.of_forall (fun T => (exponentialSeriesMean_eq_tsum c omega hC T).symm)

end

end Complex
