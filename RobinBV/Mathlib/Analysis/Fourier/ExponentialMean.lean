/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RobinBV.Mathlib.Analysis.SpecificLimits.IntervalMean

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

/-- Complete exponential series with arbitrary real frequencies. -/
def exponentialSeries {I : Type*} (c : I -> Complex) (omega : I -> Real) (t : Real) : Complex :=
  tsum (fun i => c i*Complex.exp ((omega i : Complex)*Complex.I*(t : Complex)))

/-- Actual integral mean of the complete exponential series. -/
def exponentialSeriesMean {I : Type*} (c : I -> Complex) (omega : I -> Real) (T : Real) : Complex :=
  intervalMean (exponentialSeries c omega) T

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
  unfold exponentialSeriesMean intervalMean exponentialSeries
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

/-- Absolute summability makes the full exponential series continuous. -/
theorem continuous_exponentialSeries {I : Type*} (c : I -> Complex) (omega : I -> Real)
    (hC : Summable (fun i => norm (c i))) : Continuous (exponentialSeries c omega) := by
  apply continuous_tsum (fun _i => by fun_prop) hC
  intro i t
  rw [norm_mul, Complex.norm_exp]
  simp

/-- A uniform full-series bound, independent of time and frequency gaps. -/
theorem norm_exponentialSeries_le {I : Type*} (c : I -> Complex) (omega : I -> Real)
    (hC : Summable (fun i => norm (c i))) (t : Real) :
    norm (exponentialSeries c omega t) <= tsum (fun i => norm (c i)) := by
  have hNorm (i : I) : norm (c i*Complex.exp ((omega i : Complex)*Complex.I*(t : Complex)))=norm (c i) := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have hAbs : Summable (fun i => norm (c i*Complex.exp ((omega i : Complex)*Complex.I*(t : Complex)))) :=
    hC.congr (fun i => (hNorm i).symm)
  exact (norm_tsum_le_tsum_norm hAbs).trans_eq (tsum_congr hNorm)

private theorem phase_clock_error_tendsto (omega : Real) :
    Tendsto (fun t : Real =>
      Complex.exp ((omega : Complex)*Complex.I*(Real.log (Nat.floor (Real.exp t) : Real) : Complex)) -
        Complex.exp ((omega : Complex)*Complex.I*(t : Complex))) atTop (nhds (0 : Complex)) := by
  have hDelta := (Complex.continuous_ofReal.tendsto 0).comp tendsto_log_nat_floor_exp_sub_self
  have hSmall : Tendsto (fun t : Real =>
      Complex.exp ((omega : Complex)*Complex.I*((Real.log (Nat.floor (Real.exp t) : Real)-t : Real) : Complex))-1)
      atTop (nhds (0 : Complex)) := by
    have hArg : Tendsto (fun t : Real =>
        (omega : Complex)*Complex.I*((Real.log (Nat.floor (Real.exp t) : Real)-t : Real) : Complex))
        atTop (nhds (0 : Complex)) := by
      simpa only [Function.comp_def, Complex.ofReal_zero, mul_zero] using
        hDelta.const_mul ((omega : Complex)*Complex.I)
    have h := ((Complex.continuous_exp.tendsto 0).comp hArg).sub_const 1
    simpa only [Function.comp_def, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hNormSmall := hSmall.norm
  simp only [norm_zero] at hNormSmall
  apply hNormSmall.congr'
  apply Filter.Eventually.of_forall
  intro t
  have hArg : (omega : Complex)*Complex.I*(Real.log (Nat.floor (Real.exp t) : Real) : Complex) =
      (omega : Complex)*Complex.I*(t : Complex) +
        (omega : Complex)*Complex.I*((Real.log (Nat.floor (Real.exp t) : Real)-t : Real) : Complex) := by
    push_cast
    ring
  dsimp only
  rw [hArg, Complex.exp_add]
  have hFactor (a b : Complex) : a*b-a=a*(b-1) := by ring
  rw [hFactor, norm_mul, Complex.norm_exp]
  simp

/-- Replacing exponential time by its logarithmic floor clock has a
vanishing full-series error. No summable first frequency moment is needed. -/
theorem exponentialSeries_logFloor_sub_tendsto_zero {I : Type*}
    (c : I -> Complex) (omega : I -> Real) (hC : Summable (fun i => norm (c i))) :
    Tendsto (fun t : Real => exponentialSeries c omega (Real.log (Nat.floor (Real.exp t) : Real)) -
      exponentialSeries c omega t) atTop (nhds (0 : Complex)) := by
  have hNorm (i : I) (t : Real) :
      norm (c i*Complex.exp ((omega i : Complex)*Complex.I*(t : Complex)))=norm (c i) := by
    rw [norm_mul, Complex.norm_exp]
    simp
  have hSeries (t : Real) : Summable (fun i => c i*Complex.exp ((omega i : Complex)*Complex.I*(t : Complex))) :=
    hC.of_norm_bounded (fun i => (hNorm i t).le)
  have hPoint (i : I) : Tendsto (fun t : Real =>
      c i*Complex.exp ((omega i : Complex)*Complex.I*(Real.log (Nat.floor (Real.exp t) : Real) : Complex)) -
        c i*Complex.exp ((omega i : Complex)*Complex.I*(t : Complex))) atTop (nhds (0 : Complex)) := by
    simpa only [mul_sub, mul_zero] using (phase_clock_error_tendsto (omega i)).const_mul (c i)
  have hBound : Filter.Eventually (fun t : Real => forall i,
      norm (c i*Complex.exp ((omega i : Complex)*Complex.I*(Real.log (Nat.floor (Real.exp t) : Real) : Complex)) -
        c i*Complex.exp ((omega i : Complex)*Complex.I*(t : Complex))) <= 2*norm (c i)) atTop := by
    apply Filter.Eventually.of_forall
    intro t i
    exact (norm_sub_le _ _).trans_eq (by rw [hNorm, hNorm]; ring)
  have h := tendsto_tsum_of_dominated_convergence (hC.mul_left 2) hPoint hBound
  simp only [tsum_zero] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro t
  exact (hSeries (Real.log (Nat.floor (Real.exp t) : Real))).tsum_sub (hSeries t)

/-- The complete spectral mean is preserved by logarithmic floor sampling.
The proof controls the whole clock error before averaging it. -/
theorem tendsto_exponentialSeries_logFloorMean {I : Type*} [Countable I]
    (c : I -> Complex) (omega : I -> Real) (hC : Summable (fun i => norm (c i))) :
    Tendsto (intervalMean (fun t : Real =>
      exponentialSeries c omega (Real.log (Nat.floor (Real.exp t) : Real)))) atTop
      (nhds (tsum (fun i => if omega i=0 then c i else 0))) := by
  have hCont := continuous_exponentialSeries c omega hC
  have hClock : Measurable (fun t : Real => Real.log (Nat.floor (Real.exp t) : Real)) :=
    Real.measurable_log.comp ((measurable_of_countable (fun n : Nat => (n : Real))).comp
      (Nat.measurable_floor.comp Real.measurable_exp))
  have hMeas : StronglyMeasurable (fun t : Real =>
      exponentialSeries c omega (Real.log (Nat.floor (Real.exp t) : Real)) -
        exponentialSeries c omega t) :=
    ((hCont.measurable.comp hClock).sub hCont.measurable).stronglyMeasurable
  have hBound (t : Real) :
      norm (exponentialSeries c omega (Real.log (Nat.floor (Real.exp t) : Real)) -
        exponentialSeries c omega t) <= 2*tsum (fun i => norm (c i)) := by
    exact (norm_sub_le _ _).trans ((add_le_add
      (norm_exponentialSeries_le c omega hC _) (norm_exponentialSeries_le c omega hC t)).trans_eq (by ring))
  have hError := tendsto_intervalMean_of_bounded_tendsto _ hMeas hBound
    (exponentialSeries_logFloor_sub_tendsto_zero c omega hC)
  have h := hError.add (tendsto_exponentialSeriesMean c omega hC)
  simp only [zero_add] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro T
  have hFloorInt := intervalIntegrable_nat_floor_exp
    (fun n : Nat => exponentialSeries c omega (Real.log (n : Real))) 0 T
  have hContInt : IntervalIntegrable (exponentialSeries c omega) volume 0 T :=
    hCont.intervalIntegrable 0 T
  simp only [exponentialSeriesMean, intervalMean]
  rw [intervalIntegral.integral_sub hFloorInt hContInt]
  ring

end

end Complex
