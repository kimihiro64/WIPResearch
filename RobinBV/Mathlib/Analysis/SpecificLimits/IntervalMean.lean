/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Interval means and logarithmic sampling of convergent sequences

A bounded measurable convergent function preserves its limit under interval
averaging. Convergence of a sequence supplies all boundedness and measurability
needed for its logarithmic floor-exponential sampling.
-/

namespace Complex

open Filter MeasureTheory

noncomputable section

/-- Actual continuous interval mean with base point zero. -/
def intervalMean (f : Real -> Complex) (T : Real) : Complex :=
  Inv.inv (T : Complex)*intervalIntegral f 0 T volume

/-- A bounded strongly measurable function preserves its limit under continuous Cesaro averaging. -/
theorem tendsto_intervalMean_of_bounded_tendsto (f : Real -> Complex) (hf : StronglyMeasurable f) {C : Real} {L : Complex}
    (hBound : forall t : Real, norm (f t) <= C) (hLim : Tendsto f atTop (nhds L)) :
    Tendsto (intervalMean f) atTop (nhds L) := by
  have hScaled : Tendsto (fun T : Real => intervalIntegral (fun x : Real => f (x*T)) 0 1 volume)
      atTop (nhds (intervalIntegral (fun _x : Real => L) 0 1 volume)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _x : Real => C)
    next =>
      exact Filter.Eventually.of_forall (fun T =>
        (hf.comp_measurable (measurable_id.mul_const T)).aestronglyMeasurable)
    next =>
      exact Filter.Eventually.of_forall (fun T =>
        Filter.Eventually.of_forall (fun x _hx => hBound (x*T)))
    next => exact intervalIntegrable_const
    next =>
      apply Filter.Eventually.of_forall
      intro x hx
      have hxI : Membership.mem (Set.Ioc (0 : Real) 1) x := by
        simpa only [Set.uIoc_of_le (by norm_num : (0 : Real)<=1)] using hx
      exact hLim.comp ((tendsto_const_mul_atTop_of_pos hxI.1).2 tendsto_id)
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hScaled
  apply hScaled.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with T hT
  have hChange := intervalIntegral.smul_integral_comp_mul_right (a := (0 : Real)) (b := (1 : Real)) f T
  simp only [zero_mul, one_mul, Complex.real_smul] at hChange
  unfold intervalMean
  rw [<-hChange]
  field_simp [Complex.ofReal_ne_zero.mpr hT.ne']
  simp only [mul_comm]

/-- Exact rescaling of the actual interval mean. -/
theorem intervalMean_comp_mul (f : Real -> Complex) {a : Real} (ha : Not (a=0)) (T : Real) :
    intervalMean (fun t => f (a*t)) T = intervalMean f (a*T) := by
  have hChange := intervalIntegral.smul_integral_comp_mul_left (a := (0 : Real)) (b := T) f a
  simp only [mul_zero, Complex.real_smul] at hChange
  unfold intervalMean
  rw [<-hChange]
  simp only [Complex.ofReal_mul, mul_inv_rev]
  simp [mul_assoc, Complex.ofReal_ne_zero.mpr ha]

/-- Every convergent complex sequence preserves its limit after logarithmic
floor sampling and actual continuous averaging; its boundedness is derived. -/
theorem tendsto_intervalMean_nat_floor_exp (u : Nat -> Complex) {L : Complex}
    (hU : Tendsto u atTop (nhds L)) :
    Tendsto (intervalMean (fun t : Real => u (Nat.floor (Real.exp t)))) atTop (nhds L) := by
  choose C hC using (isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto u hU))
  have hMeas : Measurable (fun t : Real => u (Nat.floor (Real.exp t))) :=
    (measurable_of_countable u).comp (Nat.measurable_floor.comp Real.measurable_exp)
  have hLim : Tendsto (fun t : Real => u (Nat.floor (Real.exp t))) atTop (nhds L) :=
    hU.comp (tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop)
  exact tendsto_intervalMean_of_bounded_tendsto _ hMeas.stronglyMeasurable
    (fun t => hC _ (Set.mem_range_self (Nat.floor (Real.exp t)))) hLim

/-- Logarithmic floor-exponential sampling has a vanishing time displacement. -/
theorem tendsto_log_nat_floor_exp_sub_self :
    Tendsto (fun t : Real => Real.log (Nat.floor (Real.exp t) : Real)-t)
      atTop (nhds (0 : Real)) := by
  have hRatio := tendsto_nat_floor_div_atTop.comp Real.tendsto_exp_atTop
  have hLog := (Real.continuousAt_log (by norm_num : Not ((1 : Real)=0))).tendsto.comp hRatio
  simp only [Real.log_one] at hLog
  apply hLog.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with t ht
  have hFloor : 0 < (Nat.floor (Real.exp t) : Real) := by
    exact_mod_cast (Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr ht.le))
  dsimp only [Function.comp_def]
  rw [Real.log_div hFloor.ne' (Real.exp_pos t).ne', Real.log_exp]

/-- An arbitrary sequence sampled at floor(exp t) is integrable on every
finite interval: only a finite prefix of the sequence occurs there. -/
theorem intervalIntegrable_nat_floor_exp (u : Nat -> Complex) (a b : Real) :
    IntervalIntegrable (fun t : Real => u (Nat.floor (Real.exp t))) volume a b := by
  let K := Nat.floor (Real.exp (max a b))
  let B : Real := Finset.sum (Finset.range (K+1)) (fun n => norm (u n))
  have hB : 0 <= B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hMeas : Measurable (fun t : Real => u (Nat.floor (Real.exp t))) :=
    (measurable_of_countable u).comp (Nat.measurable_floor.comp Real.measurable_exp)
  have hConst : IntervalIntegrable (fun _t : Real => B) volume a b := intervalIntegrable_const
  apply hConst.mono_fun hMeas.stronglyMeasurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have htMax : t <= max a b := ht.2
  have hLe : Nat.floor (Real.exp t) <= K := Nat.floor_mono (Real.exp_le_exp.mpr htMax)
  have hMem : Membership.mem (Finset.range (K+1)) (Nat.floor (Real.exp t)) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hLe)
  rw [Real.norm_eq_abs, abs_of_nonneg hB]
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) hMem

/-- Exact subtraction for sampled sequence means, with all needed local
integrability derived for the arbitrary sequences. -/
theorem intervalMean_nat_floor_exp_sub (u v : Nat -> Complex) (T : Real) :
    intervalMean (fun t : Real => u (Nat.floor (Real.exp t))-v (Nat.floor (Real.exp t))) T =
      intervalMean (fun t : Real => u (Nat.floor (Real.exp t))) T -
        intervalMean (fun t : Real => v (Nat.floor (Real.exp t))) T := by
  unfold intervalMean
  rw [intervalIntegral.integral_sub (intervalIntegrable_nat_floor_exp u 0 T)
    (intervalIntegrable_nat_floor_exp v 0 T), mul_sub]

end

end Complex
