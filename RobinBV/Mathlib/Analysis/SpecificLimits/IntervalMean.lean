/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
/-
# Interval mean limits

This module contains interval-average limit estimates for locally integrable
functions and their floor-based discretizations.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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

/-- Complex conjugation commutes with the actual interval mean. -/
theorem intervalMean_star (f : Real -> Complex) (T : Real) :
    intervalMean (fun t => star (f t)) T = star (intervalMean f T) := by
  have hInt : intervalIntegral (fun t => star (f t)) 0 T volume =
      star (intervalIntegral f 0 T volume) :=
    Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm f
  unfold intervalMean
  rw [hInt]
  simp

/-- The mean of a constant is exact at every nonzero averaging length. -/
theorem intervalMean_const (z : Complex) {T : Real} (hT : Not (T=0)) :
    intervalMean (fun _ => z) T = z := by
  have hTC := Complex.ofReal_ne_zero.mpr hT
  simp [intervalMean, intervalIntegral.integral_const, Complex.real_smul, hTC]

/-- Exact addition of arbitrary logarithmically sampled sequence means. -/
theorem intervalMean_nat_floor_exp_add (u v : Nat -> Complex) (T : Real) :
    intervalMean (fun t : Real => u (Nat.floor (Real.exp t))+v (Nat.floor (Real.exp t))) T =
      intervalMean (fun t : Real => u (Nat.floor (Real.exp t))) T +
        intervalMean (fun t : Real => v (Nat.floor (Real.exp t))) T := by
  unfold intervalMean
  rw [intervalIntegral.integral_add (intervalIntegrable_nat_floor_exp u 0 T)
    (intervalIntegrable_nat_floor_exp v 0 T), mul_add]

/-- Exact centering of the second moment for an arbitrary sampled sequence.
All required local integrability is derived from the finite sampled range. -/
theorem intervalMean_nat_floor_exp_centered_square_eq
    (u : Nat -> Complex) (z : Complex) {T : Real} (hT : Not (T=0)) :
    intervalMean (fun t : Real =>
      (u (Nat.floor (Real.exp t))-z)*star (u (Nat.floor (Real.exp t))-z)) T =
      intervalMean (fun t : Real => u (Nat.floor (Real.exp t))*star (u (Nat.floor (Real.exp t)))) T -
        intervalMean (fun t : Real => u (Nat.floor (Real.exp t))) T * star z -
        z * star (intervalMean (fun t : Real => u (Nat.floor (Real.exp t))) T) + z*star z := by
  have hPoint : (fun t : Real =>
      (u (Nat.floor (Real.exp t))-z)*star (u (Nat.floor (Real.exp t))-z)) =
      (fun t : Real => (u (Nat.floor (Real.exp t))*star (u (Nat.floor (Real.exp t))) -
        u (Nat.floor (Real.exp t))*star z) - z*star (u (Nat.floor (Real.exp t))) + z*star z) := by
    funext t
    simp only [star_sub]
    ring
  have hRight : intervalMean (fun t : Real => u (Nat.floor (Real.exp t))*star z) T =
      intervalMean (fun t : Real => u (Nat.floor (Real.exp t))) T * star z := by
    unfold intervalMean
    rw [intervalIntegral.integral_mul_const]
    ring
  have hLeft : intervalMean (fun t : Real => z*star (u (Nat.floor (Real.exp t)))) T =
      z*star (intervalMean (fun t : Real => u (Nat.floor (Real.exp t))) T) := by
    rw [<- intervalMean_star]
    unfold intervalMean
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [hPoint,
    intervalMean_nat_floor_exp_add
      (fun n => (u n*star (u n)-u n*star z)-z*star (u n)) (fun _ => z*star z),
    intervalMean_nat_floor_exp_sub
      (fun n => u n*star (u n)-u n*star z) (fun n => z*star (u n)),
    intervalMean_nat_floor_exp_sub (fun n => u n*star (u n)) (fun n => u n*star z),
    hRight, hLeft, intervalMean_const (z*star z) hT]

/-- Actual mean and second-moment limits give the exact centered variance. -/
theorem tendsto_intervalMean_nat_floor_exp_variance
    (u : Nat -> Complex) (z s : Complex)
    (hMean : Tendsto (intervalMean (fun t : Real => u (Nat.floor (Real.exp t)))) atTop (nhds z))
    (hSecond : Tendsto (intervalMean (fun t : Real =>
      u (Nat.floor (Real.exp t))*star (u (Nat.floor (Real.exp t))))) atTop (nhds s)) :
    Tendsto (intervalMean (fun t : Real =>
      (u (Nat.floor (Real.exp t))-z)*star (u (Nat.floor (Real.exp t))-z)))
      atTop (nhds (s-z*star z)) := by
  have h := ((hSecond.sub (hMean.mul_const (star z))).sub
    (hMean.star.const_mul z)).add_const (z*star z)
  have hConstant : s-z*star z-z*star z+z*star z=s-z*star z := by ring
  rw [hConstant] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with T hT
  exact (intervalMean_nat_floor_exp_centered_square_eq u z hT.ne').symm

/-- The actual squared-norm mean has nonnegative real part. -/
theorem intervalMean_mul_star_self_re_nonneg (f : Real -> Complex)
    {T : Real} (hT : 0 <= T) :
    0 <= (intervalMean (fun t => f t*star (f t)) T).re := by
  unfold intervalMean
  simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    intervalIntegral.integral_ofReal]
  rw [<- Complex.ofReal_inv, <- Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (inv_nonneg.mpr hT)
    (intervalIntegral.integral_nonneg_of_forall hT (fun t => sq_nonneg (norm (f t))))

/-- Any actual squared-norm interval-mean limit has nonnegative real part. -/
theorem re_nonneg_of_tendsto_intervalMean_mul_star_self (f : Real -> Complex) {s : Complex}
    (h : Tendsto (intervalMean (fun t => f t*star (f t))) atTop (nhds s)) :
    0 <= s.re := by
  apply ge_of_tendsto ((Complex.continuous_re.tendsto s).comp h)
  filter_upwards [Filter.eventually_ge_atTop (0 : Real)] with T hT
  exact intervalMean_mul_star_self_re_nonneg f hT

/-- A uniform norm bound passes to every positive-length interval mean.
The proof is the complete integral triangle bound divided by its length. -/
theorem norm_intervalMean_le (f : Real -> Complex) {C : Real}
    (hBound : forall t, norm (f t) <= C) {T : Real} (hT : 0 < T) :
    norm (intervalMean f T) <= C := by
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : Real)) (b := T) (C := C) (fun t _ => hBound t)
  unfold intervalMean
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  apply (mul_le_mul_of_nonneg_left hIntegral (inv_pos.mpr hT).le).trans_eq
  simp [abs_of_pos hT, hT.ne', mul_comm]

/-- An eventual norm bound controls the limit of actual sampled means.
Clipping removes the entire finite prefix; its full mean error tends to zero. -/
theorem norm_le_of_tendsto_intervalMean_nat_floor_exp_of_eventually_norm_le
    (u : Nat -> Complex) {s : Complex} {C : Real} (hC : 0 <= C)
    (hMean : Tendsto (intervalMean (fun t : Real => u (Nat.floor (Real.exp t)))) atTop (nhds s))
    (hBound : Filter.Eventually (fun n => norm (u n) <= C) atTop) :
    norm s <= C := by
  classical
  let v : Nat -> Complex := fun n => if norm (u n) <= C then u n else 0
  have hV (n : Nat) : norm (v n) <= C := by
    dsimp only [v]
    split_ifs with hn
    next => exact hn
    next => simpa only [norm_zero] using hC
  have hError : Tendsto (fun n => u n-v n) atTop (nhds (0 : Complex)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hBound] with n hn
    simp only [v, if_pos hn, sub_self]
  have hErrorMean := tendsto_intervalMean_nat_floor_exp (fun n => u n-v n) hError
  have hVMean : Tendsto (intervalMean (fun t : Real => v (Nat.floor (Real.exp t)))) atTop (nhds s) := by
    have h := hMean.sub hErrorMean
    simp only [sub_zero] at h
    apply h.congr'
    apply Filter.Eventually.of_forall
    intro T
    dsimp only
    rw [intervalMean_nat_floor_exp_sub u v]
    ring
  apply le_of_tendsto hVMean.norm
  filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with T hT
  exact norm_intervalMean_le (fun t : Real => v (Nat.floor (Real.exp t)))
    (fun t => hV (Nat.floor (Real.exp t))) hT

/-- A positive complete second-moment limit forces arbitrarily late norm
excursions at every smaller squared amplitude. No rate or gap is assumed. -/
theorem frequently_norm_gt_of_secondMoment_limit
    (u : Nat -> Complex) {s : Complex} (d : Real) (hd : 0 <= d)
    (hMean : Tendsto (intervalMean (fun t : Real =>
      u (Nat.floor (Real.exp t))*star (u (Nat.floor (Real.exp t))))) atTop (nhds s))
    (hSmall : d^2 < norm s) :
    Filter.Frequently (fun n : Nat => d < norm (u n)) atTop := by
  by_contra hNot
  have hBound : Filter.Eventually (fun n => norm (u n) <= d) atTop := by
    simpa only [not_lt] using Filter.not_frequently.mp hNot
  have hSquare : Filter.Eventually (fun n => norm (u n*star (u n)) <= d^2) atTop := by
    filter_upwards [hBound] with n hn
    rw [norm_mul, norm_star, pow_two]
    exact mul_le_mul hn hn (norm_nonneg _) hd
  have hLe := norm_le_of_tendsto_intervalMean_nat_floor_exp_of_eventually_norm_le
    (fun n => u n*star (u n)) (sq_nonneg d) hMean hSquare
  exact (not_le_of_gt hSmall) hLe

end

end Complex
