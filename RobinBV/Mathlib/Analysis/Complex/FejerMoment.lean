/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.FejerCount

/-!
# First moments from finite phase counts

Integrating a finite tail count recovers the exact first moment, with no
sampling or discretization. Two-sided finite circle-count estimates therefore
give two-sided moment bounds with all localization costs and positive
normalization conditions retained. Paired arithmetic applications can cancel
the common first-moment main terms before bounding the remaining error.
-/

set_option autoImplicit false

namespace Complex

theorem intervalIntegrable_tail_indicator (x a b : Real) :
    IntervalIntegrable ((Set.Iic x).indicator (fun _ : Real => (1 : Real)))
      MeasureTheory.volume a b := by
  have hc : IntervalIntegrable (fun _ : Real => (1 : Real)) MeasureTheory.volume a b :=
    intervalIntegrable_const
  exact And.intro (hc.1.indicator measurableSet_Iic) (hc.2.indicator measurableSet_Iic)

theorem integral_tail_indicator (T x : Real) (hx : 0 <= x) (hxT : x <= T) :
    intervalIntegral ((Set.Iic x).indicator (fun _ : Real => (1 : Real)))
      0 T MeasureTheory.volume = x := by
  calc
    _ = intervalIntegral (fun _ : Real => (1 : Real)) 0 x MeasureTheory.volume :=
      intervalIntegral.integral_indicator (And.intro hx hxT)
    _ = x := by simp [intervalIntegral.integral_const]

theorem finite_tail_count_integral {v : Type*} (s : Finset v) (x : v -> Real) (T : Real)
    (hx : forall i, Membership.mem s i -> 0 <= x i /\ x i <= T) :
    intervalIntegral (fun t : Real =>
      ((s.filter (fun i => t <= x i /\ x i <= T)).card : Real))
      0 T MeasureTheory.volume = s.sum x := by
  classical
  have he (t : Real) : ((s.filter (fun i => t <= x i /\ x i <= T)).card : Real) =
      s.sum (fun i => (Set.Iic (x i)).indicator (fun _ : Real => (1 : Real)) t) := by
    calc
      _ = (s.filter (fun i => t <= x i /\ x i <= T)).sum (fun _ => (1 : Real)) := by simp
      _ = s.sum (fun i => if t <= x i /\ x i <= T then (1 : Real) else 0) := by
        rw [Finset.sum_filter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Set.indicator_apply, (hx i hi).2]
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun i hi => intervalIntegrable_tail_indicator (x i) 0 T)]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_tail_indicator T (x i) (hx i hi).1 (hx i hi).2

theorem intervalIntegrable_finite_tail_count {v : Type*} (s : Finset v) (x : v -> Real)
    (T a b : Real) (hxT : forall i, Membership.mem s i -> x i <= T) :
    IntervalIntegrable (fun t : Real =>
      ((s.filter (fun i => t <= x i /\ x i <= T)).card : Real))
      MeasureTheory.volume a b := by
  classical
  have he : (fun t : Real => ((s.filter (fun i => t <= x i /\ x i <= T)).card : Real)) =
      (fun t => s.sum (fun i => (Set.Iic (x i)).indicator (fun _ : Real => (1 : Real)) t)) := by
    funext t
    calc
      _ = (s.filter (fun i => t <= x i /\ x i <= T)).sum (fun _ => (1 : Real)) := by simp
      _ = s.sum (fun i => if t <= x i /\ x i <= T then (1 : Real) else 0) := by
        rw [Finset.sum_filter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Set.indicator_apply, hxT i hi]
  rw [he]
  exact And.intro
    (MeasureTheory.integrable_finsetSum s (fun i hi => (intervalIntegrable_tail_indicator (x i) a b).1))
    (MeasureTheory.integrable_finsetSum s (fun i hi => (intervalIntegrable_tail_indicator (x i) a b).2))

theorem integral_affine_from_zero (T a b : Real) :
    intervalIntegral (fun t : Real => a+b*t) 0 T MeasureTheory.volume =
      a*T+b*T^2/2 := by
  have hi : IntervalIntegrable (fun t : Real => b*t) MeasureTheory.volume 0 T :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  simp only [sub_zero, zero_pow (by decide : Not (2=0)), smul_eq_mul]
  ring

theorem finite_phase_moment_bounds {v : Type*} (s : Finset v) (x : v -> Real)
    (H : Nat) (hH : 1 <= H) (E d : Real)
    (hd : 0 < d) (hdp : d <= Real.pi) (hgap : Real.pi < ((H : Real)+1)*d)
    (hx : forall i, Membership.mem s i -> 0 <= x i /\ x i <= 2*Real.pi)
    (hE : forall j, j < H -> forall k, k < H -> Not (j=k) ->
      norm (s.sum (fun i => exp (I*(((j : Int)-k : Int) : Complex)*(x i : Complex)))) <= E) :
    let A : Real := 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi))
    let B : Real := (s.card : Real)+((H : Real)-1)*E
    (s.card : Real)-(Real.pi+4*d)*B/A <= s.sum x/(2*Real.pi) /\
      s.sum x/(2*Real.pi) <= (Real.pi+2*d)*B/A := by
  classical
  let A : Real := 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi))
  let B : Real := (s.card : Real)+((H : Real)-1)*E
  let C : Real -> Real := fun t => ((s.filter (fun i => t <= x i /\ x i <= 2*Real.pi)).card : Real)
  have hA : 0 < A := finiteFejer_mass_factor_pos H hH d hd hgap
  have hC : IntervalIntegrable C MeasureTheory.volume 0 (2*Real.pi) :=
    intervalIntegrable_finite_tail_count s x (2*Real.pi) 0 (2*Real.pi) (fun i hi => (hx i hi).2)
  have hL : IntervalIntegrable (fun t : Real => (s.card : Real)-(t+4*d)*B/A)
      MeasureTheory.volume 0 (2*Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hU : IntervalIntegrable (fun t : Real => (2*Real.pi-t+2*d)*B/A)
      MeasureTheory.volume 0 (2*Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hlow : forall t, Membership.mem (Set.Icc 0 (2*Real.pi)) t ->
      (s.card : Real)-(t+4*d)*B/A <= C t := by
    intro t ht
    have hl := finiteFejer_arc_count_lower s x H hH E t (2*Real.pi) d
      ht.1 ht.2 le_rfl hd hdp hgap hx hE
    rw [show 2*Real.pi-(2*Real.pi-t)=t by ring] at hl
    change A*(s.card : Real)-(t+4*d)*B <= A*C t at hl
    calc
      _ = (A*(s.card : Real)-(t+4*d)*B)/A := by field_simp [ne_of_gt hA]
      _ <= (A*C t)/A := div_le_div_of_nonneg_right hl hA.le
      _ = C t := by field_simp [ne_of_gt hA]
  have hupp : forall t, Membership.mem (Set.Icc 0 (2*Real.pi)) t ->
      C t <= (2*Real.pi-t+2*d)*B/A := by
    intro t ht
    exact finiteFejer_arc_count_div_upper s x H hH E t (2*Real.pi) d
      ht.2 hd hdp hgap hE
  have hl := intervalIntegral.integral_mono_on (show 0 <= 2*Real.pi by positivity) hL hC hlow
  have hu := intervalIntegral.integral_mono_on (show 0 <= 2*Real.pi by positivity) hC hU hupp
  have hm : intervalIntegral C 0 (2*Real.pi) MeasureTheory.volume = s.sum x :=
    finite_tail_count_integral s x (2*Real.pi) hx
  rw [hm] at hl hu
  have hli : intervalIntegral (fun t : Real => (s.card : Real)-(t+4*d)*B/A)
      0 (2*Real.pi) MeasureTheory.volume =
        2*Real.pi*((s.card : Real)-(Real.pi+4*d)*B/A) := by
    have he : (fun t : Real => (s.card : Real)-(t+4*d)*B/A) =
        (fun t : Real => ((s.card : Real)-4*d*B/A)+(-B/A)*t) := by funext t; ring
    rw [he, integral_affine_from_zero]
    ring
  have hui : intervalIntegral (fun t : Real => (2*Real.pi-t+2*d)*B/A)
      0 (2*Real.pi) MeasureTheory.volume =
        2*Real.pi*((Real.pi+2*d)*B/A) := by
    have he : (fun t : Real => (2*Real.pi-t+2*d)*B/A) =
        (fun t : Real => ((2*Real.pi+2*d)*B/A)+(-B/A)*t) := by funext t; ring
    rw [he, integral_affine_from_zero]
    ring
  rw [hli] at hl
  rw [hui] at hu
  change (s.card : Real)-(Real.pi+4*d)*B/A <= s.sum x/(2*Real.pi) /\
    s.sum x/(2*Real.pi) <= (Real.pi+2*d)*B/A
  apply And.intro
  next =>
    calc
      _ = (2*Real.pi*((s.card : Real)-(Real.pi+4*d)*B/A))/(2*Real.pi) := by
        field_simp [ne_of_gt Real.pi_pos]
      _ <= _ := div_le_div_of_nonneg_right hl (show 0 <= 2*Real.pi by positivity)
  next =>
    calc
      _ <= (2*Real.pi*((Real.pi+2*d)*B/A))/(2*Real.pi) :=
        div_le_div_of_nonneg_right hu (show 0 <= 2*Real.pi by positivity)
      _ = _ := by field_simp [ne_of_gt Real.pi_pos]

end Complex
