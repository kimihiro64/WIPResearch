/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import RobinBV.Mathlib.Analysis.Complex.InverseChord

/-!
# Finite circle kernels and explicit localization

The squared geometric exponential sum gives a nonnegative kernel with exact
mass over a period. Inverse-chord spacing controls its pointwise tail, and
integration retains the reciprocal endpoint saving. Every finite cutoff and
normalization condition is explicit. These are analytic source estimates,
not a statement about the presence of a prime in a square interval.
-/

set_option autoImplicit false

namespace Complex

noncomputable def finiteCircleSum (H : Nat) (t : Real) : Complex :=
  (Finset.range H).sum (fun j => (exp (I*(t : Complex)))^j)

noncomputable def finiteFejerKernel (H : Nat) (t : Real) : Real :=
  norm (finiteCircleSum H t)^2 / H

theorem finiteFejerKernel_nonneg (H : Nat) (t : Real) :
    0 <= finiteFejerKernel H t := by
  unfold finiteFejerKernel
  positivity

theorem norm_finiteCircleSum_le_card (H : Nat) (t : Real) :
    norm (finiteCircleSum H t) <= H := by
  have he : norm (exp (I*(t : Complex))) = 1 := by
    rw [mul_comm I, norm_exp_ofReal_mul_I]
  calc
    norm (finiteCircleSum H t) <=
        (Finset.range H).sum (fun j => norm ((exp (I*(t : Complex)))^j)) :=
      norm_sum_le _ _
    _ = H := by simp only [norm_pow, he, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]

theorem finiteCircleSum_eq_inverseChord (H : Nat) (t : Real)
    (ht : 0 < t) (htp : t <= Real.pi) :
    finiteCircleSum H t =
      ((exp (I*(t : Complex)))^H-1)*inverseChordWeight t := by
  have hi := inverseChordWeight_mul_exp_sub_one t ht htp
  have hg := geom_sum_mul (exp (I*(t : Complex))) H
  change finiteCircleSum H t * (exp (I*(t : Complex))-1) = _ at hg
  calc
    finiteCircleSum H t = finiteCircleSum H t *
        (inverseChordWeight t*(exp (I*(t : Complex))-1)) := by rw [hi, mul_one]
    _ = (finiteCircleSum H t*(exp (I*(t : Complex))-1))*inverseChordWeight t := by ring
    _ = _ := by rw [hg]

theorem norm_finiteCircleSum_le_spacing (H : Nat) (t : Real)
    (ht : 0 < t) (htp : t <= Real.pi) :
    norm (finiteCircleSum H t) <= Real.pi/t := by
  have he : norm (exp (I*(t : Complex))) = 1 := by
    rw [mul_comm I, norm_exp_ofReal_mul_I]
  have hn : norm ((exp (I*(t : Complex)))^H-1) <= 2 := by
    calc
      norm ((exp (I*(t : Complex)))^H-1) <=
        norm ((exp (I*(t : Complex)))^H)+norm (1 : Complex) := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, he]
  rw [finiteCircleSum_eq_inverseChord H t ht htp, norm_mul]
  calc
    norm ((exp (I*(t : Complex)))^H-1)*norm (inverseChordWeight t) <=
        2*(Real.pi/(2*t)) :=
      mul_le_mul hn (norm_inverseChordWeight_le t ht htp) (norm_nonneg _) (by norm_num)
    _ = Real.pi/t := by ring

theorem finiteFejerKernel_le_spacing (H : Nat) (t : Real)
    (ht : 0 < t) (htp : t <= Real.pi) :
    finiteFejerKernel H t <= Real.pi^2/((H : Real)*t^2) := by
  have hb := norm_finiteCircleSum_le_spacing H t ht htp
  have hs : norm (finiteCircleSum H t)^2 <= (Real.pi/t)^2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hb
  unfold finiteFejerKernel
  calc
    norm (finiteCircleSum H t)^2 / H <= (Real.pi/t)^2/H :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ = Real.pi^2/((H : Real)*t^2) := by ring

theorem finiteFejerKernel_le_card (H : Nat) (t : Real) :
    finiteFejerKernel H t <= H := by
  have hb := norm_finiteCircleSum_le_card H t
  have hs : norm (finiteCircleSum H t)^2 <= (H : Real)^2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hb
  unfold finiteFejerKernel
  calc
    norm (finiteCircleSum H t)^2/H <= (H : Real)^2/H :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ = H := by by_cases h : H=0 <;> simp [h, pow_two]

theorem circle_character_integral (k : Int) :
    intervalIntegral (fun t : Real => exp (I*(k : Complex)*(t : Complex)))
      0 (2*Real.pi) MeasureTheory.volume =
      if k=0 then (2*Real.pi : Complex) else 0 := by
  classical
  by_cases hk : k=0
  case pos =>
    subst k
    simp [intervalIntegral.integral_const]
  case neg =>
    have hki : Not ((k : Complex)=0) := by exact_mod_cast hk
    rw [if_neg hk, integral_exp_mul_complex (mul_ne_zero I_ne_zero hki)]
    have he : exp (I*(k : Complex)*((2*Real.pi : Real) : Complex)) = 1 := by
      convert exp_int_mul_two_pi_mul_I k using 1 <;> push_cast <;> ring
    push_cast at he
    simp [he]

theorem circle_power_cross (j k : Nat) (t : Real) :
    (exp (I*(t : Complex)))^j *
      (starRingEnd Complex) ((exp (I*(t : Complex)))^k) =
        exp (I*(((j : Int)-k : Int) : Complex)*(t : Complex)) := by
  rw [map_pow, <- exp_conj, <- exp_nat_mul, <- exp_nat_mul, <- exp_add]
  congr 1
  simp only [map_mul, conj_I, conj_ofReal, Int.cast_sub, Int.cast_natCast]
  ring

theorem finiteCircleSum_sq_eq_cross (H : Nat) (t : Real) :
    ((norm (finiteCircleSum H t)^2 : Real) : Complex) =
      (Finset.range H).sum (fun j => (Finset.range H).sum (fun k =>
        exp (I*(((j : Int)-k : Int) : Complex)*(t : Complex)))) := by
  rw [ofReal_pow, <- mul_conj']
  unfold finiteCircleSum
  rw [map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  exact circle_power_cross j k t

theorem integral_finiteCircleSum_sq (H : Nat) :
    intervalIntegral (fun t : Real => norm (finiteCircleSum H t)^2)
      0 (2*Real.pi) MeasureTheory.volume = 2*Real.pi*H := by
  classical
  apply ofReal_injective
  rw [<- intervalIntegral.integral_ofReal]
  simp_rw [finiteCircleSum_sq_eq_cross]
  have hc (j k : Nat) : Continuous (fun t : Real =>
      exp (I*(((j : Int)-k : Int) : Complex)*(t : Complex))) := by fun_prop
  rw [intervalIntegral.integral_finsetSum (fun j hj =>
    (continuous_finsetSum _ (fun k hk => hc j k)).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_finsetSum (fun k hk => (hc _ k).intervalIntegrable _ _)]
  simp_rw [circle_character_integral]
  have he (j k : Nat) : ((j : Int)-k=0) <-> j=k := by omega
  simp_rw [he]
  have hd (j : Nat) (hj : j < H) :
      (Finset.range H).sum (fun k => if j=k then (2*Real.pi : Complex) else 0) =
        (2*Real.pi : Complex) := by simp [hj]
  rw [Finset.sum_congr rfl (fun j hj => hd j (Finset.mem_range.mp hj))]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem integral_finiteFejerKernel (H : Nat) (hH : 1 <= H) :
    intervalIntegral (finiteFejerKernel H) 0 (2*Real.pi) MeasureTheory.volume =
      2*Real.pi := by
  have hp : Not ((H : Real)=0) := by exact_mod_cast (show Not (H=0) by omega)
  unfold finiteFejerKernel
  rw [intervalIntegral.integral_div, integral_finiteCircleSum_sq]
  field_simp

theorem continuous_finiteFejerKernel (H : Nat) : Continuous (finiteFejerKernel H) := by
  unfold finiteFejerKernel finiteCircleSum
  fun_prop

theorem finiteFejerKernel_neg (H : Nat) (t : Real) :
    finiteFejerKernel H (-t) = finiteFejerKernel H t := by
  have he : finiteCircleSum H (-t) = (starRingEnd Complex) (finiteCircleSum H t) := by
    unfold finiteCircleSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_pow, <- exp_conj]
    congr 2
    simp only [ofReal_neg, map_mul, conj_I, conj_ofReal]
    ring
  simp only [finiteFejerKernel, he, norm_conj]

theorem finiteFejerKernel_periodic (H : Nat) :
    Function.Periodic (finiteFejerKernel H) (2*Real.pi) := by
  intro t
  have he : exp (I*((t+2*Real.pi : Real) : Complex)) = exp (I*(t : Complex)) := by
    have hh : I*((t+2*Real.pi : Real) : Complex) = I*(t : Complex)+2*Real.pi*I := by
      push_cast
      ring
    rw [hh, exp_add, exp_two_pi_mul_I, mul_one]
  simp only [finiteFejerKernel, finiteCircleSum, he]

theorem integral_finiteFejerKernel_center (H : Nat) (hH : 1 <= H) :
    intervalIntegral (finiteFejerKernel H) (-Real.pi) Real.pi MeasureTheory.volume =
      2*Real.pi := by
  have h := (finiteFejerKernel_periodic H).intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi+2*Real.pi=Real.pi by ring, zero_add] at h
  exact h.trans (integral_finiteFejerKernel H hH)

theorem integral_inv_square_pos (a b : Real) (ha : 0 < a) (hab : a <= b) :
    intervalIntegral (fun t : Real => 1/t^2) a b MeasureTheory.volume = 1/a-1/b := by
  have hz : Not (Membership.mem (Set.uIcc a b) (0 : Real)) :=
    Set.notMem_uIcc_of_lt ha (ha.trans_le hab)
  have h := integral_zpow (a := a) (b := b) (n := (-2 : Int))
    (Or.inr (And.intro (by norm_num) hz))
  norm_num [zpow_neg, div_eq_mul_inv] at h
  simpa only [one_div, sub_neg_eq_add, neg_sub] using h

theorem integral_finiteFejerKernel_tail (H : Nat) (d : Real)
    (hd : 0 < d) (hdp : d <= Real.pi) :
    intervalIntegral (finiteFejerKernel H) d Real.pi MeasureTheory.volume <=
      Real.pi^2/(H : Real)*(1/d-1/Real.pi) := by
  have hc : ContinuousOn (fun t : Real => (Real.pi^2/(H : Real))/t^2)
      (Set.Icc d Real.pi) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
    intro t ht
    exact pow_ne_zero 2 (ne_of_gt (hd.trans_le ht.1))
  have hi : IntervalIntegrable (finiteFejerKernel H) MeasureTheory.volume d Real.pi :=
    (continuous_finiteFejerKernel H).intervalIntegrable d Real.pi
  have hm := intervalIntegral.integral_mono_on hdp hi
    (hc.intervalIntegrable_of_Icc hdp) (fun t ht => by
      calc
        finiteFejerKernel H t <= Real.pi^2/((H : Real)*t^2) :=
          finiteFejerKernel_le_spacing H t (hd.trans_le ht.1) ht.2
        _ = (Real.pi^2/(H : Real))/t^2 := by ring)
  have he : (fun t : Real => (Real.pi^2/(H : Real))/t^2) =
      (fun t : Real => (Real.pi^2/(H : Real))*(1/t^2)) := by funext t; ring
  rw [he, intervalIntegral.integral_const_mul, integral_inv_square_pos d Real.pi hd hdp] at hm
  exact hm

theorem integral_finiteFejerKernel_near (H : Nat) (hH : 1 <= H) (d : Real)
    (hd : 0 < d) (hdp : d <= Real.pi) :
    2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi)) <=
      intervalIntegral (finiteFejerKernel H) (-d) d MeasureTheory.volume := by
  have hc := continuous_finiteFejerKernel H
  have hi (a b : Real) : IntervalIntegrable (finiteFejerKernel H) MeasureTheory.volume a b :=
    hc.intervalIntegrable a b
  have hl := intervalIntegral.integral_add_adjacent_intervals
    (hi (-Real.pi) (-d)) (hi (-d) d)
  have hr := intervalIntegral.integral_add_adjacent_intervals
    (hi (-Real.pi) d) (hi d Real.pi)
  have he : intervalIntegral (finiteFejerKernel H) (-Real.pi) (-d) MeasureTheory.volume =
      intervalIntegral (finiteFejerKernel H) d Real.pi MeasureTheory.volume := by
    have hh := intervalIntegral.integral_comp_neg (finiteFejerKernel H) (a := d) (b := Real.pi)
    simp only [finiteFejerKernel_neg] at hh
    exact hh.symm
  have ht := integral_finiteFejerKernel_tail H d hd hdp
  have hm := integral_finiteFejerKernel_center H hH
  rw [he] at hl
  linarith

end Complex
