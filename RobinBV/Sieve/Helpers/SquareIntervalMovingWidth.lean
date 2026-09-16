/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Moving-width fourth-moment transport for square intervals

The exact logarithmic square width is retained under the map x*exp(v*L(x)).
Its positive Jacobian and image bounds give a factor-three integral transfer,
including finite complex exponential packets with arbitrary coefficients.
No zero-density or additive-energy estimate is assumed or proved here.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

noncomputable def movingSquareLogWidth (x : Real) : Real :=
  2*Real.log (1+Inv.inv (Real.sqrt x))

noncomputable def movingSquareMap (v x : Real) : Real :=
  x*Real.exp (v*movingSquareLogWidth x)

noncomputable def movingSquareJacobian (v x : Real) : Real :=
  Real.exp (v*movingSquareLogWidth x)*(1-v/(Real.sqrt x+1))

theorem movingSquareLogWidth_hasDerivAt {x : Real} (hx : 0 < x) :
    HasDerivAt movingSquareLogWidth (-1/(x*(Real.sqrt x+1))) x := by
  let r : Real := Real.sqrt x
  have hr : 0 < r := Real.sqrt_pos.mpr hx
  have hr2 : r^2 = x := Real.sq_sqrt hx.le
  have hs := Real.hasDerivAt_sqrt hx.ne'
  have hi := hs.inv hr.ne'
  have harg : Not (1+Inv.inv (Real.sqrt x) = 0) :=
    ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num : (0 : Real) < 1)
      (inv_nonneg.mpr (Real.sqrt_nonneg x)))
  have hlog : HasDerivAt (fun y : Real => Real.log (1+Inv.inv (Real.sqrt y)))
      ((-(1/(2*r))/r^2)/(1+Inv.inv r)) x := by
    simpa only [Pi.add_apply, Pi.inv_apply, zero_add] using
      ((hasDerivAt_const x 1).add hi).log harg
  have h := HasDerivAt.const_mul 2 hlog
  have hD : 2*((-(1/(2*r))/r^2)/(1+Inv.inv r)) = -1/(x*(r+1)) := by
    rw [<- hr2]
    field_simp [hr.ne']
  rw [hD] at h
  exact h

theorem movingSquareMap_hasDerivAt (v : Real) {x : Real} (hx : 0 < x) :
    HasDerivAt (movingSquareMap v) (movingSquareJacobian v x) x := by
  have he := (HasDerivAt.const_mul v (movingSquareLogWidth_hasDerivAt hx)).exp
  have h := (hasDerivAt_id x).mul he
  have hp : Not (Real.sqrt x+1 = 0) :=
    ne_of_gt (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg x) (by norm_num))
  have hD :
      1*Real.exp (v*movingSquareLogWidth x) +
        x*(Real.exp (v*movingSquareLogWidth x)*(v*(-1/(x*(Real.sqrt x+1))))) =
      movingSquareJacobian v x := by
    dsimp [movingSquareJacobian]
    field_simp [hx.ne', hp]
    ring
  simp only [id_eq] at h
  rw [hD] at h
  exact h

theorem movingSquareLogWidth_nonneg (x : Real) : 0 <= movingSquareLogWidth x := by
  apply mul_nonneg (by norm_num : (0 : Real) <= 2)
  apply Real.log_nonneg
  have h := inv_nonneg.mpr (Real.sqrt_nonneg x)
  linarith

theorem exp_movingSquareLogWidth (x : Real) :
    Real.exp (movingSquareLogWidth x) = (1+Inv.inv (Real.sqrt x))^2 := by
  have hp : 0 < 1+Inv.inv (Real.sqrt x) :=
    add_pos_of_pos_of_nonneg (by norm_num) (inv_nonneg.mpr (Real.sqrt_nonneg x))
  unfold movingSquareLogWidth
  rw [show 2*Real.log (1+Inv.inv (Real.sqrt x)) =
    Real.log (1+Inv.inv (Real.sqrt x))+Real.log (1+Inv.inv (Real.sqrt x)) by ring,
    Real.exp_add, Real.exp_log hp]
  ring

theorem exp_movingSquareLogWidth_le {x : Real} (hx : 16 <= x) :
    Real.exp (movingSquareLogWidth x) <= 25/16 := by
  have hx0 : 0 <= x := by linarith
  have hr0 := Real.sqrt_nonneg x
  have hr2 := Real.sq_sqrt hx0
  have hr4 : 4 <= Real.sqrt x := by nlinarith
  have hrec := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 4) hr4
  have hrec' : Inv.inv (Real.sqrt x) <= 1/4 := by simpa only [one_div] using hrec
  have hrec0 := inv_nonneg.mpr hr0
  rw [exp_movingSquareLogWidth]
  nlinarith

theorem movingSquareMap_exp_bounds {x v : Real} (hx : 16 <= x)
    (hv0 : -1 <= v) (hv2 : v <= 2) :
    16/25 <= Real.exp (v*movingSquareLogWidth x) /\
      Real.exp (v*movingSquareLogWidth x) <= (25/16 : Real)^2 := by
  have hL0 := movingSquareLogWidth_nonneg x
  have hE := exp_movingSquareLogWidth_le hx
  have hE0 := Real.exp_pos (movingSquareLogWidth x)
  have hlow : 16/25 <= Real.exp (-movingSquareLogWidth x) := by
    calc
      _ = 1/(25/16 : Real) := by norm_num
      _ <= 1/Real.exp (movingSquareLogWidth x) :=
        one_div_le_one_div_of_le hE0 hE
      _ = _ := by rw [Real.exp_neg, one_div]
  have hvlow := mul_le_mul_of_nonneg_right hv0 hL0
  have hvhigh := mul_le_mul_of_nonneg_right hv2 hL0
  refine And.intro (hlow.trans (Real.exp_le_exp.mpr (by simpa using hvlow))) ?_
  have hhigh := Real.exp_le_exp.mpr hvhigh
  rw [show 2*movingSquareLogWidth x =
    movingSquareLogWidth x+movingSquareLogWidth x by ring, Real.exp_add] at hhigh
  calc
    _ <= Real.exp (movingSquareLogWidth x)*Real.exp (movingSquareLogWidth x) := hhigh
    _ <= (25/16 : Real)*(25/16) :=
      mul_le_mul hE hE hE0.le (by norm_num)
    _ = _ := by ring

theorem movingSquareJacobian_lower {x v : Real} (hx : 16 <= x)
    (hv0 : -1 <= v) (hv2 : v <= 2) :
    48/125 <= movingSquareJacobian v x := by
  have hr0 := Real.sqrt_nonneg x
  have hr2 := Real.sq_sqrt (show 0 <= x by linarith)
  have hr4 : 4 <= Real.sqrt x := by nlinarith
  have hd0 : 0 < Real.sqrt x+1 := by linarith
  have hfrac1 := div_le_div_of_nonneg_right hv2 hd0.le
  have hfrac2 := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 2)
    (by norm_num : (0 : Real) < 5) (show 5 <= Real.sqrt x+1 by linarith)
  have hf : 3/5 <= 1-v/(Real.sqrt x+1) := by
    have h := hfrac1.trans hfrac2
    linarith
  have he := (movingSquareMap_exp_bounds hx hv0 hv2).1
  unfold movingSquareJacobian
  calc
    _ = (16/25 : Real)*(3/5) := by norm_num
    _ <= _ := mul_le_mul he hf (by norm_num) (Real.exp_pos _).le

theorem movingSquareMap_image_bounds {X x v : Real} (hX : 16 <= X)
    (hx1 : X <= x) (hx2 : x <= 2*X) (hv0 : -1 <= v) (hv2 : v <= 2) :
    X/2 <= movingSquareMap v x /\ movingSquareMap v x <= 8*X := by
  have hx16 : 16 <= x := hX.trans hx1
  have hx0 : 0 <= x := by linarith
  have hX0 : 0 <= X := by linarith
  have he := movingSquareMap_exp_bounds hx16 hv0 hv2
  unfold movingSquareMap
  apply And.intro
  next =>
    calc
      _ <= X*(16/25 : Real) := by nlinarith
      _ <= _ := mul_le_mul hx1 he.1 (by norm_num) hx0
  next =>
    calc
      _ <= (2*X)*(25/16 : Real)^2 :=
        mul_le_mul hx2 he.2 (Real.exp_pos _).le (by linarith)
      _ <= _ := by nlinarith


theorem integral_fourth_comp_movingSquareMap_le {X v : Real}
    (hX : 16 <= X) (hv0 : -1 <= v) (hv2 : v <= 2)
    {F : Real -> Complex} (hF : ContinuousOn F (Set.Icc (X/2) (8*X))) :
    intervalIntegral (fun x => norm (F (movingSquareMap v x))^4)
        X (2*X) MeasureTheory.volume <=
      3*intervalIntegral (fun y => norm (F y)^4)
        (X/2) (8*X) MeasureTheory.volume := by
  let g : Real -> Real := fun y => norm (F y)^4
  have hX2 : X <= 2*X := by linarith
  have hlarge : X/2 <= 8*X := by linarith
  have hder : forall x, (Set.Icc X (2*X)) x ->
      HasDerivAt (movingSquareMap v) (movingSquareJacobian v x) x := by
    intro x hx
    exact movingSquareMap_hasDerivAt v (by linarith [hx.1])
  have hnonneg : forall x, (Set.Icc X (2*X)) x ->
      0 <= movingSquareJacobian v x := by
    intro x hx
    have h := movingSquareJacobian_lower (hX.trans hx.1) hv0 hv2
    linarith
  have hcont : ContinuousOn (movingSquareMap v) (Set.Icc X (2*X)) :=
    fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (movingSquareMap v) (Set.Icc X (2*X)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc X (2*X)) hcont
    next =>
      intro x hx
      rw [interior_Icc] at hx
      exact (hder x (Set.mem_Icc_of_Ioo hx)).differentiableAt.differentiableWithinAt
    next =>
      intro x hx
      rw [interior_Icc] at hx
      rw [(hder x (Set.mem_Icc_of_Ioo hx)).deriv]
      exact hnonneg x (Set.mem_Icc_of_Ioo hx)
  have horder : movingSquareMap v X <= movingSquareMap v (2*X) :=
    hmono (And.intro le_rfl hX2) (And.intro hX2 le_rfl) hX2
  have hleft := movingSquareMap_image_bounds hX le_rfl hX2 hv0 hv2
  have hright := movingSquareMap_image_bounds hX hX2 le_rfl hv0 hv2
  have hmaps : Set.MapsTo (movingSquareMap v) (Set.Icc X (2*X))
      (Set.Icc (X/2) (8*X)) :=
    fun x hx => movingSquareMap_image_bounds hX hx.1 hx.2 hv0 hv2
  have hgc : ContinuousOn g (Set.Icc (X/2) (8*X)) := hF.norm.pow 4
  have hg0 : forall y, 0 <= g y := fun y => pow_nonneg (norm_nonneg (F y)) 4
  have hgi : IntervalIntegrable g MeasureTheory.volume (X/2) (8*X) := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hlarge]
  have hge : IntervalIntegrable g MeasureTheory.volume
      (movingSquareMap v X) (movingSquareMap v (2*X)) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le horder]
    exact hgc.mono (Set.Icc_subset_Icc hleft.1 hright.2)
  have hcomp : IntervalIntegrable (fun x => g (movingSquareMap v x))
      MeasureTheory.volume X (2*X) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hX2]
    exact hgc.comp hcont hmaps
  have hcontU : ContinuousOn (movingSquareMap v) (Set.uIcc X (2*X)) := by
    rwa [Set.uIcc_of_le hX2]
  have hderO : forall x, (Set.Ioo (min X (2*X)) (max X (2*X))) x ->
      HasDerivAt (movingSquareMap v) (movingSquareJacobian v x) x := by
    intro x hx
    rw [min_eq_left hX2, max_eq_right hX2] at hx
    exact hder x (Set.mem_Icc_of_Ioo hx)
  have hnO : forall x, (Set.Ioo (min X (2*X)) (max X (2*X))) x ->
      0 <= movingSquareJacobian v x := by
    intro x hx
    rw [min_eq_left hX2, max_eq_right hX2] at hx
    exact hnonneg x (Set.mem_Icc_of_Ioo hx)
  have hjint := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    hcontU hderO hnO).mpr hge
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := g) hcontU hderO hnO
  have hcompare : intervalIntegral (fun x => g (movingSquareMap v x))
      X (2*X) MeasureTheory.volume <=
      intervalIntegral (fun x => 3*(g (movingSquareMap v x)*movingSquareJacobian v x))
        X (2*X) MeasureTheory.volume := by
    apply intervalIntegral.integral_mono_on hX2 hcomp (hjint.const_mul 3)
    intro x hx
    have hJ := movingSquareJacobian_lower (hX.trans hx.1) hv0 hv2
    have hprod := mul_le_mul_of_nonneg_left
      (show (1 : Real) <= 3*movingSquareJacobian v x by linarith)
      (hg0 (movingSquareMap v x))
    simpa only [Function.comp_apply, mul_one, mul_left_comm] using hprod
  have hrange := intervalIntegral.integral_mono_interval hleft.1 horder hright.2
    (MeasureTheory.ae_restrict_of_ae (Filter.Eventually.of_forall hg0)) hgi
  calc
    _ <= intervalIntegral
        (fun x => 3*(g (movingSquareMap v x)*movingSquareJacobian v x))
        X (2*X) MeasureTheory.volume := hcompare
    _ = 3*intervalIntegral g
        (movingSquareMap v X) (movingSquareMap v (2*X)) MeasureTheory.volume := by
      rw [intervalIntegral.integral_const_mul]
      exact congrArg (fun t : Real => 3*t) hsubst
    _ <= _ := mul_le_mul_of_nonneg_left hrange (by norm_num)


theorem integral_fourth_finite_packet_movingSquareMap_le
    {I : Type*} (A : Finset I) (rho coefficient : I -> Complex)
    {X v : Real} (hX : 16 <= X) (hv0 : -1 <= v) (hv2 : v <= 2) :
    intervalIntegral
        (fun x => norm (Finset.sum A (fun i =>
          coefficient i*Complex.exp (rho i*(Real.log (movingSquareMap v x) : Complex))))^4)
        X (2*X) MeasureTheory.volume <=
      3*intervalIntegral
        (fun y => norm (Finset.sum A (fun i =>
          coefficient i*Complex.exp (rho i*(Real.log y : Complex))))^4)
        (X/2) (8*X) MeasureTheory.volume := by
  apply integral_fourth_comp_movingSquareMap_le hX hv0 hv2
    (F := fun y => Finset.sum A (fun i =>
      coefficient i*Complex.exp (rho i*(Real.log y : Complex))))
  have hlog : ContinuousOn Real.log (Set.Icc (X/2) (8*X)) := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    exact (Real.hasDerivAt_log hy0.ne').continuousAt.continuousWithinAt
  apply continuousOn_finsetSum A
  intro i hi
  apply continuousOn_const.mul
  apply Complex.continuous_exp.comp_continuousOn
  apply continuousOn_const.mul
  exact Complex.continuous_ofReal.comp_continuousOn hlog

theorem movingSquareLogWidth_dyadic_bounds {X x : Real}
    (hX : 16 <= X) (hx1 : X <= x) (hx2 : x <= 2*X) :
    1/Real.sqrt X <= movingSquareLogWidth x /\
      movingSquareLogWidth x <= 2/Real.sqrt X := by
  have hX0 : 0 < X := by linarith
  have hx0 : 0 < x := hX0.trans_le hx1
  have hr0 := Real.sqrt_pos.mpr hx0
  have hb0 := Real.sqrt_pos.mpr hX0
  have hb2 := Real.sq_sqrt hX0.le
  have hb4 : 4 <= Real.sqrt X := by nlinarith
  have hrange : Real.sqrt x+1 <= 2*Real.sqrt X := by
    have hs : Real.sqrt x <= 2*Real.sqrt X-1 := by
      apply (Real.sqrt_le_left (by linarith : 0 <= 2*Real.sqrt X-1)).mpr
      nlinarith [sq_nonneg (Real.sqrt X-2)]
    linarith
  have hden0 : 0 < Real.sqrt x+1 := by linarith
  have harg0 : 0 < 1+Inv.inv (Real.sqrt x) :=
    add_pos_of_pos_of_nonneg (by norm_num) (inv_nonneg.mpr hr0.le)
  have halg : 1-Inv.inv (1+Inv.inv (Real.sqrt x)) = 1/(Real.sqrt x+1) := by
    field_simp [hr0.ne', hden0.ne']
    ring
  have hlogLower := Real.one_sub_inv_le_log_of_pos harg0
  rw [halg] at hlogLower
  have hlogUpper := Real.log_le_sub_one_of_pos harg0
  have hinv := one_div_le_one_div_of_le hden0 hrange
  have hinvUpper := one_div_le_one_div_of_le hb0 (Real.sqrt_le_sqrt hx1)
  unfold movingSquareLogWidth
  apply And.intro
  next =>
    calc
      _ = 2*(1/(2*Real.sqrt X)) := by field_simp
      _ <= 2*(1/(Real.sqrt x+1)) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ <= _ := mul_le_mul_of_nonneg_left hlogLower (by norm_num)
  next =>
    have hu : Real.log (1+Inv.inv (Real.sqrt x)) <= 1/Real.sqrt x := by
      simpa only [add_sub_cancel_left, one_div] using hlogUpper
    calc
      _ <= 2*(1/Real.sqrt x) := mul_le_mul_of_nonneg_left hu (by norm_num)
      _ <= 2*(1/Real.sqrt X) :=
        mul_le_mul_of_nonneg_left hinvUpper (by norm_num)
      _ = _ := by ring

theorem movingSquareLogWidth_pos {x : Real} (hx : 0 < x) :
    0 < movingSquareLogWidth x := by
  unfold movingSquareLogWidth
  apply mul_pos (by norm_num : (0 : Real) < 2)
  apply Real.log_pos
  have hi := inv_pos.mpr (Real.sqrt_pos.mpr hx)
  linarith

theorem log_movingSquareMap {x : Real} (hx : 0 < x) (v : Real) :
    Real.log (movingSquareMap v x) = Real.log x+v*movingSquareLogWidth x := by
  unfold movingSquareMap
  rw [Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]

end RobinBV.Sieve
