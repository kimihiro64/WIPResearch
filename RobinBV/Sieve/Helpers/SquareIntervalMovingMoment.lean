/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.GCongr
import RobinBV.Sieve.Helpers.SquareIntervalMovingWidth

/-!
# Fourth moments for smoothed moving square windows

Jensen on the unit interval, Fubini, and the moving-map Jacobian transfer
bound the complete smoothing integral. Integrability is proved separately
from the numerical inequality, including for a bounded scalar weight.
This does not estimate the fourth moment of any actual zeta-zero packet.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

noncomputable def movingSquareUnitIntegral
    (a b : Real) (psi F : Real -> Complex) (x : Real) : Complex :=
  MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
    (fun v => psi v*F (movingSquareMap (a+b*v) x))

theorem movingSquareUnitIntegral_fourth_moment
    {X a b : Real} (hX : 16 <= X)
    (hab : forall v, (Set.Icc (0 : Real) 1) v -> -1 <= a+b*v /\ a+b*v <= 2)
    {psi F : Real -> Complex}
    (hpsi : ContinuousOn psi (Set.Icc (0 : Real) 1))
    (hF : ContinuousOn F (Set.Ioi (0 : Real))) :
    MeasureTheory.IntegrableOn (fun x => norm (movingSquareUnitIntegral a b psi F x)^4)
      (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (movingSquareUnitIntegral a b psi F x)^4) <=
      3*(MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (psi v)^4)) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
          (fun y => norm (F y)^4) := by
  let mu : MeasureTheory.Measure Real := MeasureTheory.volume.restrict (Set.Icc X (2*X))
  let nu : MeasureTheory.Measure Real := MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1)
  let K : Set (Prod Real Real) := Set.prod (Set.Icc X (2*X)) (Set.Icc (0 : Real) 1)
  let q : Prod Real Real -> Complex :=
    fun p => psi p.2*F (movingSquareMap (a+b*p.2) p.1)
  let J : Real := MeasureTheory.integral
    (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X))) (fun y => norm (F y)^4)
  let : MeasureTheory.IsProbabilityMeasure nu :=
    MeasureTheory.IsProbabilityMeasure.mk (by simp [nu])
  have hX2 : X <= 2*X := by linarith
  have hY : X/2 <= 8*X := by linarith
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hqc : ContinuousOn q K := by
    have hp : ContinuousOn (fun p : Prod Real Real => psi p.2) K :=
      hpsi.comp continuous_snd.continuousOn (fun _ h => h.2)
    refine hp.mul ?_
    intro p hpK
    have hx0 : 0 < p.1 := by linarith [hpK.1.1]
    have hT0 : 0 < movingSquareMap (a+b*p.2) p.1 :=
      mul_pos hx0 (Real.exp_pos _)
    have hTc : ContinuousAt
        (fun z : Prod Real Real => movingSquareMap (a+b*z.2) z.1) p := by
      unfold movingSquareMap
      apply ContinuousAt.mul continuous_fst.continuousAt
      apply Real.continuous_exp.continuousAt.comp
      apply ContinuousAt.mul
      next =>
        exact (continuous_const.add (continuous_const.mul continuous_snd)).continuousAt
      next =>
        exact (movingSquareLogWidth_hasDerivAt hx0).continuousAt.comp
          continuous_fst.continuousAt
    have hFc : ContinuousAt F (movingSquareMap (a+b*p.2) p.1) :=
      hF.continuousAt (isOpen_Ioi.mem_nhds hT0)
    have hcomp : ContinuousAt
        (fun z : Prod Real Real => F (movingSquareMap (a+b*z.2) z.1)) p :=
      hFc.comp (f := fun z : Prod Real Real => movingSquareMap (a+b*z.2) z.1) hTc
    exact hcomp.continuousWithinAt
  have hqi : MeasureTheory.Integrable q (mu.prod nu) := by
    dsimp [mu, nu]
    rw [MeasureTheory.Measure.prod_restrict, <- MeasureTheory.Measure.volume_eq_prod]
    exact ContinuousOn.integrableOn_compact hK hqc
  have hPi : MeasureTheory.Integrable (fun p => norm (q p)^4) (mu.prod nu) := by
    dsimp [mu, nu]
    rw [MeasureTheory.Measure.prod_restrict, <- MeasureTheory.Measure.volume_eq_prod]
    exact ContinuousOn.integrableOn_compact hK (hqc.norm.pow 4)
  have hUi : MeasureTheory.Integrable
      (fun x => MeasureTheory.integral nu (fun v => q (x,v))) mu :=
    hqi.integral_prod_left
  have hGi : MeasureTheory.Integrable
      (fun x => MeasureTheory.integral nu (fun v => norm (q (x,v))^4)) mu :=
    hPi.integral_prod_left
  have hpoint (x : Real) (hx : (Set.Icc X (2*X)) x) :
      norm (MeasureTheory.integral nu (fun v => q (x,v)))^4 <=
        MeasureTheory.integral nu (fun v => norm (q (x,v))^4) := by
    have hqxc : ContinuousOn (fun v => q (x,v)) (Set.Icc (0 : Real) 1) :=
      hqc.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hv => And.intro hx hv)
    have hfi : MeasureTheory.Integrable (fun v => norm (q (x,v))) nu :=
      hqxc.norm.integrableOn_Icc
    have hgi : MeasureTheory.Integrable (fun v => norm (q (x,v))^4) nu :=
      (hqxc.norm.pow 4).integrableOn_Icc
    have hconv : ConvexOn Real (Set.Ici (0 : Real)) (fun t : Real => t^4) :=
      convexOn_pow 4
    have hJ : (MeasureTheory.integral nu (fun v => norm (q (x,v))))^4 <=
        MeasureTheory.integral nu (fun v => norm (q (x,v))^4) :=
      hconv.map_integral_le (continuous_id.pow 4).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall (fun v => norm_nonneg (q (x,v)))) hfi hgi
    calc
      _ <= (MeasureTheory.integral nu (fun v => norm (q (x,v))))^4 := by
        gcongr
        exact MeasureTheory.norm_integral_le_integral_norm (fun v => q (x,v))
      _ <= _ := hJ
  have hpointAE : Filter.Eventually
      (fun x => norm (MeasureTheory.integral nu (fun v => q (x,v)))^4 <=
        MeasureTheory.integral nu (fun v => norm (q (x,v))^4)) (MeasureTheory.ae mu) := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
    exact Filter.Eventually.of_forall (fun x hx => hpoint x hx)
  have hpowerC : Continuous (fun z : Complex => norm z^4) := continuous_norm.pow 4
  have hLi : MeasureTheory.Integrable
      (fun x => norm (MeasureTheory.integral nu (fun v => q (x,v)))^4) mu := by
    apply hGi.mono' (hpowerC.comp_aestronglyMeasurable hUi.aestronglyMeasurable)
    exact hpointAE.mono (fun x hx => by
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg
        (MeasureTheory.integral nu (fun v => q (x,v)))) 4)]
      exact hx)
  have hFbig : ContinuousOn F (Set.Icc (X/2) (8*X)) := by
    apply hF.mono
    intro y hy
    change 0 < y
    linarith [hy.1]
  have hT (v : Real) (hv : (Set.Icc (0 : Real) 1) v) :
      MeasureTheory.integral mu (fun x => norm (F (movingSquareMap (a+b*v) x))^4) <= 3*J := by
    have h := integral_fourth_comp_movingSquareMap_le hX (hab v hv).1 (hab v hv).2 hFbig
    rw [intervalIntegral.integral_of_le hX2, intervalIntegral.integral_of_le hY] at h
    simp only [<- MeasureTheory.integral_Icc_eq_integral_Ioc] at h
    exact h
  have hRi : MeasureTheory.Integrable (fun v => norm (psi v)^4*(3*J)) nu :=
    (hpsi.norm.pow 4).integrableOn_Icc.mul_const (3*J)
  have hupperAE : Filter.Eventually
      (fun v => MeasureTheory.integral mu (fun x => norm (q (x,v))^4) <=
        norm (psi v)^4*(3*J)) (MeasureTheory.ae nu) := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
    apply Filter.Eventually.of_forall
    intro v hv
    simp only [q, norm_mul, mul_pow]
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hT v hv) (pow_nonneg (norm_nonneg (psi v)) 4)
  refine And.intro hLi ?_
  change MeasureTheory.integral mu
      (fun x => norm (MeasureTheory.integral nu (fun v => q (x,v)))^4) <=
        3*(MeasureTheory.integral nu (fun v => norm (psi v)^4))*J
  calc
    _ <= MeasureTheory.integral mu
        (fun x => MeasureTheory.integral nu (fun v => norm (q (x,v))^4)) :=
      MeasureTheory.integral_mono_ae hLi hGi hpointAE
    _ = MeasureTheory.integral nu
        (fun v => MeasureTheory.integral mu (fun x => norm (q (x,v))^4)) :=
      MeasureTheory.integral_integral_swap hPi
    _ <= MeasureTheory.integral nu (fun v => norm (psi v)^4*(3*J)) :=
      MeasureTheory.integral_mono_ae hPi.integral_prod_right hRi hupperAE
    _ = _ := by
      rw [MeasureTheory.integral_mul_const]
      ring

theorem movingSquareUnitIntegral_weighted_fourth_moment
    {X a b R : Real} (hX : 16 <= X)
    (hab : forall v, (Set.Icc (0 : Real) 1) v -> -1 <= a+b*v /\ a+b*v <= 2)
    {psi F r : Real -> Complex}
    (hpsi : ContinuousOn psi (Set.Icc (0 : Real) 1))
    (hF : ContinuousOn F (Set.Ioi (0 : Real)))
    (hr : ContinuousOn r (Set.Icc X (2*X)))
    (hR : forall x, (Set.Icc X (2*X)) x -> norm (r x) <= R) :
    MeasureTheory.IntegrableOn
      (fun x => norm (r x*movingSquareUnitIntegral a b psi F x)^4)
      (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (r x*movingSquareUnitIntegral a b psi F x)^4) <=
      (R^4*3)*(MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (psi v)^4)) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
          (fun y => norm (F y)^4) := by
  let mu : MeasureTheory.Measure Real := MeasureTheory.volume.restrict (Set.Icc X (2*X))
  let U : Real -> Complex := movingSquareUnitIntegral a b psi F
  have hbase := movingSquareUnitIntegral_fourth_moment hX hab hpsi hF
  have hri : MeasureTheory.Integrable (fun x => norm (r x)^4) mu :=
    (hr.norm.pow 4).integrableOn_Icc
  have hbi : MeasureTheory.Integrable (fun x => norm (U x)^4) mu := hbase.1
  have hAE : Filter.Eventually
      (fun x => norm (r x)^4*norm (U x)^4 <= R^4*norm (U x)^4)
      (MeasureTheory.ae mu) := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
    apply Filter.Eventually.of_forall
    intro x hx
    have hpower : norm (r x)^4 <= R^4 := by
      gcongr
      exact hR x hx
    exact mul_le_mul_of_nonneg_right hpower (pow_nonneg (norm_nonneg (U x)) 4)
  have hi : MeasureTheory.Integrable (fun x => norm (r x)^4*norm (U x)^4) mu := by
    apply (hbi.const_mul (R^4)).mono'
      (hri.aestronglyMeasurable.mul hbi.aestronglyMeasurable)
    exact hAE.mono (fun x hx => by
      simp only [Pi.mul_apply]
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg (r x)) 4)
        (pow_nonneg (norm_nonneg (U x)) 4))]
      exact hx)
  simp only [norm_mul, mul_pow]
  refine And.intro hi ?_
  calc
    _ <= MeasureTheory.integral mu (fun x => R^4*norm (U x)^4) :=
      MeasureTheory.integral_mono_ae hi (hbi.const_mul (R^4)) hAE
    _ = R^4*MeasureTheory.integral mu (fun x => norm (U x)^4) := by
      rw [MeasureTheory.integral_const_mul]
    _ <= R^4*(3*(MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (psi v)^4)) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
          (fun y => norm (F y)^4)) :=
      mul_le_mul_of_nonneg_left hbase.2 (by positivity)
    _ = _ := by ring


theorem movingSquareUnitIntegral_logWidth_fourth_moment
    {X a b : Real} (hX : 16 <= X)
    (hab : forall v, (Set.Icc (0 : Real) 1) v -> -1 <= a+b*v /\ a+b*v <= 2)
    {psi F : Real -> Complex}
    (hpsi : ContinuousOn psi (Set.Icc (0 : Real) 1))
    (hF : ContinuousOn F (Set.Ioi (0 : Real))) :
    MeasureTheory.IntegrableOn
      (fun x => norm ((movingSquareLogWidth x : Complex)*
        movingSquareUnitIntegral a b psi F x)^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm ((movingSquareLogWidth x : Complex)*
        movingSquareUnitIntegral a b psi F x)^4) <=
      (48/X^2)*(MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (psi v)^4)) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
          (fun y => norm (F y)^4) := by
  have hr : ContinuousOn (fun x => (movingSquareLogWidth x : Complex))
      (Set.Icc X (2*X)) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    exact (movingSquareLogWidth_hasDerivAt hx0).continuousAt.continuousWithinAt
  have hbound (x : Real) (hx : (Set.Icc X (2*X)) x) :
      norm (movingSquareLogWidth x : Complex) <= 2/Real.sqrt X := by
    have hx0 : 0 < x := by linarith [hx.1]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (movingSquareLogWidth_pos hx0)]
    exact (movingSquareLogWidth_dyadic_bounds hX hx.1 hx.2).2
  have h := movingSquareUnitIntegral_weighted_fourth_moment hX hab hpsi hF hr hbound
  have hX0 : 0 <= X := by linarith
  have hs : (Real.sqrt X)^4 = X^2 := by
    calc
      _ = ((Real.sqrt X)^2)^2 := by ring
      _ = X^2 := by rw [Real.sq_sqrt hX0]
  have hcoef : (2/Real.sqrt X)^4*3 = 48/X^2 := by
    rw [div_pow, hs]
    ring
  rw [hcoef] at h
  exact h

theorem movingSquareUnitIntegral_invLogWidth_fourth_moment
    {X a b : Real} (hX : 16 <= X)
    (hab : forall v, (Set.Icc (0 : Real) 1) v -> -1 <= a+b*v /\ a+b*v <= 2)
    {psi F : Real -> Complex}
    (hpsi : ContinuousOn psi (Set.Icc (0 : Real) 1))
    (hF : ContinuousOn F (Set.Ioi (0 : Real))) :
    MeasureTheory.IntegrableOn
      (fun x => norm ((1/(movingSquareLogWidth x : Complex))*
        movingSquareUnitIntegral a b psi F x)^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm ((1/(movingSquareLogWidth x : Complex))*
        movingSquareUnitIntegral a b psi F x)^4) <=
      (3*X^2)*(MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (psi v)^4)) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
          (fun y => norm (F y)^4) := by
  have hr : ContinuousOn (fun x => (1/(movingSquareLogWidth x) : Real))
      (Set.Icc X (2*X)) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hd := (hasDerivAt_inv (movingSquareLogWidth_pos hx0).ne').comp x
      (movingSquareLogWidth_hasDerivAt hx0)
    simpa only [one_div, Function.comp_def] using hd.continuousAt.continuousWithinAt
  have hrC : ContinuousOn (fun x => 1/(movingSquareLogWidth x : Complex))
      (Set.Icc X (2*X)) := by
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_one] using
      Complex.continuous_ofReal.comp_continuousOn hr
  have hbound (x : Real) (hx : (Set.Icc X (2*X)) x) :
      norm (1/(movingSquareLogWidth x : Complex)) <= Real.sqrt X := by
    have hx0 : 0 < x := by linarith [hx.1]
    have hXp : 0 < X := by linarith
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (movingSquareLogWidth_pos hx0)]
    have h := one_div_le_one_div_of_le
      (one_div_pos.mpr (Real.sqrt_pos.mpr hXp))
      (movingSquareLogWidth_dyadic_bounds hX hx.1 hx.2).1
    simpa only [one_div_one_div] using h
  have h := movingSquareUnitIntegral_weighted_fourth_moment hX hab hpsi hF hrC hbound
  have hX0 : 0 <= X := by linarith
  have hs : (Real.sqrt X)^4 = X^2 := by
    calc
      _ = ((Real.sqrt X)^2)^2 := by ring
      _ = X^2 := by rw [Real.sq_sqrt hX0]
  rw [hs, mul_comm (X^2) 3] at h
  exact h

end RobinBV.Sieve
