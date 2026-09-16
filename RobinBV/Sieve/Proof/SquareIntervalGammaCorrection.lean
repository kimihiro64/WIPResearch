/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RobinBV.Mathlib.Analysis.Complex.ExponentialKernel
import Zeta23.ExplicitFormula.Bridge
import Zeta23.GammaFacts.Mu
import Zeta23.WeilEF.FullLine

/-!
# Complete gamma correction for positive-support tests

The actual digamma series is integrated termwise, with its nonnegative
real differences retained until constant cancellation. The exponential
series then gives a complete magnitude bound on compact positive support.
Analytic inputs and Fourier transposition are from the pinned Apache-2.0
Zeta23 dependency documented in SIBLING_CAPABILITIES.md. No GammaFacts,
zero-density or Riemann-hypothesis premise is assumed here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Zeta23.EF

def gammaResolvent (a r : Real) : Real :=
  a / (a^2 + (r/2)^2)

def gammaRealTerm (n : Nat) (r : Real) : Real :=
  1 / ((n : Real)+1) - gammaResolvent ((n : Real)+1+1/4) r

theorem gammaResolvent_nonneg_le {a : Real} (ha : 0 < a) (r : Real) :
    0 <= gammaResolvent a r /\ gammaResolvent a r <= 1/a := by
  have hd : 0 < a^2 + (r/2)^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha)
    (sq_nonneg _)
  refine And.intro (div_nonneg ha.le hd.le) ?_
  dsimp [gammaResolvent]
  calc
    a / (a^2 + (r/2)^2) <= a / a^2 :=
      div_le_div_of_nonneg_left ha.le (sq_pos_of_pos ha) (le_add_of_nonneg_right (sq_nonneg _))
    _ = 1/a := by rw [sq, div_mul_eq_div_div, div_self ha.ne']

theorem gammaRealTerm_nonneg (n : Nat) (r : Real) :
    0 <= gammaRealTerm n r := by
  have hn : 0 < (n : Real)+1 := by positivity
  have ha : 0 < (n : Real)+1+1/4 := by positivity
  have h := (gammaResolvent_nonneg_le ha r).2
  have hm := one_div_le_one_div_of_le hn (show (n : Real)+1 <= (n : Real)+1+1/4 by
    linarith)
  exact sub_nonneg.mpr (h.trans hm)

theorem continuous_gammaResolvent {a : Real} (ha : 0 < a) :
    Continuous (gammaResolvent a) := by
  apply Continuous.div continuous_const
    ((continuous_const).add ((continuous_id.div_const 2).pow 2))
  intro r
  exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg _))

theorem continuous_gammaRealTerm (n : Nat) : Continuous (gammaRealTerm n) :=
  continuous_const.sub (continuous_gammaResolvent (by positivity))

theorem summable_gammaRealTerm (r : Real) : Summable (fun n => gammaRealTerm n r) := by
  exact Zeta23.MuFields.summable_re_terms
    (a := 1/4) (by norm_num) (by norm_num) (r/2)

theorem tsum_gammaRealTerm (r : Real) :
    (tsum fun n => gammaRealTerm n r) =
      gammaBracket r + Real.log Real.pi + Real.eulerMascheroniConstant +
        gammaResolvent (1/4) r := by
  have h := Zeta23.MuFields.re_digamma_vertical
    (a := 1/4) (by norm_num) (by norm_num) (r/2)
  have he : (((1/4 : Real) : Complex) + Complex.I*((r/2 : Real) : Complex)) =
      (1/4 : Complex)+Complex.I*r/2 := by push_cast; ring
  rw [he] at h
  change (Complex.digamma ((1/4 : Complex)+Complex.I*r/2)).re =
    -Real.eulerMascheroniConstant - gammaResolvent (1/4) r +
      (tsum fun n => gammaRealTerm n r) at h
  dsimp [gammaBracket]
  linarith

theorem integrable_paperFT_mul_gammaResolvent {k : Real -> Complex}
    (hFk : Integrable (FourierTransform.fourier k)) {a : Real} (ha : 0 < a) :
    Integrable (fun r : Real => paperFT k r * (gammaResolvent a r : Complex)) := by
  refine (integrable_paperFT_ofReal hFk).mul_bdd (c := 1/a)
    (Complex.continuous_ofReal.comp (continuous_gammaResolvent ha)).aestronglyMeasurable ?_
  apply Filter.Eventually.of_forall
  intro r
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gammaResolvent_nonneg_le ha r).1]
  exact (gammaResolvent_nonneg_le ha r).2

theorem integrable_paperFT_mul_gammaBracket {k : Real -> Complex}
    (hk : ContDiff Real 2 k) (hkc : HasCompactSupport k) :
    Integrable (fun r : Real => paperFT k r * (gammaBracket r : Complex)) := by
  choose K hK0 hK using Zeta23.WeilEF.norm_Hfn_le hk hkc
  choose C hC0 hC using Zeta23.WeilEF.digamma_growth_strip
  let D : Real := 5*C + abs (Real.log Real.pi)
  have hD0 : 0 <= D := by dsimp [D]; positivity
  have hcont : Continuous gammaBracket := by
    have he : gammaBracket = fun r : Real => 2*Real.pi*mu r := by
      funext r
      dsimp [gammaBracket, mu]
      field_simp
    rw [he]
    exact continuous_const.mul Zeta23.mu_smooth.continuous
  have hH := integrable_paperFT_ofReal (integrable_fourier_of_contDiff_two hk hkc)
  have hmaj : Integrable (fun r : Real =>
      (K*D)*((1 : Real)+norm r^2)^(-(3/2 : Real)/2)) :=
    (integrable_rpow_neg_one_add_norm_sq (E := Real)
      (by rw [Module.finrank_self]; norm_num)).const_mul (K*D)
  refine hmaj.mono'
    (hH.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp hcont).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun r => ?_)
  have hq : 0 < 1+r^2 := by positivity
  have hHbound : norm (paperFT k r) <= K/(1+r^2) := by
    simpa only [Zeta23.WeilEF.Hfn_apply, sub_self, Complex.ofReal_zero,
      zero_mul, add_zero] using hK (1/2) r (by norm_num) (by norm_num)
  have hpsi := hC ((1/4 : Complex)+Complex.I*r/2) (by norm_num) (by norm_num)
  have him : ((1/4 : Complex)+Complex.I*r/2).im = r/2 := by simp
  rw [him, abs_div, abs_two] at hpsi
  have hlog : Real.log (2+abs r/2) <= 5*(1+r^2)^(1/4 : Real) := by
    calc
      _ <= Real.log (2+abs r) :=
        Real.log_le_log (by positivity) (by linarith [abs_nonneg r])
      _ <= _ := by simpa only [sq_abs] using
        Zeta23.WeilEF.log_two_add_le (abs_nonneg r)
  have hone : (1 : Real) <= (1+r^2)^(1/4 : Real) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg r]) (by norm_num)
  have hB : abs (gammaBracket r) <= D*(1+r^2)^(1/4 : Real) := by
    have ht := abs_sub
      (Complex.digamma ((1/4 : Complex)+Complex.I*r/2)).re (Real.log Real.pi)
    have hre := Complex.abs_re_le_norm
      (Complex.digamma ((1/4 : Complex)+Complex.I*r/2))
    have hpc := mul_le_mul_of_nonneg_left hlog hC0.le
    have hlogc := mul_le_mul_of_nonneg_left hone (abs_nonneg (Real.log Real.pi))
    dsimp [gammaBracket, D]
    nlinarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ <= (K/(1+r^2))*(D*(1+r^2)^(1/4 : Real)) :=
      mul_le_mul hHbound hB (abs_nonneg _) (div_nonneg hK0 hq.le)
    _ = (K*D)*((1 : Real)+norm r^2)^(-(3/2 : Real)/2) := by
      rw [Real.norm_eq_abs, sq_abs]
      have he : (1+r^2)^(-(3/2 : Real)/2) = (1+r^2)^(1/4 : Real)/(1+r^2) := by
        rw [show (-(3/2 : Real)/2) = (1/4 : Real)-1 by norm_num,
          Real.rpow_sub hq, Real.rpow_one]
      rw [he]
      ring

theorem integrable_paperFT_mul_gammaRealSum {k : Real -> Complex}
    (hk : ContDiff Real 2 k) (hkc : HasCompactSupport k) :
    Integrable (fun r : Real => paperFT k r *
      ((tsum (fun n : Nat => gammaRealTerm n r) : Real) : Complex)) := by
  have hFk := integrable_fourier_of_contDiff_two hk hkc
  have hb := integrable_paperFT_mul_gammaBracket hk hkc
  have hc := (integrable_paperFT_ofReal hFk).mul_const
    ((Real.log Real.pi + Real.eulerMascheroniConstant : Real) : Complex)
  have hq := integrable_paperFT_mul_gammaResolvent hFk
    (a := 1/4) (by norm_num)
  apply ((hb.add hc).add hq).congr
  apply Filter.Eventually.of_forall
  intro r
  change (paperFT k r * (gammaBracket r : Complex) +
    paperFT k r * ((Real.log Real.pi + Real.eulerMascheroniConstant : Real) : Complex)) +
    paperFT k r * (gammaResolvent (1/4) r : Complex) =
    paperFT k r * ((tsum (fun n : Nat => gammaRealTerm n r) : Real) : Complex)
  rw [tsum_gammaRealTerm]
  push_cast
  ring

theorem hasSum_integral_paperFT_mul_gammaRealTerm {k : Real -> Complex}
    (hk : ContDiff Real 2 k) (hkc : HasCompactSupport k) :
    HasSum (fun n : Nat => MeasureTheory.integral MeasureTheory.volume
      (fun r : Real => paperFT k r * (gammaRealTerm n r : Complex)))
      (MeasureTheory.integral MeasureTheory.volume (fun r : Real =>
        paperFT k r * ((tsum (fun n : Nat => gammaRealTerm n r) : Real) : Complex))) := by
  let H : Real -> Complex := fun r => paperFT k r
  let Q : Real -> Real := fun r => tsum fun n => gammaRealTerm n r
  have hH : Integrable H :=
    integrable_paperFT_ofReal (integrable_fourier_of_contDiff_two hk hkc)
  have hs (r : Real) : HasSum (fun n => gammaRealTerm n r) (Q r) :=
    (summable_gammaRealTerm r).hasSum
  have hQ (r : Real) : 0 <= Q r := tsum_nonneg (fun n => gammaRealTerm_nonneg n r)
  have hi : Integrable (fun r => norm (H r)*Q r) := by
    have h := (integrable_paperFT_mul_gammaRealSum hk hkc).norm
    apply h.congr
    apply Filter.Eventually.of_forall
    intro r
    change norm (H r * (Q r : Complex)) = norm (H r)*Q r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hQ r)]
  apply MeasureTheory.hasSum_integral_of_dominated_convergence
    (fun n r => norm (H r)*gammaRealTerm n r)
  next =>
    intro n
    exact hH.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp (continuous_gammaRealTerm n)).aestronglyMeasurable
  next =>
    intro n
    apply Filter.Eventually.of_forall
    intro r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gammaRealTerm_nonneg n r)]
  next =>
    apply Filter.Eventually.of_forall
    intro r
    exact (hs r).summable.mul_left _
  next =>
    apply hi.congr
    apply Filter.Eventually.of_forall
    intro r
    exact ((hs r).mul_left (norm (H r))).tsum_eq.symm
  next =>
    apply Filter.Eventually.of_forall
    intro r
    exact (((Complex.ofRealCLM).hasSum (hs r)).mul_left (H r))


def gammaWeight (a u : Real) : Complex :=
  Complex.exp (-((2*a : Real) : Complex)*abs u)

theorem integrable_gammaWeight {a : Real} (ha : 0 < a) :
    Integrable (gammaWeight a) := by
  have h4a : 0 < 4*a := by linarith
  have h := integrable_exp_neg_abs_half.comp_mul_left' h4a.ne'
  apply h.congr
  apply Filter.Eventually.of_forall
  intro u
  change ((Real.exp (-abs ((4*a)*u)/2) : Real) : Complex) =
    Complex.exp (-((2*a : Real) : Complex)*abs u)
  rw [abs_mul, abs_of_pos h4a, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem integral_gammaWeight_fourier {a : Real} (ha : 0 < a) (r : Real) :
    MeasureTheory.integral MeasureTheory.volume (fun u : Real =>
      gammaWeight a u * Complex.exp (-Complex.I*r*u)) =
        (gammaResolvent a r : Complex) := by
  calc
    _ = MeasureTheory.integral MeasureTheory.volume (fun u : Real =>
        Complex.exp (-((2*a : Real) : Complex)*abs u - Complex.I*r*u)) := by
      apply congrArg (MeasureTheory.integral MeasureTheory.volume)
      funext u
      dsimp [gammaWeight]
      rw [<- Complex.exp_add]
      congr 1
      ring
    _ = 2*((2*a : Real) : Complex) /
        (((2*a : Real) : Complex)^2+(r : Complex)^2) :=
      Complex.integral_exp_neg_mul_abs_fourier (by linarith) r
    _ = _ := by
      dsimp [gammaResolvent]
      push_cast
      rw [show (2*(a : Complex))^2+(r : Complex)^2 =
        4*((a : Complex)^2+((r : Complex)/2)^2) by ring, div_mul_eq_div_div]
      congr 1
      ring

theorem integral_paperFT_mul_gammaResolvent {k : Real -> Complex}
    (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (FourierTransform.fourier k)) {a : Real} (ha : 0 < a) :
    (1/(2*Real.pi) : Complex) * MeasureTheory.integral MeasureTheory.volume
      (fun r : Real => paperFT k r * (gammaResolvent a r : Complex)) =
    MeasureTheory.integral MeasureTheory.volume (fun u => k u * gammaWeight a u) := by
  have h := (integral_k_mul_weight hk hki hFk (integrable_gammaWeight ha)).symm
  simpa only [integral_gammaWeight_fourier ha] using h

theorem hasSum_gamma_correction_weights {k : Real -> Complex}
    (hk : ContDiff Real 2 k) (hkc : HasCompactSupport k) (hk0 : k 0 = 0) :
    HasSum (fun j : Nat => MeasureTheory.integral MeasureTheory.volume
      (fun u : Real => k u * gammaWeight ((j : Real)+1+1/4) u))
      (-(1/(2*Real.pi) : Complex) * MeasureTheory.integral MeasureTheory.volume
        (fun r : Real => paperFT k r * (gammaBracket r : Complex)) -
      MeasureTheory.integral MeasureTheory.volume (fun u => k u * gammaWeight (1/4) u)) := by
  let c : Complex := 1/(2*Real.pi)
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  have hFk := integrable_fourier_of_contDiff_two hk hkc
  have hH := integrable_paperFT_ofReal hFk
  have hzero : c*MeasureTheory.integral MeasureTheory.volume (fun r : Real => paperFT k r) =
      0 := by
    have h := paper_inversion hk.continuous hki hFk 0
    simpa only [hk0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] using h.symm
  have hterm (j : Nat) :
      c*MeasureTheory.integral MeasureTheory.volume
        (fun r : Real => paperFT k r * (gammaRealTerm j r : Complex)) =
      -MeasureTheory.integral MeasureTheory.volume
        (fun u : Real => k u * gammaWeight ((j : Real)+1+1/4) u) := by
    have ha : 0 < (j : Real)+1+1/4 := by positivity
    have hconst := hH.mul_const (((1/((j : Real)+1) : Real)) : Complex)
    have hres := integrable_paperFT_mul_gammaResolvent hFk ha
    have he : (fun r : Real => paperFT k r * (gammaRealTerm j r : Complex)) =
        fun r : Real => paperFT k r * (((1/((j : Real)+1) : Real)) : Complex) -
          paperFT k r * (gammaResolvent ((j : Real)+1+1/4) r : Complex) := by
      funext r
      dsimp [gammaRealTerm]
      push_cast
      ring
    calc
      _ = (c*MeasureTheory.integral MeasureTheory.volume (fun r : Real => paperFT k r)) *
          (((1/((j : Real)+1) : Real)) : Complex) -
          c*MeasureTheory.integral MeasureTheory.volume
            (fun r : Real => paperFT k r *
              (gammaResolvent ((j : Real)+1+1/4) r : Complex)) := by
        rw [he, MeasureTheory.integral_sub hconst hres, cintegral_mul_const]
        ring
      _ = _ := by
        rw [hzero, zero_mul, zero_sub]
        exact congrArg Neg.neg (integral_paperFT_mul_gammaResolvent
          hk.continuous hki hFk ha)
  have hseries := (hasSum_integral_paperFT_mul_gammaRealTerm hk hkc).mul_left (-c)
  have hseries' : HasSum (fun j : Nat => MeasureTheory.integral MeasureTheory.volume
      (fun u : Real => k u * gammaWeight ((j : Real)+1+1/4) u))
      (-c*MeasureTheory.integral MeasureTheory.volume (fun r : Real =>
        paperFT k r * ((tsum (fun j : Nat => gammaRealTerm j r) : Real) : Complex))) := by
    have heq : (fun j : Nat => -c*MeasureTheory.integral MeasureTheory.volume
        (fun r : Real => paperFT k r * (gammaRealTerm j r : Complex))) =
        fun j : Nat => MeasureTheory.integral MeasureTheory.volume
          (fun u : Real => k u * gammaWeight ((j : Real)+1+1/4) u) := by
      funext j
      calc
        _ = -(c*MeasureTheory.integral MeasureTheory.volume
          (fun r : Real => paperFT k r * (gammaRealTerm j r : Complex))) := by ring
        _ = _ := by rw [hterm, neg_neg]
    rw [heq] at hseries
    exact hseries
  have hb := integrable_paperFT_mul_gammaBracket hk hkc
  have hc := hH.mul_const
    ((Real.log Real.pi + Real.eulerMascheroniConstant : Real) : Complex)
  have hr := integrable_paperFT_mul_gammaResolvent hFk (a := 1/4) (by norm_num)
  have hQfun : (fun r : Real =>
      paperFT k r * ((tsum (fun j : Nat => gammaRealTerm j r) : Real) : Complex)) =
      fun r : Real => (paperFT k r * (gammaBracket r : Complex) +
        paperFT k r * ((Real.log Real.pi + Real.eulerMascheroniConstant : Real) : Complex)) +
          paperFT k r * (gammaResolvent (1/4) r : Complex) := by
    funext r
    rw [tsum_gammaRealTerm]
    push_cast
    ring
  have hval :
      -c*MeasureTheory.integral MeasureTheory.volume (fun r : Real =>
        paperFT k r * ((tsum (fun j : Nat => gammaRealTerm j r) : Real) : Complex)) =
      -c*MeasureTheory.integral MeasureTheory.volume
        (fun r : Real => paperFT k r * (gammaBracket r : Complex)) -
      MeasureTheory.integral MeasureTheory.volume (fun u => k u * gammaWeight (1/4) u) := by
    have hadd1 := MeasureTheory.integral_add (hb.add hc) hr
    have hadd2 := MeasureTheory.integral_add hb hc
    dsimp only [Pi.add_apply] at hadd1 hadd2
    rw [hQfun, hadd1, hadd2, cintegral_mul_const]
    have hres := integral_paperFT_mul_gammaResolvent hk.continuous hki hFk
      (a := 1/4) (by norm_num)
    change c*MeasureTheory.integral MeasureTheory.volume
      (fun r : Real => paperFT k r * (gammaResolvent (1/4) r : Complex)) =
        MeasureTheory.integral MeasureTheory.volume (fun u => k u * gammaWeight (1/4) u) at hres
    linear_combination
      -((Real.log Real.pi + Real.eulerMascheroniConstant : Real) : Complex)*hzero - hres
  rw [hval] at hseries'
  exact hseries'


theorem norm_integral_gammaWeight_le {k : Real -> Complex} {c d : Real}
    (hc : 0 < c) (hcd : c <= d)
    (hsupp : forall u : Real, Not (Membership.mem (Set.Icc c d) u) -> k u = 0)
    (hbound : forall u : Real, Membership.mem (Set.Icc c d) u ->
      norm (k u) <= Real.exp (u/2)) (j : Nat) :
    norm (MeasureTheory.integral MeasureTheory.volume
      (fun u : Real => k u * gammaWeight ((j : Real)+1+1/4) u)) <=
        (d-c)*Real.exp (-(2*(j : Real)+2)*c) := by
  have he : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc c d))
      (fun u : Real => k u * gammaWeight ((j : Real)+1+1/4) u) =
      MeasureTheory.integral MeasureTheory.volume
      (fun u : Real => k u * gammaWeight ((j : Real)+1+1/4) u) :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by rw [hsupp u hu, zero_mul])
  rw [<- he]
  have ht : norm (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc c d))
      (fun u : Real => k u * gammaWeight ((j : Real)+1+1/4) u)) <=
      Real.exp (-(2*(j : Real)+2)*c)*MeasureTheory.volume.real (Set.Icc c d) := by
    apply MeasureTheory.norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hc hu.1
    have hw : norm (gammaWeight ((j : Real)+1+1/4) u) =
        Real.exp (-(2*((j : Real)+1+1/4))*u) := by
      simp [gammaWeight, Complex.norm_exp, abs_of_pos hu0]
    rw [norm_mul, hw]
    calc
      _ <= Real.exp (u/2)*Real.exp (-(2*((j : Real)+1+1/4))*u) :=
        mul_le_mul_of_nonneg_right (hbound u hu) (Real.exp_pos _).le
      _ = Real.exp (-(2*(j : Real)+2)*u) := by
        rw [<- Real.exp_add]
        congr 1
        ring
      _ <= _ := Real.exp_le_exp.mpr (by
        have hj : (0 : Real) <= j := Nat.cast_nonneg j
        nlinarith [hu.1])
  rw [Real.volume_real_Icc_of_le hcd] at ht
  simpa only [mul_comm] using ht

theorem integral_gammaWeight_quarter_eq_paperFT {k : Real -> Complex}
    (hk : forall u : Real, u <= 0 -> k u = 0) :
    MeasureTheory.integral MeasureTheory.volume (fun u : Real => k u * gammaWeight (1/4) u) =
      paperFT k (Complex.I/2) := by
  unfold paperFT
  apply congrArg (MeasureTheory.integral MeasureTheory.volume)
  funext u
  by_cases hu : u <= 0
  next =>
    rw [hk u hu, zero_mul, zero_mul]
  next =>
    dsimp [gammaWeight]
    rw [abs_of_pos (lt_of_not_ge hu)]
    congr 1
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring

theorem gammaCorrection_norm_le {k : Real -> Complex} {c d : Real}
    (hk : ContDiff Real 2 k) (hkc : HasCompactSupport k)
    (hc : 0 < c) (hcd : c <= d)
    (hsupp : forall u : Real, Not (Membership.mem (Set.Icc c d) u) -> k u = 0)
    (hbound : forall u : Real, Membership.mem (Set.Icc c d) u ->
      norm (k u) <= Real.exp (u/2)) :
    norm ((1/(2*Real.pi) : Complex) * MeasureTheory.integral MeasureTheory.volume
      (fun r : Real => paperFT k r * (gammaBracket r : Complex)) +
      paperFT k (Complex.I/2)) <= (d-c)/(Real.exp (2*c)-1) := by
  have hkneg : forall u : Real, u <= 0 -> k u = 0 := by
    intro u hu
    apply hsupp u
    intro hmem
    have hcu : c <= u := hmem.1
    linarith
  have hzero : k 0 = 0 := hkneg 0 le_rfl
  have hpole := integral_gammaWeight_quarter_eq_paperFT hkneg
  let r : Real := Real.exp (-2*c)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    have h := Real.exp_lt_exp.mpr (show -2*c < (0 : Real) by linarith)
    simpa only [Real.exp_zero] using h
  have hexp (j : Nat) :
      Real.exp (-(2*(j : Real)+2)*c) = r^j*r := by
    rw [show -(2*(j : Real)+2)*c = (j : Real)*(-2*c)+(-2*c) by ring,
      Real.exp_add, Real.exp_nat_mul]
  have hfun : (fun j : Nat => (d-c)*Real.exp (-(2*(j : Real)+2)*c)) =
      fun j : Nat => ((d-c)*r)*r^j := by
    funext j
    rw [hexp]
    ring
  have hval : ((d-c)*r)*Inv.inv (1-r) = (d-c)/(Real.exp (2*c)-1) := by
    have hE : 1 < Real.exp (2*c) := by
      have h := Real.exp_lt_exp.mpr (show (0 : Real) < 2*c by linarith)
      simpa only [Real.exp_zero] using h
    have hden1 : Not (1-r = 0) := ne_of_gt (sub_pos.mpr hr1)
    have hden2 : Not (Real.exp (2*c)-1 = 0) := ne_of_gt (sub_pos.mpr hE)
    have hre : r*Real.exp (2*c) = 1 := by
      dsimp [r]
      rw [<- Real.exp_add, show -2*c+2*c = (0 : Real) by ring, Real.exp_zero]
    rw [<- div_eq_mul_inv]
    apply (_root_.div_eq_div_iff hden1 hden2).mpr
    calc
      ((d-c)*r)*(Real.exp (2*c)-1) = (d-c)*(r*Real.exp (2*c)-r) := by ring
      _ = (d-c)*(1-r) := by rw [hre]
  have hgeom : HasSum (fun j : Nat => (d-c)*Real.exp (-(2*(j : Real)+2)*c))
      ((d-c)/(Real.exp (2*c)-1)) := by
    rw [hfun]
    have h := (hasSum_geometric_of_lt_one hr0.le hr1).mul_left ((d-c)*r)
    rw [hval] at h
    exact h
  let I : Nat -> Complex := fun j => MeasureTheory.integral MeasureTheory.volume
    (fun u : Real => k u * gammaWeight ((j : Real)+1+1/4) u)
  have hI (j : Nat) : norm (I j) <= (d-c)*Real.exp (-(2*(j : Real)+2)*c) :=
    norm_integral_gammaWeight_le hc hcd hsupp hbound j
  have hnorm : Summable (fun j => norm (I j)) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hI hgeom.summable
  have hs := hasSum_gamma_correction_weights hk hkc hzero
  rw [hpole] at hs
  have hsum : (tsum I) =
      -((1/(2*Real.pi) : Complex) * MeasureTheory.integral MeasureTheory.volume
        (fun r : Real => paperFT k r * (gammaBracket r : Complex)) + paperFT k (Complex.I/2)) := by
    calc
      _ = _ := hs.tsum_eq
      _ = _ := by ring
  calc
    _ = norm (tsum I) := by rw [hsum, norm_neg]
    _ <= tsum (fun j => norm (I j)) := norm_tsum_le_tsum_norm hnorm
    _ <= tsum (fun j : Nat => (d-c)*Real.exp (-(2*(j : Real)+2)*c)) :=
      hnorm.tsum_le_tsum hI hgeom.summable
    _ = _ := hgeom.tsum_eq

end Zeta23.EF
