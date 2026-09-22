/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Distributions.Cauchy

/-!
# Cauchy smoothing Fourier identities

These identities evaluate the Cauchy smoothing profile and its inverse Fourier
transform. They are the analytic input consumed by the variable-beta
reflection energy estimate in the almost-all zero-moment chain.
-/

set_option autoImplicit false

open MeasureTheory

namespace ProbabilityTheory

noncomputable def cauchyLaplaceProfile (b : NNReal) (x : Real) : Complex :=
  Complex.exp (((-2*Real.pi*(b : Real)*abs x : Real) : Complex))

theorem cauchyLaplaceProfile_fourier (b : NNReal) (hb : 0 < (b : Real))
    (w : Real) :
    FourierTransform.fourier (cauchyLaplaceProfile b) w =
      (cauchyPDFReal 0 b w : Complex) := by
  let f : Real -> Complex := fun x =>
    Complex.exp (((-2*Real.pi*x*w : Real) : Complex)*Complex.I)*
      cauchyLaplaceProfile b x
  let aL : Complex := ((2*Real.pi*(b : Real) : Real) : Complex) -
    ((2*Real.pi*w : Real) : Complex)*Complex.I
  let aR : Complex := -((2*Real.pi*(b : Real) : Real) : Complex) -
    ((2*Real.pi*w : Real) : Complex)*Complex.I
  have hs : 0 < 2*Real.pi*(b : Real) :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) hb
  have haL : 0 < aL.re := by simpa [aL] using hs
  have haR : aR.re < 0 := by simpa [aR] using neg_neg_of_pos hs
  have heL : Filter.EventuallyEq (ae (volume.restrict (Set.Iic (0 : Real))))
      f (fun x : Real => Complex.exp (aL*(x : Complex))) := by
    apply Filter.Eventually.mono (ae_restrict_mem measurableSet_Iic)
    intro x hx
    change x <= 0 at hx
    dsimp [f, cauchyLaplaceProfile]
    rw [abs_of_nonpos hx, <- Complex.exp_add]
    congr 1
    dsimp [aL]
    push_cast
    ring
  have heR : Filter.EventuallyEq (ae (volume.restrict (Set.Ioi (0 : Real))))
      f (fun x : Real => Complex.exp (aR*(x : Complex))) := by
    apply Filter.Eventually.mono (ae_restrict_mem measurableSet_Ioi)
    intro x hx
    change 0 < x at hx
    dsimp [f, cauchyLaplaceProfile]
    rw [abs_of_nonneg hx.le, <- Complex.exp_add]
    congr 1
    dsimp [aR]
    push_cast
    ring
  have hiL : IntegrableOn f (Set.Iic (0 : Real)) :=
    (integrable_congr heL).2 (integrableOn_exp_mul_complex_Iic haL 0)
  have hiR : IntegrableOn f (Set.Ioi (0 : Real)) :=
    (integrable_congr heR).2 (integrableOn_exp_mul_complex_Ioi haR 0)
  have hL : integral (volume.restrict (Set.Iic (0 : Real))) f = 1/aL := by
    rw [integral_congr_ae heL, integral_exp_mul_complex_Iic haL]
    simp
  have hR : integral (volume.restrict (Set.Ioi (0 : Real))) f = -1/aR := by
    rw [integral_congr_ae heR, integral_exp_mul_complex_Ioi haR]
    simp
  have hL0 : Not (aL = 0) := by
    intro h
    rw [h] at haL
    norm_num at haL
  have hR0 : Not (aR = 0) := by
    intro h
    rw [h] at haR
    norm_num at haR
  have hp : Not ((Real.pi : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdR : 0 < w^2+(b : Real)^2 := by positivity
  have hd : Not (((w : Complex)^2+((b : Real) : Complex)^2) = 0) := by
    exact_mod_cast hdR.ne'
  have halg : 1/aL + -1/aR = (cauchyPDFReal 0 b w : Complex) := by
    simp only [cauchyPDFReal, sub_zero, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_add, Complex.ofReal_pow]
    field_simp [hL0, hR0, hp, hd]
    dsimp [aL, aR]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  calc
    FourierTransform.fourier (cauchyLaplaceProfile b) w =
        integral volume f := by
      simpa only [smul_eq_mul] using
        Real.fourier_real_eq_integral_exp_smul (cauchyLaplaceProfile b) w
    _ = integral (volume.restrict (Set.Iic (0 : Real))) f +
        integral (volume.restrict (Set.Ioi (0 : Real))) f :=
      (intervalIntegral.integral_Iic_add_Ioi hiL hiR).symm
    _ = 1/aL + -1/aR := by rw [hL, hR]
    _ = (cauchyPDFReal 0 b w : Complex) := halg

theorem integrable_cauchyLaplaceProfile (b : NNReal) (hb : 0 < (b : Real)) :
    Integrable (cauchyLaplaceProfile b) := by
  have h0 : Not (b = 0) := by
    intro h
    rw [h] at hb
    norm_num at hb
  have hp := cauchyPDF_pos 0 h0 0
  have hi : integral volume (cauchyLaplaceProfile b) =
      (cauchyPDFReal 0 b 0 : Complex) := by
    simpa [Real.fourier_real_eq_integral_exp_smul] using
      cauchyLaplaceProfile_fourier b hb 0
  apply Integrable.of_integral_ne_zero
  rw [hi]
  exact Complex.ofReal_ne_zero.mpr hp.ne'

theorem continuous_cauchyLaplaceProfile (b : NNReal) :
    Continuous (cauchyLaplaceProfile b) := by
  have h : Continuous (fun x : Real => -2*Real.pi*(b : Real)*abs x) :=
    continuous_const.mul continuous_abs
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.comp h)

theorem integral_cauchyPDFReal_mul_exp (b : NNReal) (hb : 0 < (b : Real))
    (lambda : Real) :
    integral volume (fun v : Real => (cauchyPDFReal 0 b v : Complex)*
      Complex.exp (-Complex.I*(v : Complex)*(lambda : Complex))) =
      Complex.exp (((-(b : Real)*abs lambda : Real) : Complex)) := by
  let u : Real := -lambda/(2*Real.pi)
  have hF : FourierTransform.fourier (cauchyLaplaceProfile b) =
      fun v : Real => (cauchyPDFReal 0 b v : Complex) :=
    funext (cauchyLaplaceProfile_fourier b hb)
  have hpdf : Integrable (fun v : Real => (cauchyPDFReal 0 b v : Complex)) :=
    (integrable_cauchyPDFReal 0).ofReal
  have hFi : Integrable (FourierTransform.fourier (cauchyLaplaceProfile b)) := by
    rw [hF]
    exact hpdf
  have hi := (integrable_cauchyLaplaceProfile b hb).fourierInv_fourier_eq hFi
    ((continuous_cauchyLaplaceProfile b).continuousAt (x := u))
  rw [hF] at hi
  have hinv : FourierTransformInv.fourierInv
      (fun v : Real => (cauchyPDFReal 0 b v : Complex)) u =
      integral volume (fun v : Real =>
        Complex.exp (((2*Real.pi*v*u : Real) : Complex)*Complex.I)*
          (cauchyPDFReal 0 b v : Complex)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Real.fourierInv_eq' (fun v : Real => (cauchyPDFReal 0 b v : Complex)) u
  have hphase (v : Real) :
      ((2*Real.pi*v*u : Real) : Complex)*Complex.I =
        -Complex.I*(v : Complex)*(lambda : Complex) := by
    dsimp [u]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    <;> ring
  have hvalue : cauchyLaplaceProfile b u =
      Complex.exp (((-(b : Real)*abs lambda : Real) : Complex)) := by
    unfold cauchyLaplaceProfile
    congr 1
    congr 1
    dsimp [u]
    rw [abs_div, abs_neg, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    field_simp
    <;> ring
  calc
    integral volume (fun v : Real => (cauchyPDFReal 0 b v : Complex)*
        Complex.exp (-Complex.I*(v : Complex)*(lambda : Complex))) =
        integral volume (fun v : Real =>
          Complex.exp (((2*Real.pi*v*u : Real) : Complex)*Complex.I)*
            (cauchyPDFReal 0 b v : Complex)) := by
      apply integral_congr_ae
      apply ae_of_all
      intro v
      change (cauchyPDFReal 0 b v : Complex)*
        Complex.exp (-Complex.I*(v : Complex)*(lambda : Complex)) =
        Complex.exp (((2*Real.pi*v*u : Real) : Complex)*Complex.I)*
          (cauchyPDFReal 0 b v : Complex)
      rw [hphase v, mul_comm]
    _ = FourierTransformInv.fourierInv
        (fun v : Real => (cauchyPDFReal 0 b v : Complex)) u := hinv.symm
    _ = cauchyLaplaceProfile b u := hi
    _ = Complex.exp (((-(b : Real)*abs lambda : Real) : Complex)) := hvalue

end ProbabilityTheory
