/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.FiniteMellinMoment
import RobinBV.Sieve.Helpers.SquareIntervalMovingMoment
import RobinBV.Sieve.Proof.SquareIntervalZeroKernel

/-!
# Fourth-moment transfer for finite square-window zero packets

The exact Fourier packets are composed with the proved smoothing estimates.
All finite coefficients, phases and nonzero-denominator conditions remain
explicit. The right-hand packet moments are not estimated here. The second
profile is intended for high zero heights, not an assertion of a power-saving
fourth moment for zeros with real part close to one.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem movingSquareTest_finite_packet_low_moment {I : Type*}
    (A : Finset I) (rho coefficient : I -> Complex)
    {X eta : Real} (hX : 16 <= X) (he : 0 < eta) :
    MeasureTheory.IntegrableOn (fun x =>
      norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) <=
      (48/X^2)*MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
        (fun y => norm (Finset.sum A (fun i =>
          coefficient i*Complex.exp (rho i*(Real.log y : Complex))))^4) := by
  let F : Real -> Complex := fun y =>
    Finset.sum A (fun i => coefficient i*Complex.exp (rho i*(Real.log y : Complex)))
  let Z : Real -> Complex := fun x => Finset.sum A (fun i => coefficient i*
    Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
      (Zeta23.gammaOf (rho i)))
  let mu : MeasureTheory.Measure Real := MeasureTheory.volume.restrict (Set.Icc X (2*X))
  let nu : MeasureTheory.Measure Real := MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1)
  have hF : ContinuousOn F (Set.Ioi (0 : Real)) := by
    have hlog : ContinuousOn Real.log (Set.Ioi (0 : Real)) :=
      fun y hy => (Real.hasDerivAt_log hy.ne').continuousAt.continuousWithinAt
    apply continuousOn_finsetSum A
    intro i hi
    apply continuousOn_const.mul
    apply Complex.continuous_exp.comp_continuousOn
    apply continuousOn_const.mul
    exact Complex.continuous_ofReal.comp_continuousOn hlog
  have hab : forall v, (Set.Icc (0 : Real) 1) v ->
      -1 <= 0+1*v /\ 0+1*v <= 2 := by
    intro v hv
    constructor <;> linarith [hv.1, hv.2]
  have hbound := movingSquareUnitIntegral_logWidth_fourth_moment hX hab
    (logWindowProfile_contDiff eta).continuous.continuousOn hF
  have heq (x : Real) (hx : (Set.Icc X (2*X)) x) :
      Z x = (movingSquareLogWidth x : Complex)*
        movingSquareUnitIntegral 0 1 (logWindowProfile eta) F x := by
    have hx0 : 0 < x := by linarith [hx.1]
    dsimp [Z]
    rw [movingSquareTest_finite_packet_integral A rho coefficient he hx0]
    apply congrArg (fun z : Complex => (movingSquareLogWidth x : Complex)*z)
    change MeasureTheory.integral MeasureTheory.volume
        (fun v => logWindowProfile eta v*F (movingSquareMap v x)) =
      MeasureTheory.integral nu
        (fun v => logWindowProfile eta v*F (movingSquareMap (0+1*v) x))
    simp only [zero_add, one_mul]
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hz : logWindowProfile eta v = 0 := by
      by_contra h
      exact hv (logWindowProfile_tsupport_subset he (subset_closure h))
    rw [hz, zero_mul]
  have heqAE : Filter.Eventually (fun x => norm (Z x)^4 =
      norm ((movingSquareLogWidth x : Complex)*
        movingSquareUnitIntegral 0 1 (logWindowProfile eta) F x)^4)
      (MeasureTheory.ae mu) := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
    exact Filter.Eventually.of_forall (fun x hx =>
      congrArg (fun z : Complex => norm z^4) (heq x hx))
  have hZi : MeasureTheory.Integrable (fun x => norm (Z x)^4) mu :=
    hbound.1.congr (Filter.Eventually.mono heqAE (fun _ h => h.symm))
  have hmass : MeasureTheory.integral nu (fun v => norm (logWindowProfile eta v)^4) <= 1 := by
    calc
      _ <= MeasureTheory.integral nu (fun _ : Real => (1 : Real)) := by
        apply MeasureTheory.integral_mono_ae
          ((logWindowProfile_contDiff eta).continuous.norm.pow 4).continuousOn.integrableOn_Icc
          (MeasureTheory.integrable_const 1)
        apply Filter.Eventually.of_forall
        intro v
        change norm (logWindowProfile eta v)^4 <= 1
        have hn := norm_nonneg (logWindowProfile eta v)
        have hb := logWindowProfile_norm_le_one eta v
        have hs : norm (logWindowProfile eta v)^2 <= 1 := by
          nlinarith [mul_le_mul_of_nonneg_right hb hn]
        nlinarith [mul_le_mul_of_nonneg_right hs
          (sq_nonneg (norm (logWindowProfile eta v)))]
      _ = 1 := by simp [nu]
  have hJ : 0 <= MeasureTheory.integral
      (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
      (fun y => norm (F y)^4) :=
    MeasureTheory.integral_nonneg (fun y => pow_nonneg (norm_nonneg (F y)) 4)
  refine And.intro hZi ?_
  change MeasureTheory.integral mu (fun x => norm (Z x)^4) <=
    (48/X^2)*MeasureTheory.integral
      (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X))) (fun y => norm (F y)^4)
  calc
    _ = MeasureTheory.integral mu
        (fun x => norm ((movingSquareLogWidth x : Complex)*
          movingSquareUnitIntegral 0 1 (logWindowProfile eta) F x)^4) :=
      MeasureTheory.integral_congr_ae heqAE
    _ <= (48/X^2)*(MeasureTheory.integral nu
        (fun v => norm (logWindowProfile eta v)^4))*
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
          (fun y => norm (F y)^4) := hbound.2
    _ <= _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass (by positivity : 0 <= (48 : Real)/X^2)) hJ

theorem movingSquareTest_finite_packet_second_profile_moment {I : Type*}
    (A : Finset I) (rho coefficient : I -> Complex)
    {X eta : Real} (hX : 16 <= X) (he : 0 < eta)
    (hrho : forall i, (A : Set I) i -> Not (rho i = 0)) :
    MeasureTheory.IntegrableOn (fun x =>
      norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) <=
      (3*X^2)*(MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4)) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
        (fun y => norm (Finset.sum A (fun i =>
          coefficient i/(rho i)^2*Complex.exp (rho i*(Real.log y : Complex))))^4) := by
  let F : Real -> Complex := fun y =>
    Finset.sum A (fun i =>
      coefficient i/(rho i)^2*Complex.exp (rho i*(Real.log y : Complex)))
  let Z : Real -> Complex := fun x => Finset.sum A (fun i => coefficient i*
    Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
      (Zeta23.gammaOf (rho i)))
  let psi : Real -> Complex := deriv (deriv (logWindowProfile eta))
  let mu : MeasureTheory.Measure Real := MeasureTheory.volume.restrict (Set.Icc X (2*X))
  let nu : MeasureTheory.Measure Real := MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1)
  have hF : ContinuousOn F (Set.Ioi (0 : Real)) := by
    have hlog : ContinuousOn Real.log (Set.Ioi (0 : Real)) :=
      fun y hy => (Real.hasDerivAt_log hy.ne').continuousAt.continuousWithinAt
    apply continuousOn_finsetSum A
    intro i hi
    apply continuousOn_const.mul
    apply Complex.continuous_exp.comp_continuousOn
    apply continuousOn_const.mul
    exact Complex.continuous_ofReal.comp_continuousOn hlog
  have hpsi : Continuous psi :=
    (logWindowProfile_contDiff eta).deriv'.continuous_deriv le_rfl
  have hab : forall v, (Set.Icc (0 : Real) 1) v ->
      -1 <= 0+1*v /\ 0+1*v <= 2 := by
    intro v hv
    constructor <;> linarith [hv.1, hv.2]
  have hbound := movingSquareUnitIntegral_invLogWidth_fourth_moment hX hab
    hpsi.continuousOn hF
  have heq (x : Real) (hx : (Set.Icc X (2*X)) x) :
      Z x = (1/(movingSquareLogWidth x : Complex))*
        movingSquareUnitIntegral 0 1 psi F x := by
    have hx0 : 0 < x := by linarith [hx.1]
    dsimp [Z]
    rw [movingSquareTest_finite_packet_second_integral A rho coefficient he hx0 hrho]
    apply congrArg (fun z : Complex => (1/(movingSquareLogWidth x : Complex))*z)
    change MeasureTheory.integral MeasureTheory.volume
        (fun v => psi v*F (movingSquareMap v x)) =
      MeasureTheory.integral nu (fun v => psi v*F (movingSquareMap (0+1*v) x))
    simp only [zero_add, one_mul]
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hz : psi v = 0 := by
      by_contra h
      exact hv (logWindowProfile_second_tsupport_subset he (subset_closure h))
    rw [hz, zero_mul]
  have heqAE : Filter.Eventually (fun x => norm (Z x)^4 =
      norm ((1/(movingSquareLogWidth x : Complex))*
        movingSquareUnitIntegral 0 1 psi F x)^4) (MeasureTheory.ae mu) := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
    exact Filter.Eventually.of_forall (fun x hx =>
      congrArg (fun z : Complex => norm z^4) (heq x hx))
  have hZi : MeasureTheory.Integrable (fun x => norm (Z x)^4) mu :=
    hbound.1.congr (Filter.Eventually.mono heqAE (fun _ h => h.symm))
  refine And.intro hZi ?_
  calc
    _ = MeasureTheory.integral mu
        (fun x => norm ((1/(movingSquareLogWidth x : Complex))*
          movingSquareUnitIntegral 0 1 psi F x)^4) :=
      MeasureTheory.integral_congr_ae heqAE
    _ <= _ := hbound.2

theorem movingSquareTest_finite_packet_low_energy {I : Type*}
    (A : Finset I) (rho coefficient : I -> Complex)
    {X eta sigma : Real} (hX : 16 <= X) (he : 0 < eta) (hsigma : sigma <= 1)
    (hrho : forall i, (A : Set I) i -> 0 <= (rho i).re /\ (rho i).re <= sigma) :
    MeasureTheory.IntegrableOn (fun x =>
      norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) <=
      (3145728*X^(4*sigma-1))*Finset.sum A (fun i => Finset.sum A (fun j =>
        Finset.sum A (fun k => Finset.sum A (fun l =>
          ((norm (coefficient i)*norm (coefficient j))*
            (norm (coefficient k)*norm (coefficient l))) /
              max 1 (abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im)))))) := by
  let E : Real := Finset.sum A (fun i => Finset.sum A (fun j =>
    Finset.sum A (fun k => Finset.sum A (fun l =>
      ((norm (coefficient i)*norm (coefficient j))*
        (norm (coefficient k)*norm (coefficient l))) /
          max 1 (abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im))))))
  have hZ := movingSquareTest_finite_packet_low_moment A rho coefficient hX he
  have hM := (Complex.integral_norm_fourth_mellin_sum_le_frequency A coefficient rho
    (by linarith : 1 <= X) hsigma hrho).2
  rw [intervalIntegral.integral_of_le (by linarith : X/2 <= 8*X)] at hM
  simp only [<- MeasureTheory.integral_Icc_eq_integral_Ioc] at hM
  have hX0 : 0 < X := by linarith
  have hp := Real.rpow_sub hX0 (1+4*sigma) ((2 : Nat) : Real)
  rw [Real.rpow_natCast] at hp
  have ha : 1+4*sigma-((2 : Nat) : Real) = 4*sigma-1 := by norm_num; ring
  rw [ha] at hp
  have hcoef : (48/X^2)*(65536*X^(1+4*sigma)) = 3145728*X^(4*sigma-1) := by
    rw [hp]
    ring
  refine And.intro hZ.1 ?_
  calc
    _ <= (48/X^2)*MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
        (fun y => norm (Finset.sum A (fun i =>
          coefficient i*Complex.exp (rho i*(Real.log y : Complex))))^4) := hZ.2
    _ <= (48/X^2)*((65536*X^(1+4*sigma))*E) :=
      mul_le_mul_of_nonneg_left hM (div_nonneg (by norm_num) (sq_nonneg X))
    _ = (3145728*X^(4*sigma-1))*E := by rw [<- mul_assoc, hcoef]

theorem movingSquareTest_finite_packet_second_profile_energy {I : Type*}
    (A : Finset I) (rho coefficient : I -> Complex)
    {X eta sigma : Real} (hX : 16 <= X) (he : 0 < eta) (hsigma : sigma <= 1)
    (hrho : forall i, (A : Set I) i -> 0 <= (rho i).re /\ (rho i).re <= sigma)
    (hr : forall i, (A : Set I) i -> Not (rho i = 0)) :
    MeasureTheory.IntegrableOn (fun x =>
      norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) <=
      (196608*X^(3+4*sigma))*(MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4)) *
        Finset.sum A (fun i => Finset.sum A (fun j =>
          Finset.sum A (fun k => Finset.sum A (fun l =>
            ((norm (coefficient i/(rho i)^2)*norm (coefficient j/(rho j)^2))*
              (norm (coefficient k/(rho k)^2)*norm (coefficient l/(rho l)^2))) /
                max 1 (abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im)))))) := by
  let M : Real := MeasureTheory.integral
    (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
    (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4)
  let E : Real := Finset.sum A (fun i => Finset.sum A (fun j =>
    Finset.sum A (fun k => Finset.sum A (fun l =>
      ((norm (coefficient i/(rho i)^2)*norm (coefficient j/(rho j)^2))*
        (norm (coefficient k/(rho k)^2)*norm (coefficient l/(rho l)^2))) /
          max 1 (abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im))))))
  have hZ := movingSquareTest_finite_packet_second_profile_moment A rho coefficient hX he hr
  have hM := (Complex.integral_norm_fourth_mellin_sum_le_frequency A
    (fun i => coefficient i/(rho i)^2) rho (by linarith : 1 <= X) hsigma hrho).2
  rw [intervalIntegral.integral_of_le (by linarith : X/2 <= 8*X)] at hM
  simp only [<- MeasureTheory.integral_Icc_eq_integral_Ioc] at hM
  have hX0 : 0 < X := by linarith
  have hM0 : 0 <= M :=
    MeasureTheory.integral_nonneg (fun v => pow_nonneg (norm_nonneg _) 4)
  have hp := Real.rpow_add hX0 ((2 : Nat) : Real) (1+4*sigma)
  rw [Real.rpow_natCast] at hp
  have ha : ((2 : Nat) : Real)+(1+4*sigma) = 3+4*sigma := by norm_num; ring
  rw [ha] at hp
  have hcoef : ((3*X^2)*M)*((65536*X^(1+4*sigma))*E) =
      (196608*X^(3+4*sigma))*M*E := by
    rw [hp]
    ring
  refine And.intro hZ.1 ?_
  calc
    _ <= ((3*X^2)*M)*MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
        (fun y => norm (Finset.sum A (fun i =>
          coefficient i/(rho i)^2*Complex.exp (rho i*(Real.log y : Complex))))^4) := hZ.2
    _ <= ((3*X^2)*M)*((65536*X^(1+4*sigma))*E) :=
      mul_le_mul_of_nonneg_left hM (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg X)) hM0)
    _ = (196608*X^(3+4*sigma))*M*E := hcoef

end RobinBV.Sieve
