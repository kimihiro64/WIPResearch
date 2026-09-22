/- Copyright (c) 2026 Jonas Whidden. -/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import RobinBV.Mathlib.Analysis.Complex.FiniteMellinMoment
import RobinBV.Sieve.Helpers.SquareIntervalMovingMoment
import RobinBV.Sieve.Proof.AlmostAllCorridorPacket
import RobinBV.Sieve.Proof.AlmostAllCorridorSummability
import RobinBV.Sieve.Proof.AlmostAllZeroPartition
import RobinBV.Sieve.Proof.ZetaWindowSummability

/-!
# Finite low-real-part corridor fourth moments

The inner and outer packet bounds are obtained from the moving-square moment
consumer with all affine width factors and real-part hypotheses explicit.
The actual inner and outer low-packet consumers below pass a uniform finite
quadruple-frequency bound through the summable finite-subset limit, retaining
the full multiplicity-weighted zero series for both corridor profiles.
-/

set_option autoImplicit false

open MeasureTheory

namespace RobinBV.Sieve

theorem square_corridor_inner_affine_moment
    {I : Type*} (A : Finset I) (rho coefficient : I -> Complex)
    {theta eta X : Real} (hX : 16 <= X) (htheta : 0 <= theta)
    (htheta2 : 2*theta < 1) (heta : 0 < eta) :
    MeasureTheory.IntegrableOn (fun x => norm (
      (movingSquareLogWidth x : Complex) *
        movingSquareUnitIntegral theta (1-2*theta) (logWindowProfile eta)
          (fun y : Real => Finset.sum A (fun i => coefficient i *
            Complex.exp (rho i * (Real.log y : Complex)))) x)^4)
      (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (
        (movingSquareLogWidth x : Complex) *
          movingSquareUnitIntegral theta (1-2*theta) (logWindowProfile eta)
            (fun y : Real => Finset.sum A (fun i => coefficient i *
              Complex.exp (rho i * (Real.log y : Complex)))) x)^4) <=
      (48/X^2) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
          (fun v => norm (logWindowProfile eta v)^4) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
          (fun y => norm (Finset.sum A (fun i => coefficient i *
            Complex.exp (rho i * (Real.log y : Complex))))^4) := by
  have hab : forall v, (Set.Icc (0 : Real) 1) v ->
      -1 <= theta+(1-2*theta)*v /\ theta+(1-2*theta)*v <= 2 := by
    intro v hv
    constructor <;> nlinarith [htheta, htheta2, hv.1, hv.2]
  have hpsi : ContinuousOn (logWindowProfile eta) (Set.Icc (0 : Real) 1) :=
    (logWindowProfile_contDiff eta).continuous.continuousOn
  let F : Real -> Complex := fun y => Finset.sum A (fun i => coefficient i *
    Complex.exp (rho i * (Real.log y : Complex)))
  have hF : ContinuousOn F (Set.Ioi (0 : Real)) := by
    have hlog : ContinuousOn Real.log (Set.Ioi (0 : Real)) :=
      fun y hy => (Real.hasDerivAt_log hy.ne').continuousAt.continuousWithinAt
    apply continuousOn_finsetSum A
    intro i hi
    apply continuousOn_const.mul
    apply Complex.continuous_exp.comp_continuousOn
    apply continuousOn_const.mul
    exact Complex.continuous_ofReal.comp_continuousOn hlog
  simpa only [F] using
    (movingSquareUnitIntegral_logWidth_fourth_moment hX hab hpsi hF)

theorem square_corridor_outer_affine_moment
    {I : Type*} (A : Finset I) (rho coefficient : I -> Complex)
    {theta eta X : Real} (hX : 16 <= X) (htheta : 0 <= theta)
    (htheta4 : 4*theta <= 1) (heta : 0 < eta) :
    MeasureTheory.IntegrableOn (fun x => norm (
      (movingSquareLogWidth x : Complex) *
        movingSquareUnitIntegral (-theta) (1+2*theta) (logWindowProfile eta)
          (fun y : Real => Finset.sum A (fun i => coefficient i *
            Complex.exp (rho i * (Real.log y : Complex)))) x)^4)
      (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (
        (movingSquareLogWidth x : Complex) *
          movingSquareUnitIntegral (-theta) (1+2*theta) (logWindowProfile eta)
            (fun y : Real => Finset.sum A (fun i => coefficient i *
              Complex.exp (rho i * (Real.log y : Complex)))) x)^4) <=
      (48/X^2) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
          (fun v => norm (logWindowProfile eta v)^4) *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
          (fun y => norm (Finset.sum A (fun i => coefficient i *
            Complex.exp (rho i * (Real.log y : Complex))))^4) := by
  have hab : forall v, (Set.Icc (0 : Real) 1) v ->
      -1 <= -theta+(1+2*theta)*v /\ -theta+(1+2*theta)*v <= 2 := by
    intro v hv
    constructor <;> nlinarith [htheta, htheta4, hv.1, hv.2]
  have hpsi : ContinuousOn (logWindowProfile eta) (Set.Icc (0 : Real) 1) :=
    (logWindowProfile_contDiff eta).continuous.continuousOn
  let F : Real -> Complex := fun y => Finset.sum A (fun i => coefficient i *
    Complex.exp (rho i * (Real.log y : Complex)))
  have hF : ContinuousOn F (Set.Ioi (0 : Real)) := by
    have hlog : ContinuousOn Real.log (Set.Ioi (0 : Real)) :=
      fun y hy => (Real.hasDerivAt_log hy.ne').continuousAt.continuousWithinAt
    apply continuousOn_finsetSum A
    intro i hi
    apply continuousOn_const.mul
    apply Complex.continuous_exp.comp_continuousOn
    apply continuousOn_const.mul
    exact Complex.continuous_ofReal.comp_continuousOn hlog
  simpa only [F] using
    (movingSquareUnitIntegral_logWidth_fourth_moment hX hab hpsi hF)

theorem fourth_moment_real_scale_transport
    {X c : Real} {P Q : Real -> Complex} {B : Real}
    (hX : 0 <= X)
    (hEq : forall x, (Set.Icc X (2*X)) x -> P x = (c : Complex)*Q x)
    (hQ : MeasureTheory.IntegrableOn (fun x => norm (Q x)^4)
      (Set.Icc X (2*X)))
    (hB : MeasureTheory.integral
      (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
        (fun x => norm (Q x)^4) <= B) :
    MeasureTheory.IntegrableOn (fun x => norm (P x)^4)
      (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (P x)^4) <= norm (c : Complex)^4*B := by
  have hAE : Filter.Eventually (fun x => norm (P x)^4 =
      norm ((c : Complex)*Q x)^4)
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Icc X (2*X)))) := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
    exact Filter.Eventually.of_forall (fun x hx =>
      congrArg (fun z : Complex => norm z^4) (hEq x hx))
  have hscaled : MeasureTheory.Integrable
      (fun x => norm (c : Complex)^4 * norm (Q x)^4)
      (MeasureTheory.volume.restrict (Set.Icc X (2*X))) :=
    hQ.const_mul _
  have hAE' : Filter.Eventually (fun x =>
      norm (c : Complex)^4 * norm (Q x)^4 = norm (P x)^4)
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Icc X (2*X)))) := by
    filter_upwards [hAE] with x hx
    simpa only [norm_mul, mul_pow] using hx.symm
  have hInt : MeasureTheory.Integrable (fun x => norm (P x)^4)
      (MeasureTheory.volume.restrict (Set.Icc X (2*X))) :=
    hscaled.congr hAE'
  refine And.intro hInt ?_
  calc
    _ = MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
        (fun x => norm ((c : Complex)*Q x)^4) :=
      MeasureTheory.integral_congr_ae hAE
    _ = norm (c : Complex)^4 *
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
          (fun x => norm (Q x)^4) := by
      simp only [norm_mul, mul_pow]
      rw [MeasureTheory.integral_const_mul]
    _ <= _ := mul_le_mul_of_nonneg_left hB (by positivity)

theorem square_corridor_inner_packet_fourth_moment
    {I : Type*} (A : Finset I) (rho coefficient : I -> Complex)
    {theta eta X : Real} (hX : 16 <= X) (htheta : 0 <= theta)
    (htheta2 : 2*theta < 1) (heta : 0 < eta) :
    MeasureTheory.IntegrableOn (fun x => norm (
      Finset.sum A (fun i => coefficient i *
        Zeta23.paperFT (squareCorridorInnerTest theta eta x)
          (Zeta23.gammaOf (rho i))))^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Finset.sum A (fun i => coefficient i *
        Zeta23.paperFT (squareCorridorInnerTest theta eta x)
          (Zeta23.gammaOf (rho i))))^4) <=
      norm (((1-2*theta) : Real) : Complex)^4 *
        ((48/X^2) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (logWindowProfile eta v)^4) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
            (fun y => norm (Finset.sum A (fun i => coefficient i *
              Complex.exp (rho i * (Real.log y : Complex))))^4)) := by
  let P : Real -> Complex := fun x => Finset.sum A (fun i => coefficient i *
    Zeta23.paperFT (squareCorridorInnerTest theta eta x)
      (Zeta23.gammaOf (rho i)))
  let Q : Real -> Complex := fun x => (movingSquareLogWidth x : Complex) *
    movingSquareUnitIntegral theta (1-2*theta) (logWindowProfile eta)
      (fun y : Real => Finset.sum A (fun i => coefficient i *
        Complex.exp (rho i * (Real.log y : Complex)))) x
  have hEq : forall x, (Set.Icc X (2*X)) x ->
      P x = (((1-2*theta) : Real) : Complex) * Q x := by
    intro x hx
    dsimp [P, Q]
    rw [square_corridor_inner_packet_affine_eq (x := x) A rho coefficient htheta htheta2 heta
      (by linarith [hX, hx.1])]
    push_cast
    ring
  have hQ := square_corridor_inner_affine_moment A rho coefficient hX htheta htheta2 heta
  have hT := fourth_moment_real_scale_transport (X := X) (c := 1-2*theta)
    (P := P) (Q := Q) (B := (48/X^2) *
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (logWindowProfile eta v)^4) *
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
        (fun y => norm (Finset.sum A (fun i => coefficient i *
          Complex.exp (rho i * (Real.log y : Complex))))^4))
    (by linarith [hX]) hEq hQ.1 hQ.2
  simpa only [P, Q] using hT

theorem square_corridor_outer_packet_fourth_moment
    {I : Type*} (A : Finset I) (rho coefficient : I -> Complex)
    {theta eta X : Real} (hX : 16 <= X) (htheta : 0 <= theta)
    (htheta4 : 4*theta <= 1) (heta : 0 < eta) :
    MeasureTheory.IntegrableOn (fun x => norm (
      Finset.sum A (fun i => coefficient i *
        Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf (rho i))))^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Finset.sum A (fun i => coefficient i *
        Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf (rho i))))^4) <=
      norm (((1+2*theta) : Real) : Complex)^4 *
        ((48/X^2) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (logWindowProfile eta v)^4) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
            (fun y => norm (Finset.sum A (fun i => coefficient i *
              Complex.exp (rho i * (Real.log y : Complex))))^4)) := by
  let P : Real -> Complex := fun x => Finset.sum A (fun i => coefficient i *
    Zeta23.paperFT (squareCorridorOuterTest theta eta x)
      (Zeta23.gammaOf (rho i)))
  let Q : Real -> Complex := fun x => (movingSquareLogWidth x : Complex) *
    movingSquareUnitIntegral (-theta) (1+2*theta) (logWindowProfile eta)
      (fun y : Real => Finset.sum A (fun i => coefficient i *
        Complex.exp (rho i * (Real.log y : Complex)))) x
  have hEq : forall x, (Set.Icc X (2*X)) x ->
      P x = (((1+2*theta) : Real) : Complex) * Q x := by
    intro x hx
    dsimp [P, Q]
    rw [square_corridor_outer_packet_affine_eq (x := x) A rho coefficient htheta heta
      (by linarith [hX, hx.1])]
    push_cast
    ring
  have hQ := square_corridor_outer_affine_moment A rho coefficient hX htheta htheta4 heta
  have hT := fourth_moment_real_scale_transport (X := X) (c := 1+2*theta)
    (P := P) (Q := Q) (B := (48/X^2) *
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (logWindowProfile eta v)^4) *
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
        (fun y => norm (Finset.sum A (fun i => coefficient i *
          Complex.exp (rho i * (Real.log y : Complex))))^4))
    (by linarith [hX]) hEq hQ.1 hQ.2
  simpa only [P, Q] using hT

theorem square_corridor_inner_packet_low_energy
    {I : Type*} (A : Finset I) (rho coefficient : I -> Complex)
    {theta eta X sigma : Real} (hX : 16 <= X) (htheta : 0 <= theta)
    (htheta2 : 2*theta < 1) (heta : 0 < eta) (hsigma : sigma <= 1)
    (hRe : forall i, (A : Set I) i ->
      0 <= (rho i).re /\ (rho i).re <= sigma) :
    MeasureTheory.IntegrableOn (fun x => norm (
      Finset.sum A (fun i => coefficient i *
        Zeta23.paperFT (squareCorridorInnerTest theta eta x)
          (Zeta23.gammaOf (rho i))))^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Finset.sum A (fun i => coefficient i *
        Zeta23.paperFT (squareCorridorInnerTest theta eta x)
          (Zeta23.gammaOf (rho i))))^4) <=
      norm (((1-2*theta) : Real) : Complex)^4 *
        ((48/X^2) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (logWindowProfile eta v)^4) *
          ((65536*X^(1+4*sigma)) *
            Finset.sum A (fun i => Finset.sum A (fun j =>
              Finset.sum A (fun k => Finset.sum A (fun l =>
                ((norm (coefficient i)*norm (coefficient j))*
                  (norm (coefficient k)*norm (coefficient l))) /
                  max 1 (abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im)))))))) := by
  have hpacket := square_corridor_inner_packet_fourth_moment
    A rho coefficient hX htheta htheta2 heta
  have hM := (Complex.integral_norm_fourth_mellin_sum_le_frequency
    A coefficient rho (by linarith : 1 <= X) hsigma hRe).2
  rw [intervalIntegral.integral_of_le (by linarith : X/2 <= 8*X)] at hM
  simp only [<- MeasureTheory.integral_Icc_eq_integral_Ioc] at hM
  have hX0 : 0 <= X := by linarith
  have hfactor : 0 <=
      norm (((1-2*theta) : Real) : Complex)^4 *
        ((48/X^2) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (logWindowProfile eta v)^4)) := by positivity
  have hscale : 0 <= norm (((1-2*theta) : Real) : Complex)^4 := by
    positivity
  refine And.intro hpacket.1 ?_
  calc
    _ <= norm (((1-2*theta) : Real) : Complex)^4 *
        ((48/X^2) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (logWindowProfile eta v)^4) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
            (fun y => norm (Finset.sum A (fun i =>
              coefficient i * Complex.exp (rho i * (Real.log y : Complex))))^4)) :=
      hpacket.2
    _ <= _ := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hM (by positivity)) hscale

theorem square_corridor_outer_packet_low_energy
    {I : Type*} (A : Finset I) (rho coefficient : I -> Complex)
    {theta eta X sigma : Real} (hX : 16 <= X) (htheta : 0 <= theta)
    (htheta4 : 4*theta <= 1) (heta : 0 < eta) (hsigma : sigma <= 1)
    (hRe : forall i, (A : Set I) i ->
      0 <= (rho i).re /\ (rho i).re <= sigma) :
    MeasureTheory.IntegrableOn (fun x => norm (
      Finset.sum A (fun i => coefficient i *
        Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf (rho i))))^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Finset.sum A (fun i => coefficient i *
        Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf (rho i))))^4) <=
      norm (((1+2*theta) : Real) : Complex)^4 *
        ((48/X^2) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (logWindowProfile eta v)^4) *
          ((65536*X^(1+4*sigma)) *
            Finset.sum A (fun i => Finset.sum A (fun j =>
              Finset.sum A (fun k => Finset.sum A (fun l =>
                ((norm (coefficient i)*norm (coefficient j))*
                  (norm (coefficient k)*norm (coefficient l))) /
                  max 1 (abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im)))))))) := by
  have hpacket := square_corridor_outer_packet_fourth_moment
    A rho coefficient hX htheta htheta4 heta
  have hM := (Complex.integral_norm_fourth_mellin_sum_le_frequency
    A coefficient rho (by linarith : 1 <= X) hsigma hRe).2
  rw [intervalIntegral.integral_of_le (by linarith : X/2 <= 8*X)] at hM
  simp only [<- MeasureTheory.integral_Icc_eq_integral_Ioc] at hM
  have hfactor : 0 <=
      norm (((1+2*theta) : Real) : Complex)^4 *
        ((48/X^2) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (logWindowProfile eta v)^4)) := by positivity
  have hscale : 0 <= norm (((1+2*theta) : Real) : Complex)^4 := by
    positivity
  refine And.intro hpacket.1 ?_
  calc
    _ <= norm (((1+2*theta) : Real) : Complex)^4 *
        ((48/X^2) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (logWindowProfile eta v)^4) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (X/2) (8*X)))
            (fun y => norm (Finset.sum A (fun i =>
              coefficient i * Complex.exp (rho i * (Real.log y : Complex))))^4)) :=
      hpacket.2
    _ <= _ := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hM (by positivity)) hscale

theorem square_corridor_actual_inner_low_energy_from_quadruple
    {sigma Q X theta eta : Real} (hX : 16 <= X) (htheta : 0 <= theta)
    (htheta2 : 2*theta < 1) (heta : 0 < eta)
    (hsigma0 : 79/100 <= sigma) (hsigma1 : sigma <= 1)
    (hQ0 : 0 <= Q)
    (hquad : forall D : Finset Complex,
      (forall z, Membership.mem D z -> Zeta23.IsNontrivialZero z) ->
      (forall z, Membership.mem D z -> 0 <= z.re /\ z.re <= sigma) ->
      Finset.sum D (fun i => Finset.sum D (fun j =>
        Finset.sum D (fun k => Finset.sum D (fun l =>
            ((norm (Zeta23.zeroMult i : Complex)*
              norm (Zeta23.zeroMult j : Complex))*
            (norm (Zeta23.zeroMult k : Complex)*
              norm (Zeta23.zeroMult l : Complex))) /
            max 1 (abs (i.im+j.im-k.im-l.im)))))) <= Q) :
    MeasureTheory.IntegrableOn (fun x => norm (tsum
      (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if (rho : Complex).re <= 79/100 then
          (Zeta23.zeroMult (rho : Complex) : Complex) *
            Zeta23.paperFT (squareCorridorInnerTest theta eta x)
              (Zeta23.gammaOf (rho : Complex)) else 0))^4)
      (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (tsum
        (fun rho : Zeta23.zetaZeroConfig.carrier =>
          if (rho : Complex).re <= 79/100 then
            (Zeta23.zeroMult (rho : Complex) : Complex) *
              Zeta23.paperFT (squareCorridorInnerTest theta eta x)
                (Zeta23.gammaOf (rho : Complex)) else 0))^4) <=
      norm (((1-2*theta) : Real) : Complex)^4 *
        ((48/X^2) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (logWindowProfile eta v)^4) *
          ((65536*X^(1+4*sigma))*Q)) := by
  classical
  let _ : Countable Zeta23.zetaZeroConfig.carrier := zeta_zero_carrier_countable
  let mu : MeasureTheory.Measure Real :=
    MeasureTheory.volume.restrict (Set.Icc X (2*X))
  let B : Real := norm (((1-2*theta) : Real) : Complex)^4 *
    ((48/X^2) *
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (logWindowProfile eta v)^4) *
      ((65536*X^(1+4*sigma))*Q))
  let g : Real -> Zeta23.zetaZeroConfig.carrier -> Complex := fun x rho =>
    if (rho : Complex).re <= 79/100 then
      (Zeta23.zeroMult (rho : Complex) : Complex) *
        Zeta23.paperFT (squareCorridorInnerTest theta eta x)
          (Zeta23.gammaOf (rho : Complex)) else 0
  let F : Finset Zeta23.zetaZeroConfig.carrier -> Real -> Real := fun s x =>
    norm (Finset.sum s (g x))^4
  let G : Real -> Real := fun x => norm (tsum (g x))^4
  have hB0 : 0 <= B := by
    dsimp [B]
    positivity
  have hF0 (s : Finset Zeta23.zetaZeroConfig.carrier) (x : Real) :
      0 <= F s x := pow_nonneg (norm_nonneg _) 4
  have hfin (s : Finset Zeta23.zetaZeroConfig.carrier) :
      MeasureTheory.Integrable (F s) mu /\
      MeasureTheory.integral mu (F s) <= B := by
    let A : Finset Zeta23.zetaZeroConfig.carrier :=
      Finset.filter (fun rho => (rho : Complex).re <= 79/100) s
    let D : Finset Complex := Finset.image
      (fun rho : Zeta23.zetaZeroConfig.carrier => (rho : Complex)) A
    have hD (z : Complex) (hz : Membership.mem D z) :
        Zeta23.IsNontrivialZero z := by
      obtain hm := Finset.mem_image.mp hz
      rw [<- hm.choose_spec.2]
      exact hm.choose.property
    have hbeta (z : Complex) (hz : Membership.mem D z) :
        z.re <= sigma := by
      obtain hm := Finset.mem_image.mp hz
      rw [<- hm.choose_spec.2]
      exact (Finset.mem_filter.mp hm.choose_spec.1).2.trans hsigma0
    have hRe (z : Complex) (hz : Membership.mem D z) :
        0 <= z.re /\ z.re <= sigma := by
      exact And.intro (le_of_lt (hD z hz).2.1) (hbeta z hz)
    have hp := square_corridor_inner_packet_low_energy
      D (fun z : Complex => z) (fun z : Complex => Zeta23.zeroMult z)
      hX htheta htheta2 heta hsigma1 hRe
    have hq := hquad D hD hRe
    have hpacket : MeasureTheory.IntegrableOn (fun x => norm (
        Finset.sum D (fun z => Zeta23.zeroMult z *
          Zeta23.paperFT (squareCorridorInnerTest theta eta x)
            (Zeta23.gammaOf z)))^4) (Set.Icc X (2*X)) /\
      MeasureTheory.integral mu (fun x => norm (
        Finset.sum D (fun z => Zeta23.zeroMult z *
          Zeta23.paperFT (squareCorridorInnerTest theta eta x)
            (Zeta23.gammaOf z)))^4) <= B := by
      refine And.intro hp.1 ?_
      calc
        _ <= norm (((1-2*theta) : Real) : Complex)^4 *
            ((48/X^2) *
              MeasureTheory.integral
                (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
                (fun v => norm (logWindowProfile eta v)^4) *
              ((65536*X^(1+4*sigma)) *
                Finset.sum D (fun i => Finset.sum D (fun j =>
                  Finset.sum D (fun k => Finset.sum D (fun l =>
                    ((norm (Zeta23.zeroMult i : Complex)*
                      norm (Zeta23.zeroMult j : Complex))*
                      (norm (Zeta23.zeroMult k : Complex)*
                        norm (Zeta23.zeroMult l : Complex))) /
                      max 1 (abs (i.im+j.im-k.im-l.im)))))))) := hp.2
        _ <= B := by
          dsimp [B]
          gcongr
    have hsum (x : Real) :
        Finset.sum D (fun z => Zeta23.zeroMult z *
          Zeta23.paperFT (squareCorridorInnerTest theta eta x)
            (Zeta23.gammaOf z)) = Finset.sum s (g x) := by
      calc
        _ = Finset.sum A (fun rho => Zeta23.zeroMult (rho : Complex) *
            Zeta23.paperFT (squareCorridorInnerTest theta eta x)
              (Zeta23.gammaOf (rho : Complex))) :=
          Finset.sum_image (by
            intro a ha b hb hab
            exact Subtype.val_injective hab)
        _ = _ := by
          change Finset.sum
            (Finset.filter
              (fun rho : Zeta23.zetaZeroConfig.carrier =>
                (rho : Complex).re <= 79/100) s)
            (fun rho => Zeta23.zeroMult (rho : Complex) *
              Zeta23.paperFT (squareCorridorInnerTest theta eta x)
                (Zeta23.gammaOf (rho : Complex))) = Finset.sum s (g x)
          rw [Finset.sum_filter]
    have hfin' : MeasureTheory.Integrable (F s) mu /\
        MeasureTheory.integral mu (F s) <= B := by
      exact And.intro (by
        simpa only [F, hsum, mu] using hpacket.1.integrable) (by
        simpa only [F, hsum] using hpacket.2)
    exact hfin'
  have hlim : Filter.Eventually
      (fun x => Filter.Tendsto (fun s : Finset Zeta23.zetaZeroConfig.carrier => F s x)
        Filter.atTop (nhds (G x))) (MeasureTheory.ae mu) := by
    have hmem : Filter.Eventually (fun x => (Set.Icc X (2*X)) x)
        (MeasureTheory.ae mu) := MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem] with x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hsfull := square_corridor_inner_zero_sum_summable
      htheta htheta2 heta hx0
    have hs := (summable_predicate_partition
      (fun rho : Zeta23.zetaZeroConfig.carrier =>
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorInnerTest theta eta x)
            (Zeta23.gammaOf (rho : Complex)))
      (fun rho : Zeta23.zetaZeroConfig.carrier =>
        (rho : Complex).re <= 79/100) hsfull).1
    change Summable (g x) at hs
    have ht := hs.hasSum
    change Filter.Tendsto
      (fun s : Finset Zeta23.zetaZeroConfig.carrier =>
        norm (Finset.sum s (g x))^4) Filter.atTop
      (nhds (norm (tsum (g x))^4))
    exact ht.norm.pow 4
  have hmeas : MeasureTheory.AEStronglyMeasurable G mu :=
    _root_.aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun s => (hfin s).1.aestronglyMeasurable) hlim
  have hG0 : Filter.Eventually (fun x => 0 <= G x) (MeasureTheory.ae mu) :=
    Filter.Eventually.of_forall (fun x => pow_nonneg (norm_nonneg _) 4)
  have hLinEach (s : Finset Zeta23.zetaZeroConfig.carrier) :
      MeasureTheory.lintegral mu (fun x => ENNReal.ofReal (F s x)) <=
        ENNReal.ofReal B := by
    calc
      _ = ENNReal.ofReal (MeasureTheory.integral mu (F s)) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfin s).1
          (Filter.Eventually.of_forall (hF0 s))).symm
      _ <= ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hfin s).2
  have hLin : MeasureTheory.lintegral mu (fun x => ENNReal.ofReal (G x)) <=
      ENNReal.ofReal B := by
    have hFatou := MeasureTheory.lintegral_liminf_le'
      (u := (Filter.atTop : Filter (Finset Zeta23.zetaZeroConfig.carrier)))
      (f := fun s x => ENNReal.ofReal (F s x))
      (fun s => ENNReal.measurable_ofReal.comp_aemeasurable
        (hfin s).1.aestronglyMeasurable.aemeasurable)
    have heq := hlim.mono (fun x hx =>
      ((ENNReal.continuous_ofReal.tendsto (G x)).comp hx).liminf_eq)
    simp only [Function.comp_def] at heq
    rw [MeasureTheory.lintegral_congr_ae heq] at hFatou
    exact hFatou.trans (Filter.liminf_le_of_frequently_le
      (Filter.Eventually.of_forall hLinEach).frequently)
  have hint : MeasureTheory.Integrable G mu := And.intro hmeas
    ((MeasureTheory.hasFiniteIntegral_iff_ofReal hG0).mpr
      (hLin.trans_lt ENNReal.ofReal_lt_top))
  refine And.intro hint ?_
  change MeasureTheory.integral mu G <= B
  apply (ENNReal.ofReal_le_ofReal_iff hB0).mp
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hG0]
  exact hLin

theorem square_corridor_actual_tsum_fourth_moment_of_finite
    {I : Type*} [Countable I] {X B : Real} (hX : 16 <= X)
    (g : Real -> I -> Complex)
    (hfin : forall s : Finset I,
      MeasureTheory.Integrable (fun x => norm (Finset.sum s (g x))^4)
        (MeasureTheory.volume.restrict (Set.Icc X (2*X))) /\
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
        (fun x => norm (Finset.sum s (g x))^4) <= B)
    (hs : forall x, Set.Icc X (2*X) x -> Summable (g x)) :
    MeasureTheory.IntegrableOn (fun x => norm (tsum (g x))^4)
      (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (tsum (g x))^4) <= B := by
  let mu : MeasureTheory.Measure Real :=
    MeasureTheory.volume.restrict (Set.Icc X (2*X))
  let F : Finset I -> Real -> Real := fun s x =>
    norm (Finset.sum s (g x))^4
  let G : Real -> Real := fun x => norm (tsum (g x))^4
  have hF0 (s : Finset I) (x : Real) : 0 <= F s x :=
    pow_nonneg (norm_nonneg _) 4
  have hlim : Filter.Eventually
      (fun x => Filter.Tendsto (fun s : Finset I => F s x)
        Filter.atTop (nhds (G x))) (MeasureTheory.ae mu) := by
    have hmem : Filter.Eventually (fun x => (Set.Icc X (2*X)) x)
        (MeasureTheory.ae mu) := MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem] with x hx
    have ht := (hs x hx).hasSum
    change Filter.Tendsto
      (fun s : Finset I => norm (Finset.sum s (g x))^4) Filter.atTop
      (nhds (norm (tsum (g x))^4))
    exact ht.norm.pow 4
  have hmeas : MeasureTheory.AEStronglyMeasurable G mu :=
    _root_.aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun s => (hfin s).1.aestronglyMeasurable) hlim
  have hG0 : Filter.Eventually (fun x => 0 <= G x) (MeasureTheory.ae mu) :=
    Filter.Eventually.of_forall (fun x => pow_nonneg (norm_nonneg _) 4)
  have hLinEach (s : Finset I) :
      MeasureTheory.lintegral mu (fun x => ENNReal.ofReal (F s x)) <=
        ENNReal.ofReal B := by
    calc
      _ = ENNReal.ofReal (MeasureTheory.integral mu (F s)) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfin s).1
          (Filter.Eventually.of_forall (hF0 s))).symm
      _ <= ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hfin s).2
  have hB0 : 0 <= B := by
    have hnonneg (s : Finset I) :
        0 <= MeasureTheory.integral mu (F s) :=
      MeasureTheory.integral_nonneg (fun x => hF0 s x)
    exact (hnonneg (Finset.empty)).trans (hfin Finset.empty).2
  have hLin : MeasureTheory.lintegral mu (fun x => ENNReal.ofReal (G x)) <=
      ENNReal.ofReal B := by
    have hFatou := MeasureTheory.lintegral_liminf_le'
      (u := (Filter.atTop : Filter (Finset I)))
      (f := fun s x => ENNReal.ofReal (F s x))
      (fun s => ENNReal.measurable_ofReal.comp_aemeasurable
        (hfin s).1.aestronglyMeasurable.aemeasurable)
    have heq := hlim.mono (fun x hx =>
      ((ENNReal.continuous_ofReal.tendsto (G x)).comp hx).liminf_eq)
    simp only [Function.comp_def] at heq
    rw [MeasureTheory.lintegral_congr_ae heq] at hFatou
    exact hFatou.trans (Filter.liminf_le_of_frequently_le
      (Filter.Eventually.of_forall hLinEach).frequently)
  have hint : MeasureTheory.Integrable G mu := And.intro hmeas
    ((MeasureTheory.hasFiniteIntegral_iff_ofReal hG0).mpr
      (hLin.trans_lt ENNReal.ofReal_lt_top))
  refine And.intro hint ?_
  change MeasureTheory.integral mu G <= B
  apply (ENNReal.ofReal_le_ofReal_iff hB0).mp
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hG0]
  exact hLin

theorem square_corridor_actual_outer_low_energy_from_quadruple
    {sigma Q X theta eta : Real} (hX : 16 <= X) (htheta : 0 <= theta)
    (htheta4 : 4*theta <= 1) (heta : 0 < eta)
    (hsigma0 : 79/100 <= sigma) (hsigma1 : sigma <= 1)
    (hQ0 : 0 <= Q)
    (hquad : forall D : Finset Complex,
      (forall z, Membership.mem D z -> Zeta23.IsNontrivialZero z) ->
      (forall z, Membership.mem D z -> 0 <= z.re /\ z.re <= sigma) ->
      Finset.sum D (fun i => Finset.sum D (fun j =>
        Finset.sum D (fun k => Finset.sum D (fun l =>
          ((norm (Zeta23.zeroMult i : Complex)*
              norm (Zeta23.zeroMult j : Complex))*
            (norm (Zeta23.zeroMult k : Complex)*
              norm (Zeta23.zeroMult l : Complex))) /
            max 1 (abs (i.im+j.im-k.im-l.im)))))) <= Q) :
    MeasureTheory.IntegrableOn (fun x => norm (tsum
      (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if (rho : Complex).re <= 79/100 then
          (Zeta23.zeroMult (rho : Complex) : Complex) *
            Zeta23.paperFT (squareCorridorOuterTest theta eta x)
              (Zeta23.gammaOf (rho : Complex)) else 0))^4)
      (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (tsum
        (fun rho : Zeta23.zetaZeroConfig.carrier =>
          if (rho : Complex).re <= 79/100 then
            (Zeta23.zeroMult (rho : Complex) : Complex) *
              Zeta23.paperFT (squareCorridorOuterTest theta eta x)
                (Zeta23.gammaOf (rho : Complex)) else 0))^4) <=
      norm (((1+2*theta) : Real) : Complex)^4 *
        ((48/X^2) *
          MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (logWindowProfile eta v)^4) *
          ((65536*X^(1+4*sigma))*Q)) := by
  classical
  let _ : Countable Zeta23.zetaZeroConfig.carrier := zeta_zero_carrier_countable
  let mu : MeasureTheory.Measure Real :=
    MeasureTheory.volume.restrict (Set.Icc X (2*X))
  let B : Real := norm (((1+2*theta) : Real) : Complex)^4 *
    ((48/X^2) *
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (logWindowProfile eta v)^4) *
      ((65536*X^(1+4*sigma))*Q))
  let g : Real -> Zeta23.zetaZeroConfig.carrier -> Complex := fun x rho =>
    if (rho : Complex).re <= 79/100 then
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf (rho : Complex)) else 0
  have hfin (s : Finset Zeta23.zetaZeroConfig.carrier) :
      MeasureTheory.Integrable (fun x => norm (Finset.sum s (g x))^4) mu /\
      MeasureTheory.integral mu (fun x => norm (Finset.sum s (g x))^4) <= B := by
    let A : Finset Zeta23.zetaZeroConfig.carrier :=
      Finset.filter (fun rho => (rho : Complex).re <= 79/100) s
    let D : Finset Complex := Finset.image
      (fun rho : Zeta23.zetaZeroConfig.carrier => (rho : Complex)) A
    have hD (z : Complex) (hz : Membership.mem D z) :
        Zeta23.IsNontrivialZero z := by
      obtain hm := Finset.mem_image.mp hz
      rw [<- hm.choose_spec.2]
      exact hm.choose.property
    have hbeta (z : Complex) (hz : Membership.mem D z) : z.re <= sigma := by
      obtain hm := Finset.mem_image.mp hz
      rw [<- hm.choose_spec.2]
      exact (Finset.mem_filter.mp hm.choose_spec.1).2.trans hsigma0
    have hRe (z : Complex) (hz : Membership.mem D z) :
        0 <= z.re /\ z.re <= sigma :=
      And.intro (le_of_lt (hD z hz).2.1) (hbeta z hz)
    have hp := square_corridor_outer_packet_low_energy
      D (fun z : Complex => z) (fun z : Complex => Zeta23.zeroMult z)
      hX htheta htheta4 heta hsigma1 hRe
    have hq := hquad D hD hRe
    have hpacket : MeasureTheory.IntegrableOn (fun x => norm (
        Finset.sum D (fun z => Zeta23.zeroMult z *
          Zeta23.paperFT (squareCorridorOuterTest theta eta x)
            (Zeta23.gammaOf z)))^4) (Set.Icc X (2*X)) /\
      MeasureTheory.integral mu (fun x => norm (
        Finset.sum D (fun z => Zeta23.zeroMult z *
          Zeta23.paperFT (squareCorridorOuterTest theta eta x)
            (Zeta23.gammaOf z)))^4) <= B := by
      refine And.intro hp.1 ?_
      calc
        _ <= norm (((1+2*theta) : Real) : Complex)^4 *
            ((48/X^2) *
              MeasureTheory.integral
                (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
                (fun v => norm (logWindowProfile eta v)^4) *
              ((65536*X^(1+4*sigma)) *
                Finset.sum D (fun i => Finset.sum D (fun j =>
                  Finset.sum D (fun k => Finset.sum D (fun l =>
                    ((norm (Zeta23.zeroMult i : Complex)*
                        norm (Zeta23.zeroMult j : Complex))*
                      (norm (Zeta23.zeroMult k : Complex)*
                        norm (Zeta23.zeroMult l : Complex))) /
                      max 1 (abs (i.im+j.im-k.im-l.im)))))))) := hp.2
        _ <= B := by
          dsimp [B]
          gcongr
    have hsum (x : Real) :
        Finset.sum D (fun z => Zeta23.zeroMult z *
          Zeta23.paperFT (squareCorridorOuterTest theta eta x)
            (Zeta23.gammaOf z)) = Finset.sum s (g x) := by
      calc
        _ = Finset.sum A (fun rho => Zeta23.zeroMult (rho : Complex) *
            Zeta23.paperFT (squareCorridorOuterTest theta eta x)
              (Zeta23.gammaOf (rho : Complex))) :=
          Finset.sum_image (by
            intro a ha b hb hab
            exact Subtype.val_injective hab)
        _ = _ := by
          change Finset.sum
            (Finset.filter
              (fun rho : Zeta23.zetaZeroConfig.carrier =>
                (rho : Complex).re <= 79/100) s)
            (fun rho => (Zeta23.zetaZeroConfig.mult rho : Complex) *
              Zeta23.paperFT (squareCorridorOuterTest theta eta x)
                (Zeta23.gammaOf (rho : Complex))) = Finset.sum s (g x)
          rw [Finset.sum_filter]
    exact And.intro (by
      simpa only [g, hsum, mu] using hpacket.1.integrable) (by
      simpa only [g, hsum] using hpacket.2)
  apply square_corridor_actual_tsum_fourth_moment_of_finite hX g hfin
  intro x hx
  have hxlo : X <= x := hx.1
  have hsfull := square_corridor_outer_zero_sum_summable htheta heta (by
    linarith [hX, hxlo])
  have hs := (summable_predicate_partition
    (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf (rho : Complex)))
    (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (rho : Complex).re <= 79/100) hsfull).1
  change Summable (g x) at hs
  simpa only [g, Zeta23.zetaZeroConfig_mult] using hs

theorem square_corridor_hb_exponent_budget_left {sigma : Real}
    (hlo : 1/2 <= sigma) (hhi : sigma <= 2/3) :
    4*sigma-1 + ((10-11*sigma)/(2-sigma))/2 <= 11/4 := by
  have hden : 0 < 2-sigma := by linarith
  have hmul :
      (4*sigma-1 + ((10-11*sigma)/(2-sigma))/2)*(2-sigma) <=
        (11/4)*(2-sigma) := by
    calc
      _ = (4*sigma-1)*(2-sigma) + (10-11*sigma)/2 := by
        field_simp [ne_of_gt hden]
      _ <= _ := by nlinarith
  exact le_of_mul_le_mul_right hmul hden

theorem square_corridor_hb_exponent_budget_middle {sigma : Real}
    (hlo : 2/3 <= sigma) (hhi : sigma <= 3/4) :
    4*sigma-1 + ((18-19*sigma)/(4-2*sigma))/2 <= 11/4 := by
  have hden : 0 < 4-2*sigma := by linarith
  have hden' : 0 < 4-sigma*2 := by linarith
  have hmul :
      (4*sigma-1 + ((18-19*sigma)/(4-2*sigma))/2)*(4-2*sigma) <=
        (11/4)*(4-2*sigma) := by
    calc
      _ = (4*sigma-1)*(4-2*sigma) + (18-19*sigma)/2 := by
        field_simp [ne_of_gt hden, ne_of_gt hden'] <;> ring_nf
      _ <= _ := by nlinarith
  exact le_of_mul_le_mul_right hmul hden

theorem square_corridor_hb_exponent_budget_right {sigma : Real}
    (hlo : 3/4 <= sigma) (hhi : sigma <= 79/100) :
    4*sigma-1 + (12*(1-sigma)/(4*sigma-1))/2 <= 11/4 := by
  have hden : 0 < 4*sigma-1 := by linarith
  have hmul :
      (4*sigma-1 + (12*(1-sigma)/(4*sigma-1))/2)*(4*sigma-1) <=
        (11/4)*(4*sigma-1) := by
    calc
      _ = (4*sigma-1)^2 + 12*(1-sigma)/2 := by
        field_simp [ne_of_gt hden]
      _ <= _ := by nlinarith
  exact le_of_mul_le_mul_right hmul hden

noncomputable def square_corridor_hb_exponent (sigma : Real) : Real :=
  if sigma <= 2/3 then
    4*sigma-1 + ((10-11*sigma)/(2-sigma))/2
  else if sigma <= 3/4 then
    4*sigma-1 + ((18-19*sigma)/(4-2*sigma))/2
  else
    4*sigma-1 + (12*(1-sigma)/(4*sigma-1))/2

theorem square_corridor_hb_exponent_budget {sigma : Real}
    (hlo : 1/2 <= sigma) (hhi : sigma <= 79/100) :
    square_corridor_hb_exponent sigma <= 11/4 := by
  unfold square_corridor_hb_exponent
  by_cases hleft : sigma <= 2/3
  next =>
    rw [if_pos hleft]
    exact square_corridor_hb_exponent_budget_left hlo hleft
  next =>
    by_cases hmiddle : sigma <= 3/4
    next =>
      rw [if_neg hleft, if_pos hmiddle]
      exact square_corridor_hb_exponent_budget_middle (le_of_not_ge hleft) hmiddle
    next =>
      rw [if_neg hleft, if_neg hmiddle]
      exact square_corridor_hb_exponent_budget_right
        (le_of_not_ge hmiddle) hhi

theorem square_corridor_ivic_gap
    {sigma delta eta0 : Real}
    (hdelta : 0 < delta) (heta0 : 0 < eta0)
    (hsigma_lo : 11/14 + delta <= sigma)
    (hsigma_hi : sigma <= 1 - eta0) :
    (7*delta*eta0/3)*(7*sigma-1) <=
      (1-sigma)*(14*sigma-11) := by
  have hsig : 0 < 7*sigma-1 := by
    linarith
  have hone : 0 <= 1-sigma := by
    have : eta0 <= 1-sigma := by linarith
    exact le_trans (le_of_lt heta0) this
  have hden_le : 7*sigma-1 <= 6 := by
    have hsigma_le : sigma <= 1 := by linarith
    linarith
  have hdelta_factor : 14*delta <= 14*sigma-11 := by
    linarith
  have hprod : 14*delta*eta0 <= (1-sigma)*(14*sigma-11) := by
    calc
      14*delta*eta0 <= 14*delta*(1-sigma) := by
        apply mul_le_mul_of_nonneg_left
        next => linarith
        next => positivity
      _ <= (1-sigma)*(14*sigma-11) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hdelta_factor hone
  have hcoef : 0 <= 7*delta*eta0/3 := by positivity
  have hleft : (7*delta*eta0/3)*(7*sigma-1) <=
      14*delta*eta0 := by
    calc
      (7*delta*eta0/3)*(7*sigma-1) <=
          (7*delta*eta0/3)*6 :=
        mul_le_mul_of_nonneg_left hden_le hcoef
      _ = 14*delta*eta0 := by ring
  exact hleft.trans hprod

theorem square_corridor_fixed_sigma_power_mass
    {S : Finset Real} {X C T sigma f : Real}
    (hX : 1 <= X)
    (hcount : (S.card : Real) <= C * T ^ f)
    (hbeta : forall beta, Membership.mem S beta -> beta <= sigma) :
    Finset.sum S (fun beta => X ^ (beta - 1/2)) <=
      C * T ^ f * X ^ (sigma - 1/2) := by
  have hpoint : forall beta, Membership.mem S beta ->
      X ^ (beta - 1/2) <= X ^ (sigma - 1/2) := by
    intro beta hmem
    exact Real.rpow_le_rpow_of_exponent_le hX (by linarith [hbeta beta hmem])
  calc
    Finset.sum S (fun beta => X ^ (beta - 1/2)) <=
        Finset.sum S (fun _ => X ^ (sigma - 1/2)) := by
      exact Finset.sum_le_sum (fun beta hmem => hpoint beta hmem)
    _ = (S.card : Real) * X ^ (sigma - 1/2) := by simp
    _ <= C * T ^ f * X ^ (sigma - 1/2) := by
      exact mul_le_mul_of_nonneg_right hcount
        (Real.rpow_nonneg (by linarith : 0 <= X) _)

end RobinBV.Sieve
