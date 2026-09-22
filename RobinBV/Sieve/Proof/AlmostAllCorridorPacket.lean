/- Copyright (c) 2026 Jonas Whidden. -/
import RobinBV.Sieve.Helpers.SquareCorridorTest
import RobinBV.Sieve.Helpers.SquareIntervalMovingMoment
import RobinBV.Sieve.Proof.SquareIntervalZeroKernel

/-!
# Moving-square corridor packet identities

This module rewrites the inner and outer corridor packets as affine moving
square integrals, retaining the endpoint and width factors used by the
fourth-moment consumers.
-/

set_option autoImplicit false

open MeasureTheory

namespace RobinBV.Sieve

theorem square_corridor_inner_packet_integral
    {I : Type*} (A : Finset I) (rho coefficient : I -> Complex)
    {theta eta x : Real} (htheta : 0 <= theta) (htheta2 : 2*theta < 1)
    (heta : 0 < eta) (hx : 0 < x) :
    Finset.sum A (fun i => coefficient i*
      Zeta23.paperFT (squareCorridorInnerTest theta eta x)
        (Zeta23.gammaOf (rho i))) =
      (((1-2*theta)*movingSquareLogWidth x : Real) : Complex)*
        integral volume (fun v : Real =>
          logWindowProfile eta v *
            Finset.sum A (fun i => coefficient i*
              Complex.exp (rho i *
                (((Real.log x+theta*movingSquareLogWidth x : Real) : Complex) +
                  (((1-2*theta)*movingSquareLogWidth x : Real) : Complex)*v)))) := by
  have hw : 0 < movingSquareLogWidth x := movingSquareLogWidth_pos hx
  have hL : 0 < (1-2*theta)*movingSquareLogWidth x :=
    mul_pos (by linarith) hw
  simpa only [squareCorridorInnerTest] using
    (scaledLogWindowTest_finite_packet_integral A rho coefficient heta hL
      (Real.log x+theta*movingSquareLogWidth x))

theorem square_corridor_outer_packet_integral
    {I : Type*} (A : Finset I) (rho coefficient : I -> Complex)
    {theta eta x : Real} (htheta : 0 <= theta) (heta : 0 < eta) (hx : 0 < x) :
    Finset.sum A (fun i => coefficient i*
      Zeta23.paperFT (squareCorridorOuterTest theta eta x)
        (Zeta23.gammaOf (rho i))) =
      (((1+2*theta)*movingSquareLogWidth x : Real) : Complex)*
        integral volume (fun v : Real =>
          logWindowProfile eta v *
            Finset.sum A (fun i => coefficient i*
              Complex.exp (rho i *
                (((Real.log x-theta*movingSquareLogWidth x : Real) : Complex) +
                  (((1+2*theta)*movingSquareLogWidth x : Real) : Complex)*v)))) := by
  have hw : 0 < movingSquareLogWidth x := movingSquareLogWidth_pos hx
  have hL : 0 < (1+2*theta)*movingSquareLogWidth x :=
    mul_pos (by linarith) hw
  simpa only [squareCorridorOuterTest] using
    (scaledLogWindowTest_finite_packet_integral A rho coefficient heta hL
      (Real.log x-theta*movingSquareLogWidth x))

theorem square_corridor_inner_packet_affine_eq
    {I : Type*} (A : Finset I) (rho coefficient : I -> Complex)
    {theta eta x : Real} (htheta : 0 <= theta) (htheta2 : 2*theta < 1)
    (heta : 0 < eta) (hx : 0 < x) :
    Finset.sum A (fun i => coefficient i*
      Zeta23.paperFT (squareCorridorInnerTest theta eta x)
        (Zeta23.gammaOf (rho i))) =
      ((((1-2*theta)*movingSquareLogWidth x : Real) : Complex) *
        movingSquareUnitIntegral theta (1-2*theta) (logWindowProfile eta)
          (fun y : Real => Finset.sum A (fun i => coefficient i *
            Complex.exp (rho i * (Real.log y : Complex)))) x) := by
  have h := square_corridor_inner_packet_integral A rho coefficient
    htheta htheta2 heta hx
  rw [h]
  congr 1
  unfold movingSquareUnitIntegral
  let G : Real -> Complex := fun v =>
    logWindowProfile eta v *
      (fun y : Real => Finset.sum A (fun i => coefficient i *
        Complex.exp (rho i * (Real.log y : Complex))))
        (movingSquareMap (theta+(1-2*theta)*v) x)
  have hset : integral (volume.restrict (Set.Icc (0 : Real) 1)) G =
      integral volume G := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hz : logWindowProfile eta v = 0 := by
      by_contra hne
      exact hv (logWindowProfile_tsupport_subset heta (subset_closure hne))
    rw [hz, zero_mul]
  symm
  calc
    _ = integral volume G := hset
    _ = _ := by
      apply congrArg (integral volume)
      funext v
      dsimp [G]
      apply congrArg (fun z : Complex => logWindowProfile eta v*z)
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      rw [log_movingSquareMap hx]
      push_cast
      ring

theorem square_corridor_outer_packet_affine_eq
    {I : Type*} (A : Finset I) (rho coefficient : I -> Complex)
    {theta eta x : Real} (htheta : 0 <= theta) (heta : 0 < eta) (hx : 0 < x) :
    Finset.sum A (fun i => coefficient i*
      Zeta23.paperFT (squareCorridorOuterTest theta eta x)
        (Zeta23.gammaOf (rho i))) =
      ((((1+2*theta)*movingSquareLogWidth x : Real) : Complex) *
        movingSquareUnitIntegral (-theta) (1+2*theta) (logWindowProfile eta)
          (fun y : Real => Finset.sum A (fun i => coefficient i *
            Complex.exp (rho i * (Real.log y : Complex)))) x) := by
  have h := square_corridor_outer_packet_integral A rho coefficient
    htheta heta hx
  rw [h]
  congr 1
  unfold movingSquareUnitIntegral
  let G : Real -> Complex := fun v =>
    logWindowProfile eta v *
      (fun y : Real => Finset.sum A (fun i => coefficient i *
        Complex.exp (rho i * (Real.log y : Complex))))
        (movingSquareMap (-theta+(1+2*theta)*v) x)
  have hset : integral (volume.restrict (Set.Icc (0 : Real) 1)) G =
      integral volume G := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hz : logWindowProfile eta v = 0 := by
      by_contra hne
      exact hv (logWindowProfile_tsupport_subset heta (subset_closure hne))
    rw [hz, zero_mul]
  symm
  calc
    _ = integral volume G := hset
    _ = _ := by
      apply congrArg (integral volume)
      funext v
      dsimp [G]
      apply congrArg (fun z : Complex => logWindowProfile eta v*z)
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      rw [log_movingSquareMap hx]
      push_cast
      ring

end RobinBV.Sieve
