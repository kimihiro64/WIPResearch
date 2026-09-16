/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import RobinBV.Sieve.Helpers.LogWindowTest
import RobinBV.Sieve.Helpers.SquareIntervalMovingWidth
import Zeta23.WeilEF.FullLine

/-!
# Uniform all-height zero weights for square windows

Translation and dilation identify each actual Fourier coefficient with
the fixed unit profile. The pinned Zeta23 uniform strip estimate gives
one constant for each fixed taper parameter, independent of the square
interval and zero height. No zero-density or moment estimate is assumed
or proved by this module.
-/

set_option autoImplicit false

open MeasureTheory

namespace RobinBV.Sieve

theorem scaledLogWindowTest_paperFT_integral (eta L c : Real) (rho : Complex) :
    Zeta23.paperFT (scaledLogWindowTest eta L c) (Zeta23.gammaOf rho) =
      MeasureTheory.integral MeasureTheory.volume (fun u : Real =>
        Complex.exp (rho*(u : Complex)) *
          (logWindowCutoff eta ((u-c)/L) : Complex)) := by
  unfold Zeta23.paperFT scaledLogWindowTest Zeta23.gammaOf
  apply congrArg (MeasureTheory.integral MeasureTheory.volume)
  funext u
  have he : Complex.I*((rho-1/2)/Complex.I) = rho-1/2 := by
    field_simp [Complex.I_ne_zero]
  calc
    _ = (Complex.exp ((u : Complex)/2) *
        Complex.exp (Complex.I*((rho-1/2)/Complex.I)*(u : Complex))) *
          (logWindowCutoff eta ((u-c)/L) : Complex) := by ring
    _ = _ := by
      rw [<- Complex.exp_add, he]
      congr 2
      ring

theorem unitLogWindowTest_Hfn_integral (eta : Real) (rho : Complex) :
    Zeta23.WeilEF.Hfn (unitLogWindowTest eta) rho =
      MeasureTheory.integral MeasureTheory.volume (fun u : Real =>
        Complex.exp (rho*(u : Complex)) * (logWindowCutoff eta u : Complex)) := by
  change Zeta23.paperFT (scaledLogWindowTest eta 1 0) (Zeta23.gammaOf rho) = _
  simpa only [sub_zero, div_one] using scaledLogWindowTest_paperFT_integral eta 1 0 rho

theorem scaledLogWindowTest_paperFT_eq {L : Real} (hL : 0 < L)
    (eta c : Real) (rho : Complex) :
    Zeta23.paperFT (scaledLogWindowTest eta L c) (Zeta23.gammaOf rho) =
      (L : Complex)*Complex.exp (rho*(c : Complex)) *
        Zeta23.WeilEF.Hfn (unitLogWindowTest eta) ((L : Complex)*rho) := by
  let q : Real -> Complex := fun v =>
    Complex.exp (rho*((c : Complex)+(L : Complex)*v)) * (logWindowCutoff eta v : Complex)
  have hfun : (fun u : Real => Complex.exp (rho*(u : Complex)) *
      (logWindowCutoff eta ((u-c)/L) : Complex)) =
      fun u : Real => q ((u-c)/L) := by
    funext u
    dsimp [q]
    congr 2
    push_cast
    field_simp [hL.ne']
    ring
  have hq : q = fun v : Real =>
      Complex.exp (rho*(c : Complex)) *
        (Complex.exp (((L : Complex)*rho)*v) * (logWindowCutoff eta v : Complex)) := by
    funext v
    dsimp [q]
    rw [show rho*((c : Complex)+(L : Complex)*v) =
      rho*(c : Complex)+((L : Complex)*rho)*v by ring, Complex.exp_add]
    ring
  rw [scaledLogWindowTest_paperFT_integral, hfun,
    MeasureTheory.integral_sub_right_eq_self (fun u : Real => q (u/L)) c,
    MeasureTheory.Measure.integral_comp_div q L, abs_of_pos hL]
  have hsmul (z : Complex) : HSMul.hSMul L z = (L : Complex)*z := by
    simp [Algebra.smul_def]
  rw [hsmul, hq, Zeta23.EF.cintegral_const_mul,
    <- unitLogWindowTest_Hfn_integral]
  ring

theorem scaledLogWindowTest_uniform_zero_kernel {eta : Real} (he : 0 < eta) :
    exists C : Real, 0 <= C /\ forall L : Real, 0 < L -> L <= 2 ->
      forall c : Real, forall rho : Complex, 0 <= rho.re -> rho.re <= 1 ->
        norm (Zeta23.paperFT (scaledLogWindowTest eta L c) (Zeta23.gammaOf rho)) <=
          C * Real.exp (rho.re*c) * L / (1+(rho.im*L)^2) := by
  choose C hC hbound using Zeta23.WeilEF.norm_Hfn_le
    (unitLogWindowTest_contDiff eta) (unitLogWindowTest_hasCompactSupport he)
  refine Exists.intro C (And.intro hC ?_)
  intro L hL hL2 c rho hb0 hb1
  have hs0 : -1 <= L*rho.re := by nlinarith
  have hs2 : L*rho.re <= 2 := by
    have h := mul_le_mul_of_nonneg_left hb1 hL.le
    linarith
  have hz : (L : Complex)*rho =
      ((L*rho.re : Real) : Complex) + ((L*rho.im : Real) : Complex)*Complex.I := by
    apply Complex.ext <;> simp [mul_comm]
  have h := hbound (L*rho.re) (L*rho.im) hs0 hs2
  rw [<- hz] at h
  rw [scaledLogWindowTest_paperFT_eq hL, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, Complex.norm_exp]
  have hre : (rho*(c : Complex)).re = rho.re*c := by simp
  rw [hre]
  calc
    _ <= (L*Real.exp (rho.re*c)) * (C/(1+(L*rho.im)^2)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [mul_comm L rho.im]; ring

theorem squareIntervalLogTest_uniform_zero_kernel {eta : Real} (he : 0 < eta) :
    exists C : Real, 0 <= C /\ forall n : Nat, 2 <= n ->
      forall rho : Zeta23.zetaZeroConfig.carrier,
        norm (Zeta23.paperFT
          (squareIntervalLogTest n (eta*squareIntervalLogWidth n)) (Zeta23.gammaOf rho)) <=
          C * Real.exp ((rho : Complex).re*Real.log (n*n : Nat)) *
            squareIntervalLogWidth n /
              (1+((rho : Complex).im*squareIntervalLogWidth n)^2) := by
  choose C hC hbound using scaledLogWindowTest_uniform_zero_kernel he
  refine Exists.intro C (And.intro hC ?_)
  intro n hn rho
  have hb := Zeta23.zetaZeroConfig.strip rho rho.property
  rw [squareIntervalLogTest_eq_scaled hn he]
  exact hbound (squareIntervalLogWidth n) (squareIntervalLogWidth_pos hn)
    ((squareIntervalLogWidth_le_one hn).trans (by norm_num)) (Real.log (n*n : Nat))
    rho hb.1 hb.2

theorem movingSquareLogWidth_nat_square {n : Nat} (hn : 2 <= n) :
    movingSquareLogWidth ((n : Real)^2) = squareIntervalLogWidth n := by
  have hn0 : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : (0 : Real) < (n : Real)+1 := by linarith
  have harg : 1+Inv.inv (n : Real) = ((n : Real)+1)/(n : Real) := by
    field_simp [hn0.ne']
  unfold movingSquareLogWidth squareIntervalLogWidth
  rw [Real.sqrt_sq hn0.le, harg]
  push_cast
  rw [Real.log_mul hnp.ne' hnp.ne', Real.log_mul hn0.ne' hn0.ne',
    Real.log_div hnp.ne' hn0.ne']
  ring

theorem unitLogWindowTest_Hfn_eq_profile_paperFT (eta : Real) (s : Complex) :
    Zeta23.WeilEF.Hfn (unitLogWindowTest eta) s =
      Zeta23.paperFT (logWindowProfile eta) (s/Complex.I) := by
  rw [unitLogWindowTest_Hfn_integral, Zeta23.paperFT_def]
  apply congrArg (MeasureTheory.integral MeasureTheory.volume)
  funext u
  have hI : Complex.I*(s/Complex.I) = s := by field_simp
  rw [hI]
  unfold logWindowProfile
  ring

theorem scaledLogWindowTest_finite_packet_integral {I : Type*}
    (A : Finset I) (rho coefficient : I -> Complex)
    {eta L : Real} (he : 0 < eta) (hL : 0 < L) (c : Real) :
    Finset.sum A (fun i => coefficient i*
      Zeta23.paperFT (scaledLogWindowTest eta L c) (Zeta23.gammaOf (rho i))) =
    (L : Complex)*MeasureTheory.integral MeasureTheory.volume (fun v : Real =>
      logWindowProfile eta v * Finset.sum A (fun i => coefficient i*
        Complex.exp (rho i*((c : Complex)+(L : Complex)*v)))) := by
  let q : I -> Real -> Complex := fun i v =>
    logWindowProfile eta v *
      (coefficient i*Complex.exp (rho i*((c : Complex)+(L : Complex)*v)))
  have hq (i : I) : MeasureTheory.Integrable (q i) MeasureTheory.volume := by
    have hE : Continuous (fun v : Real =>
        coefficient i*Complex.exp (rho i*((c : Complex)+(L : Complex)*v))) := by
      apply continuous_const.mul
      apply Complex.continuous_exp.comp
      exact continuous_const.mul (continuous_const.add
        (continuous_const.mul Complex.continuous_ofReal))
    exact ((logWindowProfile_contDiff eta).continuous.mul hE).integrable_of_hasCompactSupport
      (logWindowProfile_hasCompactSupport he).mul_right
  have hterm (i : I) :
      coefficient i*Zeta23.paperFT (scaledLogWindowTest eta L c) (Zeta23.gammaOf (rho i)) =
      (L : Complex)*MeasureTheory.integral MeasureTheory.volume (q i) := by
    rw [scaledLogWindowTest_paperFT_eq hL, unitLogWindowTest_Hfn_integral]
    have hfun : q i = fun v : Real =>
        (coefficient i*Complex.exp (rho i*(c : Complex))) *
          (Complex.exp (((L : Complex)*rho i)*v) * (logWindowCutoff eta v : Complex)) := by
      funext v
      dsimp [q, logWindowProfile]
      rw [show rho i*((c : Complex)+(L : Complex)*v) =
        rho i*(c : Complex)+((L : Complex)*rho i)*v by ring, Complex.exp_add]
      ring
    rw [hfun, Zeta23.integral_const_mul_C]
    ring
  calc
    _ = Finset.sum A (fun i =>
        (L : Complex)*MeasureTheory.integral MeasureTheory.volume (q i)) :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (L : Complex)*Finset.sum A (fun i =>
        MeasureTheory.integral MeasureTheory.volume (q i)) := by rw [Finset.mul_sum]
    _ = (L : Complex)*MeasureTheory.integral MeasureTheory.volume
        (fun v : Real => Finset.sum A (fun i => q i v)) := by
      rw [MeasureTheory.integral_finsetSum A (fun i _ => hq i)]
    _ = _ := by
      apply congrArg (fun z : Complex => (L : Complex)*z)
      apply congrArg (MeasureTheory.integral MeasureTheory.volume)
      funext v
      simp only [q, Finset.mul_sum]

theorem movingSquareTest_finite_packet_integral {I : Type*}
    (A : Finset I) (rho coefficient : I -> Complex)
    {eta x : Real} (he : 0 < eta) (hx : 0 < x) :
    Finset.sum A (fun i => coefficient i*
      Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
        (Zeta23.gammaOf (rho i))) =
    (movingSquareLogWidth x : Complex)*MeasureTheory.integral MeasureTheory.volume
      (fun v : Real => logWindowProfile eta v *
        Finset.sum A (fun i => coefficient i*
          Complex.exp (rho i*(Real.log (movingSquareMap v x) : Complex)))) := by
  rw [scaledLogWindowTest_finite_packet_integral A rho coefficient he
    (movingSquareLogWidth_pos hx)]
  apply congrArg (fun z : Complex => (movingSquareLogWidth x : Complex)*z)
  apply congrArg (MeasureTheory.integral MeasureTheory.volume)
  funext v
  rw [log_movingSquareMap hx, mul_comm v (movingSquareLogWidth x)]
  push_cast
  rfl

theorem logWindowProfile_second_paperFT {eta : Real} (he : 0 < eta) (s : Complex) :
    Zeta23.paperFT (deriv (deriv (logWindowProfile eta))) (s/Complex.I) =
      s^2*Zeta23.WeilEF.Hfn (unitLogWindowTest eta) s := by
  rw [Zeta23.paperFT_deriv_deriv (logWindowProfile_contDiff eta)
    (logWindowProfile_hasCompactSupport he),
    <- unitLogWindowTest_Hfn_eq_profile_paperFT]
  have hI : -(s/Complex.I)^2 = s^2 := by
    rw [div_pow, Complex.I_sq]
    ring
  rw [hI]

theorem scaledLogWindowTest_paperFT_second_profile {eta L : Real}
    (he : 0 < eta) (hL : 0 < L) (c : Real) (rho : Complex) (hr : Not (rho = 0)) :
    Zeta23.paperFT (scaledLogWindowTest eta L c) (Zeta23.gammaOf rho) =
      (1/(L : Complex))*Complex.exp (rho*(c : Complex))/(rho^2) *
        Zeta23.paperFT (deriv (deriv (logWindowProfile eta)))
          (((L : Complex)*rho)/Complex.I) := by
  rw [scaledLogWindowTest_paperFT_eq hL, logWindowProfile_second_paperFT he]
  have hLC : Not ((L : Complex) = 0) := by exact_mod_cast hL.ne'
  field_simp [hLC, hr]

theorem scaledLogWindowTest_finite_packet_second_integral {I : Type*}
    (A : Finset I) (rho coefficient : I -> Complex)
    {eta L : Real} (he : 0 < eta) (hL : 0 < L) (c : Real)
    (hr : forall i, (A : Set I) i -> Not (rho i = 0)) :
    Finset.sum A (fun i => coefficient i*
      Zeta23.paperFT (scaledLogWindowTest eta L c) (Zeta23.gammaOf (rho i))) =
    (1/(L : Complex))*MeasureTheory.integral MeasureTheory.volume (fun v : Real =>
      deriv (deriv (logWindowProfile eta)) v *
        Finset.sum A (fun i => coefficient i/(rho i)^2 *
          Complex.exp (rho i*((c : Complex)+(L : Complex)*v)))) := by
  let q : I -> Real -> Complex := fun i v =>
    deriv (deriv (logWindowProfile eta)) v *
      (coefficient i/(rho i)^2 *
        Complex.exp (rho i*((c : Complex)+(L : Complex)*v)))
  have hphi : Continuous (deriv (deriv (logWindowProfile eta))) :=
    (logWindowProfile_contDiff eta).deriv'.continuous_deriv le_rfl
  have hphis : HasCompactSupport (deriv (deriv (logWindowProfile eta))) :=
    (logWindowProfile_hasCompactSupport he).deriv.deriv
  have hq (i : I) : MeasureTheory.Integrable (q i) MeasureTheory.volume := by
    have hE : Continuous (fun v : Real =>
        coefficient i/(rho i)^2 *
          Complex.exp (rho i*((c : Complex)+(L : Complex)*v))) := by
      apply continuous_const.mul
      apply Complex.continuous_exp.comp
      exact continuous_const.mul (continuous_const.add
        (continuous_const.mul Complex.continuous_ofReal))
    exact (hphi.mul hE).integrable_of_hasCompactSupport hphis.mul_right
  have hterm (i : I) (hi : (A : Set I) i) :
      coefficient i*Zeta23.paperFT (scaledLogWindowTest eta L c) (Zeta23.gammaOf (rho i)) =
      (1/(L : Complex))*MeasureTheory.integral MeasureTheory.volume (q i) := by
    rw [scaledLogWindowTest_paperFT_second_profile he hL c (rho i) (hr i hi)]
    have hfun : q i = fun v : Real =>
        (coefficient i/(rho i)^2 * Complex.exp (rho i*(c : Complex))) *
          (deriv (deriv (logWindowProfile eta)) v *
            Complex.exp (((L : Complex)*rho i)*v)) := by
      funext v
      dsimp [q]
      rw [show rho i*((c : Complex)+(L : Complex)*v) =
        rho i*(c : Complex)+((L : Complex)*rho i)*v by ring, Complex.exp_add]
      ring
    rw [hfun, Zeta23.integral_const_mul_C, Zeta23.paperFT_def]
    have hI : Complex.I*(((L : Complex)*rho i)/Complex.I) = (L : Complex)*rho i := by
      field_simp
    simp only [hI]
    ring
  calc
    _ = Finset.sum A (fun i =>
        (1/(L : Complex))*MeasureTheory.integral MeasureTheory.volume (q i)) :=
      Finset.sum_congr rfl (fun i hi => hterm i hi)
    _ = (1/(L : Complex))*Finset.sum A (fun i =>
        MeasureTheory.integral MeasureTheory.volume (q i)) := by rw [Finset.mul_sum]
    _ = (1/(L : Complex))*MeasureTheory.integral MeasureTheory.volume
        (fun v : Real => Finset.sum A (fun i => q i v)) := by
      rw [MeasureTheory.integral_finsetSum A (fun i _ => hq i)]
    _ = _ := by
      apply congrArg (fun z : Complex => (1/(L : Complex))*z)
      apply congrArg (MeasureTheory.integral MeasureTheory.volume)
      funext v
      simp only [q, Finset.mul_sum]

theorem movingSquareTest_finite_packet_second_integral {I : Type*}
    (A : Finset I) (rho coefficient : I -> Complex)
    {eta x : Real} (he : 0 < eta) (hx : 0 < x)
    (hr : forall i, (A : Set I) i -> Not (rho i = 0)) :
    Finset.sum A (fun i => coefficient i*
      Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
        (Zeta23.gammaOf (rho i))) =
    (1/(movingSquareLogWidth x : Complex))*MeasureTheory.integral MeasureTheory.volume
      (fun v : Real => deriv (deriv (logWindowProfile eta)) v *
        Finset.sum A (fun i => coefficient i/(rho i)^2 *
          Complex.exp (rho i*(Real.log (movingSquareMap v x) : Complex)))) := by
  rw [scaledLogWindowTest_finite_packet_second_integral A rho coefficient he
    (movingSquareLogWidth_pos hx) (Real.log x) hr]
  apply congrArg (fun z : Complex => (1/(movingSquareLogWidth x : Complex))*z)
  apply congrArg (MeasureTheory.integral MeasureTheory.volume)
  funext v
  rw [log_movingSquareMap hx, mul_comm v (movingSquareLogWidth x)]
  push_cast
  rfl

end RobinBV.Sieve
