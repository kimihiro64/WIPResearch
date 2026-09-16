/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.UnitScaleEnergy
import RobinBV.Sieve.Assembly.SquareIntervalZeroMoment
import RobinBV.Sieve.Proof.ZetaLocalEnergy

/-!
# Unit-scale energy consumers for finite square-window zero packets

The complete reciprocal-frequency majorant is bounded by weighted unit-scale
energy. The high-height theorem also removes every inverse-square zero weight
using the lower height bound, retaining both signs of the imaginary part.
The final two theorems substitute an unconditional multiplicity-weighted local
zero-energy bound for actual zeros with real part at most one half. Constants
are existential, and the conclusions are finite-packet moments; an infinite
zero sum or a full prime-count theorem is not asserted here.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem movingSquareTest_finite_packet_low_unit_energy {I : Type*}
    (A : Finset I) (rho coefficient : I -> Complex)
    {X eta sigma T : Real} (hX : 16 <= X) (he : 0 < eta) (hsigma : sigma <= 1)
    (hrho : forall i, (A : Set I) i -> 0 <= (rho i).re /\ (rho i).re <= sigma)
    (hT : 1 <= T) (hheight : forall i, (A : Set I) i -> abs (rho i).im <= T) :
    MeasureTheory.IntegrableOn (fun x =>
      norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) <=
      (3145728*X^(4*sigma-1))*(5+2*Real.log (4*T+2))*
        Finset.sum A (fun i => Finset.sum A (fun j =>
          Finset.sum A (fun k => Finset.sum A (fun l =>
            if abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im) <= 1
            then (norm (coefficient i)*norm (coefficient j))*
              (norm (coefficient k)*norm (coefficient l)) else 0)))) := by
  have hZ := movingSquareTest_finite_packet_low_energy A rho coefficient hX he hsigma hrho
  have hE := Real.sum_quadruple_reciprocal_frequency_le_unit_scale A
    (fun i => (rho i).im) (fun i => norm (coefficient i))
    (fun i _ => norm_nonneg _) hT hheight
  have hC : 0 <= 3145728*X^(4*sigma-1) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
  refine And.intro hZ.1 ?_
  simpa only [mul_assoc] using hZ.2.trans (mul_le_mul_of_nonneg_left hE hC)

theorem movingSquareTest_finite_packet_high_height_unit_energy {I : Type*}
    (A : Finset I) (rho coefficient : I -> Complex)
    {X eta sigma T : Real} (hX : 16 <= X) (he : 0 < eta) (hsigma : sigma <= 1)
    (hrho : forall i, (A : Set I) i -> 0 <= (rho i).re /\ (rho i).re <= sigma)
    (hT : 1 <= T)
    (hheight : forall i, (A : Set I) i -> T <= abs (rho i).im /\ abs (rho i).im <= 2*T) :
    MeasureTheory.IntegrableOn (fun x =>
      norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) (Set.Icc X (2*X)) /\
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Finset.sum A (fun i => coefficient i*
        Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
          (Zeta23.gammaOf (rho i))))^4) <=
      ((196608*X^(3+4*sigma))*(MeasureTheory.integral
        (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
        (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4)) *
        (5+2*Real.log (8*T+2))/T^8) *
        Finset.sum A (fun i => Finset.sum A (fun j =>
          Finset.sum A (fun k => Finset.sum A (fun l =>
            if abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im) <= 1
            then (norm (coefficient i)*norm (coefficient j))*
              (norm (coefficient k)*norm (coefficient l)) else 0)))) := by
  let M : Real := MeasureTheory.integral
    (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
    (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4)
  let E : Real := Finset.sum A (fun i => Finset.sum A (fun j =>
    Finset.sum A (fun k => Finset.sum A (fun l =>
      if abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im) <= 1
      then (norm (coefficient i)*norm (coefficient j))*
        (norm (coefficient k)*norm (coefficient l)) else 0))))
  let E2 : Real := Finset.sum A (fun i => Finset.sum A (fun j =>
    Finset.sum A (fun k => Finset.sum A (fun l =>
      if abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im) <= 1
      then (norm (coefficient i/(rho i)^2)*norm (coefficient j/(rho j)^2))*
        (norm (coefficient k/(rho k)^2)*norm (coefficient l/(rho l)^2)) else 0))))
  have hT0 : 0 < T := by linarith
  have hr : forall i, (A : Set I) i -> Not (rho i = 0) := by
    intro i hi hz
    have hh := (hheight i hi).1
    rw [hz, Complex.zero_im, abs_zero] at hh
    linarith
  have hweight (i : I) (hi : (A : Set I) i) :
      norm (coefficient i/(rho i)^2) <= norm (coefficient i)/T^2 := by
    have hN : T <= norm (rho i) :=
      (hheight i hi).1.trans (Complex.abs_im_le_norm _)
    have hs : T^2 <= norm (rho i)^2 := by
      simpa only [pow_two] using mul_le_mul hN hN hT0.le (norm_nonneg _)
    rw [norm_div, norm_pow]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hT0) hs
  have hE2 : E2 <= E/T^8 := by
    calc
      _ <= Finset.sum A (fun i => Finset.sum A (fun j =>
          Finset.sum A (fun k => Finset.sum A (fun l =>
            (if abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im) <= 1
            then (norm (coefficient i)*norm (coefficient j))*
              (norm (coefficient k)*norm (coefficient l)) else 0)/T^8)))) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro l hl
        by_cases hd : abs ((rho i).im+(rho j).im-(rho k).im-(rho l).im) <= 1
        next =>
          rw [if_pos hd, if_pos hd]
          have hij := mul_le_mul (hweight i hi) (hweight j hj) (norm_nonneg _)
            (div_nonneg (norm_nonneg _) (sq_nonneg T))
          have hkl := mul_le_mul (hweight k hk) (hweight l hl) (norm_nonneg _)
            (div_nonneg (norm_nonneg _) (sq_nonneg T))
          calc
            _ <= ((norm (coefficient i)/T^2)*(norm (coefficient j)/T^2))*
                ((norm (coefficient k)/T^2)*(norm (coefficient l)/T^2)) :=
              mul_le_mul hij hkl (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                (mul_nonneg (div_nonneg (norm_nonneg _) (sq_nonneg T))
                  (div_nonneg (norm_nonneg _) (sq_nonneg T)))
            _ = _ := by ring
        next =>
          simp only [if_neg hd, zero_div, le_refl]
      _ = E/T^8 := by simp only [<- Finset.sum_div]; rfl
  have hZ := movingSquareTest_finite_packet_second_profile_energy
    A rho coefficient hX he hsigma hrho hr
  have hUE := Real.sum_quadruple_reciprocal_frequency_le_unit_scale A
    (fun i => (rho i).im) (fun i => norm (coefficient i/(rho i)^2))
    (fun i _ => norm_nonneg _) (by linarith : 1 <= 2*T)
    (fun i hi => (hheight i hi).2)
  rw [show 4*(2*T)+2 = 8*T+2 by ring] at hUE
  have hM0 : 0 <= M := MeasureTheory.integral_nonneg
    (fun v => pow_nonneg (norm_nonneg _) 4)
  have hC : 0 <= (196608*X^(3+4*sigma))*M :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)) hM0
  have hL : 0 <= 5+2*Real.log (8*T+2) := by
    have hlog := Real.log_nonneg (by linarith : 1 <= 8*T+2)
    linarith
  refine And.intro hZ.1 ?_
  calc
    _ <= ((196608*X^(3+4*sigma))*M)*((5+2*Real.log (8*T+2))*E2) :=
      hZ.2.trans (mul_le_mul_of_nonneg_left hUE hC)
    _ <= ((196608*X^(3+4*sigma))*M)*((5+2*Real.log (8*T+2))*(E/T^8)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE2 hL) hC
    _ = _ := by ring

theorem movingSquareTest_actual_left_zero_low_moment :
    Exists fun C : Real => 1 <= C /\
      forall X eta T : Real, 16 <= X -> 0 < eta -> 1 <= T ->
      forall A : Finset Complex,
      (forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) ->
      (forall rho, (A : Set Complex) rho -> rho.re <= 1/2) ->
      (forall rho, (A : Set Complex) rho -> abs rho.im <= T) ->
      MeasureTheory.IntegrableOn (fun x =>
        norm (Finset.sum A (fun rho => (Zeta23.zeroMult rho : Complex)*
          Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
            (Zeta23.gammaOf rho)))^4) (Set.Icc X (2*X)) /\
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
        (fun x => norm (Finset.sum A (fun rho => (Zeta23.zeroMult rho : Complex)*
          Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
            (Zeta23.gammaOf rho)))^4) <=
        8257536000*C^4*X*T^3*(Real.log (8*T))^5 := by
  obtain h := zeta_unit_energy_log_bound
  let C : Real := h.choose
  have hC1 : 1 <= C := h.choose_spec.1
  have hC0 : 0 <= C := by linarith
  refine Exists.intro C (And.intro hC1 ?_)
  intro X eta T hX he hT A hA hbeta hh
  let L : Real := Real.log (8*T)
  have hL1 : 1 <= L := by
    calc
      (1 : Real) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ <= L := Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have hL0 : 0 <= L := by linarith
  have hT0 : 0 <= T := by linarith
  have hX0 : 0 <= X := by linarith
  have hF0 : 0 <= 5+2*Real.log (4*T+2) := by
    have hl := Real.log_nonneg (by linarith : 1 <= 4*T+2)
    linarith
  have hF : 5+2*Real.log (4*T+2) <= 7*L := by
    have hl : Real.log (4*T+2) <= L :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hnorm (rho : Complex) : norm (Zeta23.zeroMult rho : Complex) =
      (Zeta23.zeroMult rho : Real) := by simp
  have hZ := movingSquareTest_finite_packet_low_unit_energy A
    (fun rho : Complex => rho) (fun rho => (Zeta23.zeroMult rho : Complex))
    hX he (by norm_num : (1/2 : Real) <= 1)
    (fun rho hr => And.intro (hA rho hr).2.1.le (hbeta rho hr)) hT hh
  simp only [hnorm] at hZ
  rw [show 4*(1/2 : Real)-1 = 1 by norm_num, Real.rpow_one] at hZ
  have hE := h.choose_spec.2 T hT A hA hh
  have hB0 : 0 <= 375*C^4*T^3*L^4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC0 4))
      (pow_nonneg hT0 3)) (pow_nonneg hL0 4)
  refine And.intro hZ.1 ?_
  calc
    _ <= (3145728*X)*(5+2*Real.log (4*T+2))*(375*C^4*T^3*L^4) :=
      hZ.2.trans (mul_le_mul_of_nonneg_left hE
        (mul_nonneg (mul_nonneg (by norm_num) hX0) hF0))
    _ <= (3145728*X)*(7*L)*(375*C^4*T^3*L^4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hF (mul_nonneg (by norm_num) hX0)) hB0
    _ = _ := by dsimp [L]; ring

theorem movingSquareTest_actual_left_zero_high_moment :
    Exists fun C : Real => 1 <= C /\
      forall X eta T : Real, 16 <= X -> 0 < eta -> 1 <= T ->
      forall A : Finset Complex,
      (forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) ->
      (forall rho, (A : Set Complex) rho -> rho.re <= 1/2) ->
      (forall rho, (A : Set Complex) rho -> T <= abs rho.im /\ abs rho.im <= 2*T) ->
      MeasureTheory.IntegrableOn (fun x =>
        norm (Finset.sum A (fun rho => (Zeta23.zeroMult rho : Complex)*
          Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
            (Zeta23.gammaOf rho)))^4) (Set.Icc X (2*X)) /\
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
        (fun x => norm (Finset.sum A (fun rho => (Zeta23.zeroMult rho : Complex)*
          Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
            (Zeta23.gammaOf rho)))^4) <=
        4128768000*C^4*(MeasureTheory.integral
          (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
          (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4))*
          X^5/T^5*(Real.log (16*T))^5 := by
  obtain h := zeta_unit_energy_log_bound
  let C : Real := h.choose
  have hC1 : 1 <= C := h.choose_spec.1
  have hC0 : 0 <= C := by linarith
  refine Exists.intro C (And.intro hC1 ?_)
  intro X eta T hX he hT A hA hbeta hh
  let M : Real := MeasureTheory.integral
    (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
    (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4)
  let L : Real := Real.log (16*T)
  have hL1 : 1 <= L := by
    calc
      (1 : Real) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ <= L := Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have hL0 : 0 <= L := by linarith
  have hT0 : 0 < T := by linarith
  have hTn : Not (T = 0) := ne_of_gt hT0
  have hX0 : 0 <= X := by linarith
  have hM0 : 0 <= M := MeasureTheory.integral_nonneg
    (fun v => pow_nonneg (norm_nonneg _) 4)
  have hF0 : 0 <= 5+2*Real.log (8*T+2) := by
    have hl := Real.log_nonneg (by linarith : 1 <= 8*T+2)
    linarith
  have hF : 5+2*Real.log (8*T+2) <= 7*L := by
    have hl : Real.log (8*T+2) <= L :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hnorm (rho : Complex) : norm (Zeta23.zeroMult rho : Complex) =
      (Zeta23.zeroMult rho : Real) := by simp
  have hZ := movingSquareTest_finite_packet_high_height_unit_energy A
    (fun rho : Complex => rho) (fun rho => (Zeta23.zeroMult rho : Complex))
    hX he (by norm_num : (1/2 : Real) <= 1)
    (fun rho hr => And.intro (hA rho hr).2.1.le (hbeta rho hr)) hT hh
  simp only [hnorm] at hZ
  have hpow : X^(3+4*(1/2 : Real)) = X^5 := by norm_num
  rw [hpow] at hZ
  have hE := h.choose_spec.2 (2*T) (by linarith) A hA
    (fun rho hr => (hh rho hr).2)
  rw [show 8*(2*T) = 16*T by ring] at hE
  have hB0 : 0 <= 375*C^4*(2*T)^3*L^4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC0 4))
      (pow_nonneg (by linarith : 0 <= 2*T) 3)) (pow_nonneg hL0 4)
  have hK0 : 0 <= (196608*X^5)*M :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hX0 5)) hM0
  refine And.intro hZ.1 ?_
  calc
    _ <= ((196608*X^5)*M*(5+2*Real.log (8*T+2))/T^8)*
        (375*C^4*(2*T)^3*L^4) :=
      hZ.2.trans (mul_le_mul_of_nonneg_left hE
        (div_nonneg (mul_nonneg hK0 hF0) (pow_nonneg hT0.le 8)))
    _ <= ((196608*X^5)*M*(7*L)/T^8)*(375*C^4*(2*T)^3*L^4) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF hK0)
          (pow_nonneg hT0.le 8)) hB0
    _ = _ := by dsimp [L, M]; field_simp [hTn]; ring

end RobinBV.Sieve
