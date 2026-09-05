import RobinBV.NumberField.Proof.CharacterRootPrimeERH
import RobinBV.NumberField.Proof.MovingCharacterSecondary

/-!
# Quartic secondary resonance beyond the cubic character error

The first two finite prime moments stay exact. The complete cubic and
quartic layers and every higher power are separated; actual ERH of the
nonprincipal cube supplies the cancellation needed at the quartic scale.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- Exact cubic, quartic and full higher-layer decomposition after
removing the first two admitted finite prime moments. -/
theorem movingCharacterCorrection_quartic_identity
    {N : Nat} (chi : DirichletCharacter Complex N) (P : Nat)
    {x : Real} (hx : 3 <= x) (hP : ((P ^ 2 : Nat) : Real) <= x) :
    movingCharacterCorrection chi P x +
      Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
        Finset.sum (Finset.Icc 1 2) (fun j => chi (p : ZMod N) ^ j)) /
          ((x : Complex) * (Real.log x : Complex)) =
      -cappedRootPrimeCharacterTail (chi ^ 3) P (Inv.inv (3 : Real)) x -
        cappedRootPrimeCharacterTail (chi ^ 4) P (Inv.inv (4 : Real)) x -
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p 4 t) *
              (Robin1984.robinRealWeight 1 t : Complex)) := by
  have hxOne : 1 < x := by linarith
  have hBase := movingCharacterCorrection_secondary_identity chi P 2 (by norm_num) hx hP
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hBase
  simp only [one_div] at hBase
  have hCap := (cappedRootPrimeCharacterTail_integral_data (chi ^ 4) P (Inv.inv (4 : Real)) hxOne).1
  have hHigher := (higherCharacterPrimePower_integral_data chi P 4 (by norm_num) hxOne).1
  have hSplit : integral (volume.restrict (Ioi x)) (fun t : Real =>
      Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p 3 t) *
        (Robin1984.robinRealWeight 1 t : Complex)) =
      cappedRootPrimeCharacterTail (chi ^ 4) P (Inv.inv (4 : Real)) x +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p 4 t) *
            (Robin1984.robinRealWeight 1 t : Complex)) := by
    unfold cappedRootPrimeCharacterTail
    rw [<- integral_add hCap hHigher]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hStep := chi.sum_primePowerHigherStep_eq_primeMoment_add_higher P 3 (hxOne.trans ht).le
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hStep
    simp only [one_div] at hStep
    rw [hStep, add_mul]
  rw [hSplit] at hBase
  exact hBase.trans (by ring)

private theorem quartic_square_normalization (P : Nat) :
    ((P : Real) ^ 2) ^ (1 - Inv.inv (4 : Real)) * Real.log ((P : Real) ^ 2) =
      2 * ((P : Real) ^ (3 / 2 : Real) * Real.log P) := by
  rw [Real.log_pow, <- Real.rpow_natCast, <- Real.rpow_mul (Nat.cast_nonneg P)]
  norm_num
  ring

/-- At the quartic square scale, the full finite prime-cap error is
negligible for every root layer j>=3. Its actual threshold is P^j. -/
theorem rootPrimeCharacterTail_quartic_cap_error_tendsto
    {N : Nat} (chi : DirichletCharacter Complex N) (j : Nat) (hj : 3 <= j) :
    Tendsto (fun P : Nat =>
      (((((P : Real) ^ 2) ^ (1 - Inv.inv (4 : Real)) * Real.log ((P : Real) ^ 2) : Real) : Complex) *
        (rootPrimeCharacterTail chi (Inv.inv (j : Real)) ((P : Real) ^ 2) -
          cappedRootPrimeCharacterTail chi P (Inv.inv (j : Real)) ((P : Real) ^ 2))))
      atTop (nhds (0 : Complex)) := by
  let r : Real := Inv.inv (j : Real)
  let C : Real := (Real.log 4 + 4) / (1 - r) + (Real.log 4 + 4)
  let R : Nat -> Real := fun P => (2 / (j : Real)) * (P : Real) ^ ((5 / 2 : Real) - (j : Real))
  have hjPos : (0 : Real) < j := by exact_mod_cast (show 0 < j by omega)
  have hjReal : (3 : Real) <= j := by exact_mod_cast hj
  have hr0 : 0 <= r := by dsimp only [r]; positivity
  have hr1 : r < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le (n := 1) (k := j)
      (by norm_num) (by omega)
  have hPowerLimit : Tendsto (fun P : Nat => (P : Real) ^ ((5 / 2 : Real) - (j : Real)))
      atTop (nhds (0 : Real)) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (show 0 < (j : Real) - 5 / 2 by linarith)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  have hUpper : Tendsto (fun P : Nat => R P * C) atTop (nhds (0 : Real)) := by
    simpa only [mul_zero, zero_mul] using (hPowerLimit.const_mul (2 / (j : Real))).mul_const C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with P hP
  have hPPos : 0 < (P : Real) := by exact_mod_cast (show 0 < P by omega)
  have hx : 1 < (P : Real) ^ 2 := by exact_mod_cast (show 1 < P ^ 2 by nlinarith)
  have hLeNat : P ^ 2 <= P ^ j := by
    have hPositive : 0 < P ^ (j - 2) := Nat.pow_pos (by omega)
    have hIndex : j - 2 + 2 = j := Nat.sub_add_cancel (show 2 <= j by omega)
    have hProduct : P ^ j = P ^ (j - 2) * P ^ 2 := by
      calc
        _ = P ^ (j - 2 + 2) := congrArg (fun i : Nat => P ^ i) hIndex.symm
        _ = _ := pow_add P (j - 2) 2
    rw [hProduct]
    nlinarith
  have hxT : (P : Real) ^ 2 <= (P : Real) ^ j := by exact_mod_cast hLeNat
  have hCap : ((P : Real) ^ j) ^ r = (P : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hPPos.le]
    dsimp only [r]
    rw [show (j : Real) * Inv.inv (j : Real) = 1 by field_simp, Real.rpow_one]
  have hThresholdPower : ((P : Real) ^ j) ^ (1 - r) = (P : Real) ^ ((j : Real) - 1) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hPPos.le]
    congr 1
    dsimp only [r]
    field_simp [hjPos.ne']
  have hPowers : (P : Real) ^ ((5 / 2 : Real) - (j : Real)) * (P : Real) ^ ((j : Real) - 1) =
      (P : Real) ^ (3 / 2 : Real) := by
    rw [<- Real.rpow_add hPPos]
    congr 1
    ring
  have hNormalize : ((P : Real) ^ 2) ^ (1 - Inv.inv (4 : Real)) * Real.log ((P : Real) ^ 2) =
      R P * (((P : Real) ^ j) ^ (1 - r) * Real.log ((P : Real) ^ j)) := by
    rw [quartic_square_normalization, hThresholdPower, Real.log_pow]
    dsimp only [R]
    rw [<- hPowers]
    field_simp [hjPos.ne']
  have hR : 0 <= R P := by dsimp only [R]; positivity
  have hBound := rootPrimeCharacterTail_cap_error_scaled_le chi P hr0 hr1 hx hxT hCap
  rw [hNormalize, Complex.ofReal_mul, mul_assoc, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hR]
  exact mul_le_mul_of_nonneg_left hBound hR

/-- The complete quartic-scale residual in its root normalization.
Only ERH of the nonprincipal cube is required for the cubic cancellation. -/
theorem movingCharacter_quartic_rootScale_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (hCube : Not (chi ^ 3 = 1)) (hERH : DirichletERH (chi ^ 3)) :
    Tendsto (fun P : Nat =>
      (((((P : Real) ^ 2) ^ (1 - Inv.inv (4 : Real)) * Real.log ((P : Real) ^ 2) : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real) ^ 2) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 2) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ 2 : Real) : Complex) * (Real.log ((P : Real) ^ 2) : Complex)))))
      atTop (nhds (-((if chi ^ 4 = 1 then (1 : Complex) else 0) /
        ((1 - Inv.inv (4 : Real) : Real) : Complex)))) := by
  have hX : Tendsto (fun P : Nat => (P : Real) ^ 2) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < ((2 : Nat) : Real) by norm_num)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  have hCubic := (rootPrimeCharacterTail_scaled_tendsto_of_ERH hCube hERH
    (k := 3) (by norm_num) (s := Inv.inv (4 : Real)) (by norm_num)).comp hX
  have hQuartic := (rootPrimeCharacterTail_normalized_tendsto (chi ^ 4)
    (r := Inv.inv (4 : Real)) (by norm_num) (by norm_num)).comp hX
  have hCapThree := rootPrimeCharacterTail_quartic_cap_error_tendsto (chi ^ 3) 3 (by norm_num)
  have hCapFour := rootPrimeCharacterTail_quartic_cap_error_tendsto (chi ^ 4) 4 (by norm_num)
  have hHigher : Tendsto (fun P : Nat =>
      (((((P : Real) ^ 2) ^ (1 - Inv.inv (4 : Real)) * Real.log ((P : Real) ^ 2) : Real) : Complex) *
        integral (volume.restrict (Ioi ((P : Real) ^ 2))) (fun t : Real =>
          Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p 4 t) *
            (Robin1984.robinRealWeight 1 t : Complex)))) atTop (nhds (0 : Complex)) := by
    apply Metric.tendsto_nhds.mpr
    intro epsilon hEpsilon
    have hSmall := higherCharacterPrimePower_uniform_scaled_small 4 (by norm_num)
      (s := Inv.inv (4 : Real)) (by norm_num) hEpsilon
    filter_upwards [hX.eventually hSmall] with P hSmallP
    simpa only [dist_zero_right] using hSmallP N chi P
  have h := (((hCapThree.add hCapFour).sub hCubic).sub hQuartic).sub hHigher
  simp only [add_zero, sub_zero, zero_sub] at h
  apply h.congr'
  filter_upwards [hX.eventually (Filter.eventually_ge_atTop (3 : Real))] with P hx
  rw [movingCharacterCorrection_quartic_identity chi P hx
    (by simp only [Nat.cast_pow]; exact le_rfl)]
  dsimp only [Function.comp_def]
  simp only [Complex.ofReal_mul]
  ring_nf

/-- Sharp quartic resonance for arbitrary complex characters. After the
first two exact prime moments are removed, ERH of a nonprincipal cube
reveals coefficient -2/3 precisely when the fourth power is principal. -/
theorem movingCharacter_quartic_secondary_of_cubic_ERH
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (hCube : Not (chi ^ 3 = 1)) (hERH : DirichletERH (chi ^ 3)) :
    Tendsto (fun P : Nat =>
      ((((P : Real) ^ (3 / 2 : Real) * Real.log P : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real) ^ 2) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 2) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ 2 : Real) : Complex) * 2 * (Real.log P : Complex)))))
      atTop (nhds (-(2 / 3 : Complex) * (if chi ^ 4 = 1 then (1 : Complex) else 0))) := by
  have h := (movingCharacter_quartic_rootScale_tendsto chi hCube hERH).div_const (2 : Complex)
  have hLimit : -((if chi ^ 4 = 1 then (1 : Complex) else 0) /
      ((1 - Inv.inv (4 : Real) : Real) : Complex)) / 2 =
        -(2 / 3 : Complex) * (if chi ^ 4 = 1 then (1 : Complex) else 0) := by
    split_ifs <;> norm_num
  rw [hLimit] at h
  apply h.congr'
  filter_upwards [] with P
  rw [quartic_square_normalization, Real.log_pow]
  push_cast
  ring

/-- The sharp quartic coefficient belongs to the actual centered
integral difference at the original and primorial-enlarged lcm levels. -/
theorem centeredCharacter_quartic_secondary_of_cubic_ERH
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (hCube : Not (chi ^ 3 = 1)) (hERH : DirichletERH (chi ^ 3)) :
    Tendsto (fun P : Nat =>
      ((((P : Real) ^ (3 / 2 : Real) * Real.log P : Real) : Complex) *
        (centeredCharacterWeightedIntegral
          (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) ((P : Real) ^ 2) -
            centeredCharacterWeightedIntegral chi ((P : Real) ^ 2) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 2) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ 2 : Real) : Complex) * 2 * (Real.log P : Complex)))))
      atTop (nhds (-(2 / 3 : Complex) * (if chi ^ 4 = 1 then (1 : Complex) else 0))) := by
  apply (movingCharacter_quartic_secondary_of_cubic_ERH chi hCube hERH).congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with P hP
  have hx : 3 <= (P : Real) ^ 2 := by exact_mod_cast (show 3 <= P ^ 2 by nlinarith)
  rw [centeredCharacterWeightedIntegral_changeLevel_primorial_sub chi P hx]

end

end RobinBV.NumberField
