import RobinBV.NumberField.Proof.MovingCharacterLevelBridge
import RobinBV.NumberField.Proof.MovingCharacterSecondaryBound
import RobinBV.NumberField.Proof.PrimeMomentTail

/-!
# Complete first-omitted-layer secondary terms

The exact earlier prime moments are removed before the first remaining
layer is identified. Both the finite prime-cap error and every higher
power remain in the complete decomposition and its explicit bounds.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- Removing the exact first m prime moments leaves precisely the full
higher-power integral, not a truncated approximation. -/
theorem movingCharacterCorrection_prefix_eq_higher_integral
    {N : Nat} (chi : DirichletCharacter Complex N) (P m : Nat) (hm : 1 <= m)
    {x : Real} (hx : 3 <= x) (hPm : ((P ^ m : Nat) : Real) <= x) :
    movingCharacterCorrection chi P x +
      Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
        Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
          ((x : Complex) * (Real.log x : Complex)) =
      -integral (volume.restrict (Ioi x)) (fun t : Real =>
        Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p m t) *
          (Robin1984.robinRealWeight 1 t : Complex)) := by
  let B : Complex := Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
    Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j))
  have hxOne : 1 < x := by linarith
  have hWeight := Robin1984.integrableOn_robinRealWeight (n := 1) (by norm_num) hxOne
  have hConst : IntegrableOn (fun t : Real => B * (Robin1984.robinRealWeight 1 t : Complex))
      (Ioi x) := hWeight.ofReal.const_mul B
  have hHigher := (higherCharacterPrimePower_integral_data chi P m hm hxOne).1
  have hConstIntegral : integral (volume.restrict (Ioi x))
      (fun t : Real => B * (Robin1984.robinRealWeight 1 t : Complex)) =
        B / ((x : Complex) * (Real.log x : Complex)) := by
    rw [integral_const_mul, integral_complex_ofReal, Robin1984.integral_robinRealWeight
      (by norm_num : 1 <= (1 : Nat)) hxOne]
    norm_num [Real.rpow_neg_one]
    ring
  have hIntegral : integral (volume.restrict (Ioi x)) (fun t : Real =>
      Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t) *
        (Robin1984.robinRealWeight 1 t : Complex)) =
      B / ((x : Complex) * (Real.log x : Complex)) +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p m t) *
            (Robin1984.robinRealWeight 1 t : Complex)) := by
    rw [<- hConstIntegral, <- integral_add hConst hHigher]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hSum : Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t) =
        B + Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p m t) := by
      calc
        _ = Finset.sum (Nat.primesLE P) (fun p =>
            (Real.log p : Complex) * Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j) +
              chi.primePowerHigherStep p m t) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hPrime := (Nat.mem_primesLE.mp hp).2
          have hLe := (Nat.mem_primesLE.mp hp).1
          have hPower : ((p ^ m : Nat) : Real) <= ((P ^ m : Nat) : Real) := by
            exact_mod_cast Nat.pow_le_pow_left hLe m
          exact chi.primePowerChebyshevStep_eq_prefix_add_higher p m t
            (Nat.le_log_of_pow_le hPrime.one_lt (Nat.le_floor ((hPower.trans hPm).trans ht.le)))
        _ = _ := by rw [Finset.sum_add_distrib]
    rw [hSum, add_mul]
  change movingCharacterCorrection chi P x + B / ((x : Complex) * (Real.log x : Complex)) = _
  unfold movingCharacterCorrection
  rw [hIntegral]
  ring

/-- The first omitted layer is its exact capped root-prime character
moment; the entire higher-layer integral remains explicitly in the identity. -/
theorem movingCharacterCorrection_secondary_identity
    {N : Nat} (chi : DirichletCharacter Complex N) (P m : Nat) (hm : 1 <= m)
    {x : Real} (hx : 3 <= x) (hPm : ((P ^ m : Nat) : Real) <= x) :
    movingCharacterCorrection chi P x +
      Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
        Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
          ((x : Complex) * (Real.log x : Complex)) =
      -cappedRootPrimeCharacterTail (chi ^ (m + 1)) P (Inv.inv ((m + 1 : Nat) : Real)) x -
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p (m + 1) t) *
            (Robin1984.robinRealWeight 1 t : Complex)) := by
  have hxOne : 1 < x := by linarith
  have hCap := (cappedRootPrimeCharacterTail_integral_data (chi ^ (m + 1)) P
    (Inv.inv ((m + 1 : Nat) : Real)) hxOne).1
  have hHigher := (higherCharacterPrimePower_integral_data chi P (m + 1) (by omega) hxOne).1
  rw [movingCharacterCorrection_prefix_eq_higher_integral chi P m hm hx hPm]
  have hIntegral : integral (volume.restrict (Ioi x)) (fun t : Real =>
      Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p m t) *
        (Robin1984.robinRealWeight 1 t : Complex)) =
      cappedRootPrimeCharacterTail (chi ^ (m + 1)) P (Inv.inv ((m + 1 : Nat) : Real)) x +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p (m + 1) t) *
            (Robin1984.robinRealWeight 1 t : Complex)) := by
    unfold cappedRootPrimeCharacterTail
    rw [<- integral_add hCap hHigher]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [chi.sum_primePowerHigherStep_eq_primeMoment_add_higher P m (hxOne.trans ht).le, add_mul]
  rw [hIntegral]
  ring

/-- Complete finite error against the uncapped first-layer tail. The
prime-cap theta term and the entire higher-power tail are both retained. -/
theorem movingCharacterCorrection_secondary_error_le
    {N : Nat} (chi : DirichletCharacter Complex N) (P m : Nat) (hm : 1 <= m)
    {x T : Real} (hx : 3 <= x) (hPm : ((P ^ m : Nat) : Real) <= x)
    (hxT : x <= T) (hCap : T ^ (Inv.inv ((m + 1 : Nat) : Real)) <= (P : Real)) :
    norm (movingCharacterCorrection chi P x +
      Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
        Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
          ((x : Complex) * (Real.log x : Complex)) +
        rootPrimeCharacterTail (chi ^ (m + 1)) (Inv.inv ((m + 1 : Nat) : Real)) x) <=
      ((Real.log 4 + 4) * T ^ (Inv.inv ((m + 1 : Nat) : Real) - 1) /
        ((1 - Inv.inv ((m + 1 : Nat) : Real)) * Real.log T) +
          Chebyshev.theta (P : Real) / (T * Real.log T)) +
      (1 + 1 / Real.log x) / (1 - Inv.inv ((m + 1 + 1 : Nat) : Real)) *
        x ^ (Inv.inv ((m + 1 + 1 : Nat) : Real) - 1) := by
  have hxOne : 1 < x := by linarith
  have hr0 : 0 <= Inv.inv ((m + 1 : Nat) : Real) := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hr1 : Inv.inv ((m + 1 : Nat) : Real) < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le (n := 1) (k := m + 1)
      (by norm_num) (by omega)
  rw [movingCharacterCorrection_secondary_identity chi P m hm hx hPm]
  have hCapBound := norm_rootPrimeCharacterTail_sub_capped_le (chi ^ (m + 1)) P hr0 hr1 hxOne hxT hCap
  have hHigherBound := (higherCharacterPrimePower_integral_data chi P (m + 1) (by omega) hxOne).2
  calc
    _ = norm ((rootPrimeCharacterTail (chi ^ (m + 1)) (Inv.inv ((m + 1 : Nat) : Real)) x -
        cappedRootPrimeCharacterTail (chi ^ (m + 1)) P (Inv.inv ((m + 1 : Nat) : Real)) x) -
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p (m + 1) t) *
              (Robin1984.robinRealWeight 1 t : Complex))) := by congr 1; ring
    _ <= _ := (norm_sub_le _ _).trans (add_le_add hCapBound hHigherBound)

private theorem secondary_power_scale_ratio (P m : Nat) (r : Real) (hP : 0 < (P : Real)) :
    ((P : Real) ^ m) ^ (1 - r) * Real.log ((P : Real) ^ m) =
      ((m : Real) / ((m + 1 : Nat) : Real) * (P : Real) ^ (r - 1)) *
        (((P : Real) ^ (m + 1)) ^ (1 - r) * Real.log ((P : Real) ^ (m + 1))) := by
  rw [Real.log_pow, Real.log_pow]
  simp only [<- Real.rpow_natCast, <- Real.rpow_mul hP.le]
  have hPower : (P : Real) ^ (r - 1) *
      (P : Real) ^ (((m + 1 : Nat) : Real) * (1 - r)) =
        (P : Real) ^ ((m : Real) * (1 - r)) := by
    rw [<- Real.rpow_add hP]
    congr 1
    push_cast
    ring
  have hM : Not (((m + 1 : Nat) : Real) = 0) := by positivity
  calc
    _ = (m : Real) * Real.log P * (P : Real) ^ ((m : Real) * (1 - r)) := by ring
    _ = _ := by rw [<- hPower]; field_simp [hM]

/-- The entire finite-prime cap error vanishes at the first omitted
power scale. No cancellation or fixed-modulus prime estimate is needed. -/
theorem rootPrimeCharacterTail_power_cap_error_tendsto
    {N : Nat} (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m) :
    Tendsto (fun P : Nat =>
      (((((P : Real) ^ m) ^ (1 - Inv.inv ((m + 1 : Nat) : Real)) *
        Real.log ((P : Real) ^ m) : Real) : Complex) *
        (rootPrimeCharacterTail chi (Inv.inv ((m + 1 : Nat) : Real)) ((P : Real) ^ m) -
          cappedRootPrimeCharacterTail chi P (Inv.inv ((m + 1 : Nat) : Real)) ((P : Real) ^ m))))
      atTop (nhds (0 : Complex)) := by
  let r : Real := Inv.inv ((m + 1 : Nat) : Real)
  let K : Real := (Real.log 4 + 4) / (1 - r) + (Real.log 4 + 4)
  let R : Nat -> Real := fun P => (m : Real) / ((m + 1 : Nat) : Real) * (P : Real) ^ (r - 1)
  have hr0 : 0 <= r := by dsimp only [r]; positivity
  have hr1 : r < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le (n := 1) (k := m + 1)
      (by norm_num) (by omega)
  have hPowerLimit : Tendsto (fun P : Nat => (P : Real) ^ (r - 1)) atTop (nhds (0 : Real)) := by
    simpa only [neg_sub, Function.comp_def] using (tendsto_rpow_neg_atTop (sub_pos.mpr hr1)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  have hUpper : Tendsto (fun P : Nat => R P * K) atTop (nhds (0 : Real)) := by
    simpa only [mul_zero, zero_mul] using
      (hPowerLimit.const_mul ((m : Real) / ((m + 1 : Nat) : Real))).mul_const K
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with P hP
  have hPPos : 0 < (P : Real) := by exact_mod_cast (show 0 < P by omega)
  have hPowerGe : P <= P ^ m := by
    have hPositive : 0 < P ^ (m - 1) := Nat.pow_pos (by omega)
    have hIndex : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have hProduct : P ^ m = P ^ (m - 1) * P := by
      calc
        _ = P ^ (m - 1 + 1) := congrArg (fun k : Nat => P ^ k) hIndex.symm
        _ = _ := pow_succ P (m - 1)
    rw [hProduct]
    nlinarith
  have hx : 1 < (P : Real) ^ m := by exact_mod_cast (show 1 < P ^ m by omega)
  have hxT : (P : Real) ^ m <= (P : Real) ^ (m + 1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg hPPos.le m, show (1 : Real) <= P by exact_mod_cast (show 1 <= P by omega)]
  have hCap : ((P : Real) ^ (m + 1)) ^ r = (P : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hPPos.le]
    dsimp only [r]
    rw [show ((m + 1 : Nat) : Real) * Inv.inv ((m + 1 : Nat) : Real) = 1 by field_simp,
      Real.rpow_one]
  have hBound := rootPrimeCharacterTail_cap_error_scaled_le chi P hr0 hr1 hx hxT hCap
  have hR : 0 <= R P := by dsimp only [R]; positivity
  rw [secondary_power_scale_ratio P m r hPPos, Complex.ofReal_mul, mul_assoc, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  exact mul_le_mul_of_nonneg_left hBound hR

/-- The complete first omitted layer in its root-tail normalization.
The first m prime moments are exact; the cap and every higher layer have
been proved negligible, and actual SW supplies the surviving coefficient. -/
theorem movingCharacter_first_omitted_layer_rootScale_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m) :
    Tendsto (fun P : Nat =>
      (((((P : Real) ^ m) ^ (1 - Inv.inv ((m + 1 : Nat) : Real)) *
        Real.log ((P : Real) ^ m) : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (Real.log ((P : Real) ^ m) : Complex)))))
      atTop (nhds (-((if chi ^ (m + 1) = 1 then (1 : Complex) else 0) /
        ((1 - Inv.inv ((m + 1 : Nat) : Real) : Real) : Complex)))) := by
  let r : Real := Inv.inv ((m + 1 : Nat) : Real)
  have hr0 : 0 < r := by dsimp only [r]; positivity
  have hr1 : r < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le (n := 1) (k := m + 1)
      (by norm_num) (by omega)
  have hX : Tendsto (fun P : Nat => (P : Real) ^ m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < m by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  have hHigher : Tendsto (fun P : Nat =>
      (((((P : Real) ^ m) ^ (1 - r) * Real.log ((P : Real) ^ m) : Real) : Complex) *
        integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
          Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p (m + 1) t) *
            (Robin1984.robinRealWeight 1 t : Complex)))) atTop (nhds (0 : Complex)) := by
    apply Metric.tendsto_nhds.mpr
    intro epsilon hEpsilon
    have hs : Inv.inv ((m + 1 + 1 : Nat) : Real) < r := by
      simpa only [one_div] using one_div_lt_one_div_of_lt
        (by positivity : (0 : Real) < ((m + 1 : Nat) : Real))
        (by exact_mod_cast (show m + 1 < m + 1 + 1 by omega))
    have hSmall := higherCharacterPrimePower_uniform_scaled_small (m + 1) (by omega) hs hEpsilon
    filter_upwards [hX.eventually hSmall] with P hSmallP
    simpa only [dist_zero_right] using hSmallP N chi P
  have hRoot := (rootPrimeCharacterTail_normalized_tendsto (chi ^ (m + 1)) hr0 hr1).comp hX
  have hCap := rootPrimeCharacterTail_power_cap_error_tendsto (chi ^ (m + 1)) m hm
  have hResult := (hCap.sub hRoot).sub hHigher
  simp only [zero_sub, sub_zero] at hResult
  apply hResult.congr'
  filter_upwards [hX.eventually (Filter.eventually_ge_atTop (3 : Real))] with P hx
  rw [movingCharacterCorrection_secondary_identity chi P m hm hx
    (by simp only [Nat.cast_pow]; exact le_rfl)]
  dsimp only [Function.comp_def, r]
  simp only [Complex.ofReal_mul]
  ring

/-- Sharp first-omitted-power asymptotic for every complex character and
every positive integer prefix length. All earlier finite prime moments
are retained exactly, so no unproved secondary-scale PNT error is used. -/
theorem movingCharacter_first_omitted_layer_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m) :
    Tendsto (fun P : Nat =>
      ((((P : Real) ^ ((m : Real) ^ 2 / ((m + 1 : Nat) : Real)) * Real.log P : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (m : Complex) * (Real.log P : Complex)))))
      atTop (nhds (-(if chi ^ (m + 1) = 1 then (1 : Complex) else 0) *
        ((m + 1 : Nat) : Complex) / (m : Complex) ^ 2)) := by
  have hM : Not ((m : Complex) = 0) := by exact_mod_cast (show Not (m = 0) by omega)
  have hM1 : Not (((m + 1 : Nat) : Complex) = 0) := by exact_mod_cast Nat.succ_ne_zero m
  have h := (movingCharacter_first_omitted_layer_rootScale_tendsto chi m hm).div_const (m : Complex)
  have hLimit : -((if chi ^ (m + 1) = 1 then (1 : Complex) else 0) /
      ((1 - Inv.inv ((m + 1 : Nat) : Real) : Real) : Complex)) / (m : Complex) =
        -(if chi ^ (m + 1) = 1 then (1 : Complex) else 0) *
          ((m + 1 : Nat) : Complex) / (m : Complex) ^ 2 := by
    push_cast
    field_simp [hM]
    ring
  rw [hLimit] at h
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with P hP
  have hPPos : 0 < (P : Real) := by exact_mod_cast (show 0 < P by omega)
  have hExponent : (m : Real) * (1 - Inv.inv ((m + 1 : Nat) : Real)) =
      (m : Real) ^ 2 / ((m + 1 : Nat) : Real) := by
    push_cast
    field_simp
    ring
  have hScale : ((P : Real) ^ m) ^ (1 - Inv.inv ((m + 1 : Nat) : Real)) *
      Real.log ((P : Real) ^ m) =
        (m : Real) * ((P : Real) ^ ((m : Real) ^ 2 / ((m + 1 : Nat) : Real)) * Real.log P) := by
    rw [Real.log_pow, <- Real.rpow_natCast, <- Real.rpow_mul hPPos.le, hExponent]
    ring
  rw [hScale, Real.log_pow]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp [hM]

/-- The sharp secondary coefficient applies to the actual centered
integral difference at the original and primorial-enlarged lcm levels. -/
theorem centeredCharacter_first_omitted_secondary
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m) :
    Tendsto (fun P : Nat =>
      ((((P : Real) ^ ((m : Real) ^ 2 / ((m + 1 : Nat) : Real)) * Real.log P : Real) : Complex) *
        (centeredCharacterWeightedIntegral
          (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) ((P : Real) ^ m) -
            centeredCharacterWeightedIntegral chi ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (m : Complex) * (Real.log P : Complex)))))
      atTop (nhds (-(if chi ^ (m + 1) = 1 then (1 : Complex) else 0) *
        ((m + 1 : Nat) : Complex) / (m : Complex) ^ 2)) := by
  have hX : Tendsto (fun P : Nat => (P : Real) ^ m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < m by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  apply (movingCharacter_first_omitted_layer_tendsto chi m hm).congr'
  filter_upwards [hX.eventually (Filter.eventually_ge_atTop (3 : Real))] with P hx
  rw [centeredCharacterWeightedIntegral_changeLevel_primorial_sub chi P hx]

end

end RobinBV.NumberField
