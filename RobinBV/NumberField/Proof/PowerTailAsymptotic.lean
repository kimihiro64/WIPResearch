import Robin1984.NicolasLandau.WeightedPrimePowerTail

/-!
# Signed power-tail secondary terms for the actual Robin weight

The exact unconditional Robin kernel split and integration-by-parts
recurrence are reused from Robin1984 at
2a74ac5c912cebf839bd3bf908249201eb62eb2d. The complete next logarithmic
tail is retained with its correct sign. No RH-dependent root-psi bound is
used. This supplies the model integral for the first omitted prime layer.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set

noncomputable section

private theorem cpowLogTail_real_two (r : Real) {x : Real} (hx : 1 < x) :
    Robin1984.robinCpowLogTail ((r : Complex) - 1) 2 x =
      ((integral (volume.restrict (Ioi x)) (fun t : Real =>
        t ^ (r - 2) * Inv.inv ((Real.log t) ^ 2)) : Real) : Complex) := by
  unfold Robin1984.robinCpowLogTail
  rw [<- integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have htPos : 0 < t := lt_trans Real.zero_lt_one (hx.trans ht)
  rw [Complex.ofReal_mul, Complex.ofReal_cpow htPos.le]
  congr 2
  push_cast
  ring

/-- Exact signed secondary identity for every subcritical real exponent.
The full remaining logarithmic tail is part of the identity. -/
theorem robinPowerTail_secondary_identity
    {r x : Real} (hr : r < 1) (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t) =
      x ^ (r - 1) / ((1 - r) * Real.log x) -
        r / (1 - r) * integral (volume.restrict (Ioi x))
          (fun t : Real => t ^ (r - 2) * Inv.inv ((Real.log t) ^ 2)) := by
  have hRe : (r : Complex).re < ((1 : Nat) : Real) := by simpa using hr
  have ha : ((r : Complex) - 1).re < 0 := by simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]; linarith
  have hKernel := Robin1984.robinZeroKernel_eq_nat_mul_tail_one_add_tail_two hx hRe
  norm_num only [Nat.cast_one, one_mul] at hKernel
  rw [Robin1984.robinCpowLogTail_recurrence hx ha 1] at hKernel
  norm_num only [Nat.cast_one, one_mul, pow_one, Nat.reduceAdd] at hKernel
  have hPower : (x : Complex) ^ ((r : Complex) - 1) = (x ^ (r - 1) : Real) := by
    rw [show (r : Complex) - 1 = ((r - 1 : Real) : Complex) by push_cast; rfl]
    exact (Complex.ofReal_cpow (by linarith : 0 <= x) (r - 1)).symm
  rw [hPower, cpowLogTail_real_two r hx] at hKernel
  rw [show (r : Complex) - 1 = ((r - 1 : Real) : Complex) by push_cast; rfl] at hKernel
  rw [Robin1984.integral_rpow_mul_robinRealWeight 1 r hx, hKernel]
  simp only [<- Complex.ofReal_inv, <- Complex.ofReal_neg, <- Complex.ofReal_mul,
    <- Complex.ofReal_add, Complex.ofReal_re]
  field_simp [show Not (r - 1 = 0) by linarith, show Not (1 - r = 0) by linarith]
  ring

/-- For a nonnegative subcritical exponent, the entire signed residual
lies between zero and an explicit inverse-logarithmic improvement. -/
theorem robinPowerTail_secondary_bounds
    {r x : Real} (hr0 : 0 <= r) (hr1 : r < 1) (hx : 1 < x) :
    And
      (0 <= x ^ (r - 1) / ((1 - r) * Real.log x) -
        integral (volume.restrict (Ioi x)) (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t))
      (x ^ (r - 1) / ((1 - r) * Real.log x) -
        integral (volume.restrict (Ioi x)) (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t) <=
          r / (1 - r) ^ 2 * x ^ (r - 1) / (Real.log x) ^ 2) := by
  let T : Real := integral (volume.restrict (Ioi x))
    (fun t : Real => t ^ (r - 2) * Inv.inv ((Real.log t) ^ 2))
  have hTNonneg : 0 <= T := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htPos : 0 < t := lt_trans Real.zero_lt_one (hx.trans ht)
    exact mul_nonneg (Real.rpow_nonneg htPos.le _) (inv_nonneg.mpr (sq_nonneg _))
  have ha : ((r : Complex) - 1).re < 0 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hTail := Robin1984.norm_robinCpowLogTail_le hx ha 2
  rw [cpowLogTail_real_two r hx, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hTNonneg] at hTail
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at hTail
  have hTUpper : T <= x ^ (r - 1) / ((1 - r) * (Real.log x) ^ 2) := by
    calc
      _ <= (-x ^ (r - 1) / (r - 1)) * Inv.inv ((Real.log x) ^ 2) := hTail
      _ = _ := by
        field_simp [show Not (r - 1 = 0) by linarith, show Not (1 - r = 0) by linarith]
        ring
  have hCoefficient : 0 <= r / (1 - r) := div_nonneg hr0 (by linarith)
  rw [robinPowerTail_secondary_identity hr1 hx]
  change And (0 <= _ - (_ - r / (1 - r) * T))
    (_ - (_ - r / (1 - r) * T) <= _)
  constructor
  next =>
    nlinarith [mul_nonneg hCoefficient hTNonneg]
  next =>
    have h := mul_le_mul_of_nonneg_left hTUpper hCoefficient
    have hEq : r / (1 - r) * (x ^ (r - 1) / ((1 - r) * (Real.log x) ^ 2)) =
        r / (1 - r) ^ 2 * x ^ (r - 1) / (Real.log x) ^ 2 := by
      field_simp [show Not (1 - r = 0) by linarith, (Real.log_pos hx).ne']
    rw [hEq] at h
    linarith

/-- Exact normalization of the full power-tail sandwich. The error is
explicit and uniform in the endpoint, with the exponent still a parameter. -/
theorem robinPowerTail_normalized_sandwich
    {r x : Real} (hr0 : 0 <= r) (hr1 : r < 1) (hx : 1 < x) :
    And
      (1 / (1 - r) - (r / (1 - r) ^ 2) / Real.log x <=
        (x ^ (1 - r) * Real.log x) * integral (volume.restrict (Ioi x))
          (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t))
      ((x ^ (1 - r) * Real.log x) * integral (volume.restrict (Ioi x))
          (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t) <= 1 / (1 - r)) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLog := (Real.log_pos hx).ne'
  have hDen : Not (1 - r = 0) := by linarith
  have hPower : x ^ (1 - r) * x ^ (r - 1) = 1 := by
    rw [<- Real.rpow_add hxPos]
    norm_num
  have hScale : 0 <= x ^ (1 - r) * Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_pos hx).le
  have hMain : (x ^ (1 - r) * Real.log x) *
      (x ^ (r - 1) / ((1 - r) * Real.log x)) = 1 / (1 - r) := by
    calc
      _ = (x ^ (1 - r) * x ^ (r - 1)) / (1 - r) := by field_simp [hLog, hDen]
      _ = _ := by rw [hPower]
  have hError : (x ^ (1 - r) * Real.log x) *
      (r / (1 - r) ^ 2 * x ^ (r - 1) / (Real.log x) ^ 2) =
        (r / (1 - r) ^ 2) / Real.log x := by
    calc
      _ = (r / (1 - r) ^ 2) * (x ^ (1 - r) * x ^ (r - 1)) / Real.log x := by
        field_simp [hLog, hDen]
      _ = _ := by rw [hPower, mul_one]
  have hBase := robinPowerTail_secondary_bounds hr0 hr1 hx
  have hNonneg := mul_nonneg hScale hBase.1
  have hBound := mul_le_mul_of_nonneg_left hBase.2 hScale
  rw [mul_sub, hMain] at hNonneg
  rw [mul_sub, hMain, hError] at hBound
  constructor <;> linarith

/-- The complete model integral has its exact leading coefficient for
every fixed nonnegative subcritical exponent, unconditionally. -/
theorem robinPowerTail_normalized_tendsto
    {r : Real} (hr0 : 0 <= r) (hr1 : r < 1) :
    Tendsto (fun x : Real => (x ^ (1 - r) * Real.log x) *
      integral (volume.restrict (Ioi x)) (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t))
      atTop (nhds (1 / (1 - r))) := by
  have hSmall : Tendsto (fun x : Real => (r / (1 - r) ^ 2) / Real.log x)
      atTop (nhds (0 : Real)) := Real.tendsto_log_atTop.const_div_atTop _
  have hLower : Tendsto (fun x : Real => 1 / (1 - r) - (r / (1 - r) ^ 2) / Real.log x)
      atTop (nhds (1 / (1 - r))) := by
    simpa only [sub_zero] using hSmall.const_sub (1 / (1 - r))
  have hBounds := (Filter.eventually_gt_atTop (1 : Real)).mono
    (fun x hx => robinPowerTail_normalized_sandwich hr0 hr1 hx)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower tendsto_const_nhds
    (hBounds.mono (fun _ h => h.1)) (hBounds.mono (fun _ h => h.2))

end

end RobinBV.NumberField
