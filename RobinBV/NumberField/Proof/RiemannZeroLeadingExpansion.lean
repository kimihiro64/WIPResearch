import Robin1984.Equivalence.RobinLemmaTwo
import RobinBV.NumberField.Helpers.ZeroKernelLeadingExpansion

/-!
# Leading expansion of the actual complete Riemann zero kernel

The generic kernel estimate is instantiated with the multiplicity-aware
xi divisor and Robin's exact inverse-square zero mass under RH.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter

noncomputable section

/-- Explicit complete leading error for the actual zeta zero series. -/
theorem norm_riemannZeroKernel_leading_error_scaled_le
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    norm (((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) *
      (tsum (fun p : RiemannXiDivisorZeroIndex =>
        Robin1984.robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) -
        tsum (fun p : RiemannXiDivisorZeroIndex => zeroKernelLeadingTerm n (riemannXiDivisorZeroValue p) x))) <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        (Inv.inv (Real.log x) + (2 / ((n : Real) - 1 / 2)) * Inv.inv (Real.log x) ^ 2) := by
  have h := norm_zeroKernel_sum_leading_error_scaled_le riemannXiDivisorZeroValue
    (fun p => Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p)
    Robin1984.summable_robinXiZeroWeight hn hx
  rw [Robin1984.robinXiZeroConstant_eq_of_riemannHypothesis hRH] at h
  exact h

/-- The actual complete zeta leading-kernel error vanishes at the
critical normalization, retaining every zero and its multiplicity. -/
theorem riemannZeroKernel_leading_error_scaled_tendsto
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) :
    Tendsto (fun x : Real => ((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) *
      (tsum (fun p : RiemannXiDivisorZeroIndex =>
        Robin1984.robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) -
        tsum (fun p : RiemannXiDivisorZeroIndex => zeroKernelLeadingTerm n (riemannXiDivisorZeroValue p) x)))
      atTop (nhds (0 : Complex)) :=
  zeroKernel_sum_leading_error_scaled_tendsto riemannXiDivisorZeroValue
    (fun p => Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p)
    Robin1984.summable_robinXiZeroWeight hn

/-- In the actual rational explicit formula, every nonzero-kernel
correction vanishes at the critical normalization for all n>=1. -/
theorem riemannWeightedIntegral_add_zeroKernel_scaled_tendsto
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) :
    Tendsto (fun x : Real => ((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) *
      ((Robin1984.robinPsiWeightedErrorIntegral n x : Complex) +
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          Robin1984.robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p)))
      atTop (nhds (0 : Complex)) := by
  have hUpper : Tendsto (fun x : Real => Real.log (2 * Real.pi) * x ^ (-(1 / 2 : Real)))
      atTop (nhds (0 : Real)) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : Real) < 1 / 2)).const_mul
      (Real.log (2 * Real.pi))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_ge_atTop (2 : Real)] with x hx
  have hxOne : 1 < x := by linarith
  have hxPos : 0 < x := by linarith
  have hLog : Not (Real.log x = 0) := (Real.log_pos hxOne).ne'
  have hScale : 0 <= x ^ ((n : Real) - 1 / 2) * Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_pos hxOne).le
  have hIdentity := Robin1984.robinPsiWeightedErrorIntegral_eq_zero_sum_correction_all hRH hn hx
  have hTrivial := Robin1984.robinTrivialZeroCorrection_bounds hn hx
  rw [hIdentity]
  have hCancel (a b : Complex) : -a - b + a = -b := by ring
  rw [hCancel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale,
    norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hTrivial.1]
  apply (mul_le_mul_of_nonneg_left hTrivial.2 hScale).trans_eq
  have hPowers : x ^ ((n : Real) - 1 / 2) * x ^ (-(n : Real)) = x ^ (-(1 / 2 : Real)) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  calc
    _ = Real.log (2 * Real.pi) * (x ^ ((n : Real) - 1 / 2) * x ^ (-(n : Real))) := by field_simp [hLog]
    _ = _ := by rw [hPowers]

/-- The actual rational weighted arithmetic integral is minus its full
leading zero series up to a vanishing critical-scaled error under RH. -/
theorem riemannWeightedIntegral_add_leadingZeroSeries_scaled_tendsto
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) :
    Tendsto (fun x : Real => ((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) *
      ((Robin1984.robinPsiWeightedErrorIntegral n x : Complex) +
        tsum (fun p : RiemannXiDivisorZeroIndex => zeroKernelLeadingTerm n (riemannXiDivisorZeroValue p) x)))
      atTop (nhds (0 : Complex)) := by
  have h := (riemannWeightedIntegral_add_zeroKernel_scaled_tendsto hRH hn).sub
    (riemannZeroKernel_leading_error_scaled_tendsto hRH hn)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with x
  ring

end

end RobinBV.NumberField
