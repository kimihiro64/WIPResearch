import RobinBV.Mathlib.Analysis.Complex.ShiftedInverseSquare
import RobinBV.NumberField.Helpers.ZeroKernelLeadingExpansion

/-!
# Shifted spectral mass in the complete Robin kernel error

Retain the exact shifted denominator from the integrated remainder, rather
than replacing it by the unshifted inverse-square majorant.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex

noncomputable section

/-- Full divided remainder with its actual shifted inverse-square factor. -/
theorem norm_zeroKernelRemainder_div_shifted_le
    {n : Nat} (hn : 1 <= n) {rho : Complex} (hRho : Not (rho = 0))
    (hRe : rho.re = (1/2 : Real)) {x : Real} (hx : 1 < x) :
    norm (Robin1984.robinZeroKernelRemainder n rho x / rho) <=
      (Inv.inv (norm ((n : Complex)-rho)))^2 *
        (x ^ ((1/2 : Real)-(n : Real)) * Inv.inv (Real.log x ^ 2) +
          2*((-x ^ ((1/2 : Real)-(n : Real))/((1/2 : Real)-(n : Real))) *
            Inv.inv (Real.log x ^ 3))) := by
  rw [Robin1984.robinZeroKernelRemainder_div_rho hRho, norm_mul, norm_inv, norm_pow]
  rw [norm_sub_rev rho (n : Complex), inv_pow]
  exact mul_le_mul_of_nonneg_left
    (Robin1984.norm_robinZeroKernelRemainder_bracket_le hn hRe hx) (by positivity)

/-- Normalized complete error controlled by the smaller shifted weight. -/
theorem norm_zeroKernel_leading_error_scaled_shifted_le
    {n : Nat} (hn : 1 <= n) {rho : Complex} (hRe : rho.re = (1 / 2 : Real))
    {x : Real} (hx : 1 < x) :
    norm (((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) *
      (Robin1984.robinZeroKernel n rho x / rho - zeroKernelLeadingTerm n rho x)) <=
      (Inv.inv (norm ((n : Complex) - rho))) ^ 2 *
        (Inv.inv (Real.log x) + (2 / ((n : Real) - 1 / 2)) * Inv.inv (Real.log x) ^ 2) := by
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn
  have hRho : Not (rho = 0) := by
    intro h
    rw [h, Complex.zero_re] at hRe
    norm_num at hRe
  have hReLt : rho.re < n := by rw [hRe]; linarith
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLogPos := Real.log_pos hx
  have hScale : 0 <= x ^ ((n : Real) - 1 / 2) * Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hLogPos.le
  have hPowers : x ^ ((n : Real) - 1 / 2) * x ^ ((1 / 2 : Real) - (n : Real)) = 1 := by
    rw [<- Real.rpow_add hxPos]
    norm_num
  have hBound := norm_zeroKernelRemainder_div_shifted_le hn hRho hRe hx
  rw [zeroKernel_div_eq_leading_add_remainder hn hx hReLt, add_sub_cancel_left,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale]
  apply (mul_le_mul_of_nonneg_left hBound hScale).trans_eq
  simp only [show (1 / 2 : Real) - (n : Real) = -((n : Real) - 1 / 2) by ring] at hPowers
  simp only [show (1 / 2 : Real) - (n : Real) = -((n : Real) - 1 / 2) by ring,
    neg_div_neg_eq]
  have hDen : Not ((n : Real) - 1 / 2 = 0) := by linarith
  calc
    _ = (Inv.inv (norm ((n : Complex) - rho))) ^ 2 *
        (x ^ ((n : Real) - 1 / 2) * x ^ (-((n : Real) - 1 / 2))) *
          (Inv.inv (Real.log x) + (2 / ((n : Real) - 1 / 2)) * Inv.inv (Real.log x) ^ 2) := by
      field_simp [hLogPos.ne', hDen]
    _ = _ := by rw [hPowers, mul_one]


/-- Complete zero-sum leading error controlled by the full shifted mass. -/
theorem norm_zeroKernel_sum_leading_error_scaled_shifted_le
    {I : Type*} (rho : I -> Complex) (hRe : forall i : I, (rho i).re = (1 / 2 : Real))
    (hWeight : Summable (fun i : I => (Inv.inv (norm (rho i))) ^ 2))
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    norm (((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) *
      (tsum (fun i : I => Robin1984.robinZeroKernel n (rho i) x / rho i) -
        tsum (fun i : I => zeroKernelLeadingTerm n (rho i) x))) <=
      tsum (fun i : I => (Inv.inv (norm ((n : Complex) - rho i))) ^ 2) *
        (Inv.inv (Real.log x) + (2 / ((n : Real) - 1 / 2)) * Inv.inv (Real.log x) ^ 2) := by
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn
  have hShift := Complex.summable_inv_norm_real_sub_sq_of_re_eq_half rho hRe hWeight hnReal
  let C : Real := Inv.inv (Real.log x) + (2 / ((n : Real) - 1 / 2)) * Inv.inv (Real.log x) ^ 2
  have hSeries := zeroKernel_leading_series_summable rho hRe hWeight hn hx
  have hError := (hSeries.1.sub hSeries.2).mul_left
    (((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex))
  rw [<- hSeries.1.tsum_sub hSeries.2, <- tsum_mul_left]
  calc
    _ <= tsum (fun i : I => norm (((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) *
        (Robin1984.robinZeroKernel n (rho i) x / rho i - zeroKernelLeadingTerm n (rho i) x))) :=
      norm_tsum_le_tsum_norm hError.norm
    _ <= tsum (fun i : I => (Inv.inv (norm ((n : Complex) - rho i))) ^ 2 * C) :=
      hError.norm.tsum_le_tsum (fun i => norm_zeroKernel_leading_error_scaled_shifted_le hn (hRe i) hx)
        (by simpa only [Complex.ofReal_natCast] using hShift.mul_right C)
    _ = _ := by rw [tsum_mul_right]


/-- The leading phase series has the smaller Cauchy-Schwarz amplitude. -/
theorem norm_zeroKernel_leading_sum_scaled_le_sqrt
    {I : Type*} (rho : I -> Complex) (hRe : forall i, (rho i).re = (1/2 : Real))
    (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2))
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    norm (((x ^ ((n : Real)-1/2)*Real.log x : Real) : Complex)*
      tsum (fun i => zeroKernelLeadingTerm n (rho i) x)) <=
      (n : Real)*Real.sqrt (tsum (fun i => (Inv.inv (norm (rho i)))^2)*
        tsum (fun i => (Inv.inv (norm ((n : Complex)-rho i)))^2)) := by
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  let F : Complex := ((x ^ ((n : Real)-1/2)*Real.log x : Real) : Complex)
  have hSeries := (zeroKernel_leading_series_summable rho hRe hWeight hn hx).2.mul_left F
  have hNorm (i : I) : norm (F * zeroKernelLeadingTerm n (rho i) x) =
      norm ((n : Complex)/(rho i*((n : Complex)-rho i))) := by
    rw [show F = ((x ^ ((n : Real)-1/2)*Real.log x : Real) : Complex) from rfl,
      zeroKernelLeadingTerm_scaled_eq n (rho i) hx, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
    have hExponent : (rho i-(1/2 : Complex)).re = 0 := by simp [hRe i]
    rw [hExponent, Real.rpow_zero, mul_one]
  change norm (F * tsum (fun i => zeroKernelLeadingTerm n (rho i) x)) <= _
  rw [<- tsum_mul_left]
  calc
    _ <= tsum (fun i => norm (F * zeroKernelLeadingTerm n (rho i) x)) :=
      norm_tsum_le_tsum_norm hSeries.norm
    _ = tsum (fun i => norm ((n : Complex)/(rho i*((n : Complex)-rho i)))) :=
      tsum_congr hNorm
    _ <= _ := by
      simpa only [Complex.ofReal_natCast] using
        Complex.tsum_norm_real_div_mul_sub_le_sqrt_of_re_eq_half rho hRe hWeight hnReal

/-- Complete normalized Robin kernel bound with the refined leading
amplitude and the full shifted-mass logarithmic remainder. -/
theorem norm_zeroKernel_sum_scaled_le_sqrt_add_shifted
    {I : Type*} (rho : I -> Complex) (hRe : forall i, (rho i).re = (1/2 : Real))
    (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2))
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    norm (((x ^ ((n : Real)-1/2)*Real.log x : Real) : Complex)*
      tsum (fun i => Robin1984.robinZeroKernel n (rho i) x / rho i)) <=
      (n : Real)*Real.sqrt (tsum (fun i => (Inv.inv (norm (rho i)))^2)*
        tsum (fun i => (Inv.inv (norm ((n : Complex)-rho i)))^2)) +
      tsum (fun i => (Inv.inv (norm ((n : Complex)-rho i)))^2)*
        (Inv.inv (Real.log x)+(2/((n : Real)-1/2))*Inv.inv (Real.log x)^2) := by
  have hLead := norm_zeroKernel_leading_sum_scaled_le_sqrt rho hRe hWeight hn hx
  have hError := norm_zeroKernel_sum_leading_error_scaled_shifted_le rho hRe hWeight hn hx
  let F : Complex := ((x ^ ((n : Real)-1/2)*Real.log x : Real) : Complex)
  let K : Complex := tsum (fun i => Robin1984.robinZeroKernel n (rho i) x / rho i)
  let L : Complex := tsum (fun i => zeroKernelLeadingTerm n (rho i) x)
  have hSplit : F*K=F*L+F*(K-L) := by ring
  change norm (F*K) <= _
  rw [hSplit]
  exact (norm_add_le _ _).trans (add_le_add hLead hError)

end

end RobinBV.NumberField
