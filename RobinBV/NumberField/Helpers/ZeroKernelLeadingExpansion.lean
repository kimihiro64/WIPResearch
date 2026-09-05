import Robin1984.NicolasLandau.RobinWeightedIntegral

/-!
# Complete leading expansion of Robin's zero kernel

The exact leading atom and the full twice-integrated remainder are
kept separately. The normalized remainder has an inverse-logarithmic
bound uniform over the critical line, suitable for actual zero sums.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter

noncomputable section

/-- Exact leading atom after dividing Robin's kernel by its zero. -/
def zeroKernelLeadingTerm (n : Nat) (rho : Complex) (x : Real) : Complex :=
  (((n : Complex) / ((n : Complex) - rho)) / rho) *
    (x : Complex) ^ (rho - (n : Complex)) * (Inv.inv (Real.log x) : Complex)

/-- Robin's exact kernel decomposition with the divided leading atom. -/
theorem zeroKernel_div_eq_leading_add_remainder
    {n : Nat} (hn : 1 <= n) {rho : Complex} {x : Real}
    (hx : 1 < x) (hRe : rho.re < n) :
    Robin1984.robinZeroKernel n rho x / rho = zeroKernelLeadingTerm n rho x +
      Robin1984.robinZeroKernelRemainder n rho x / rho := by
  rw [Robin1984.robinZeroKernel_eq_main_add_remainder hn hx hRe]
  unfold zeroKernelLeadingTerm
  simp only [Complex.ofReal_inv]
  ring

/-- The complete normalized leading error is logarithmically small,
uniformly at every critical-line point, including zero imaginary part. -/
theorem norm_zeroKernel_leading_error_scaled_le
    {n : Nat} (hn : 1 <= n) {rho : Complex} (hRe : rho.re = (1 / 2 : Real))
    {x : Real} (hx : 1 < x) :
    norm (((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) *
      (Robin1984.robinZeroKernel n rho x / rho - zeroKernelLeadingTerm n rho x)) <=
      (Inv.inv (norm rho)) ^ 2 *
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
  have hBound := Robin1984.norm_robinZeroKernelRemainder_div_rho_le hn hRho hRe hx
  rw [zeroKernel_div_eq_leading_add_remainder hn hx hReLt, add_sub_cancel_left,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale]
  apply (mul_le_mul_of_nonneg_left hBound hScale).trans_eq
  simp only [show (1 / 2 : Real) - (n : Real) = -((n : Real) - 1 / 2) by ring] at hPowers
  simp only [show (1 / 2 : Real) - (n : Real) = -((n : Real) - 1 / 2) by ring,
    neg_div_neg_eq]
  have hDen : Not ((n : Real) - 1 / 2 = 0) := by linarith
  calc
    _ = (Inv.inv (norm rho)) ^ 2 *
        (x ^ ((n : Real) - 1 / 2) * x ^ (-((n : Real) - 1 / 2))) *
          (Inv.inv (Real.log x) + (2 / ((n : Real) - 1 / 2)) * Inv.inv (Real.log x) ^ 2) := by
      field_simp [hLogPos.ne', hDen]
    _ = _ := by rw [hPowers, mul_one]

/-- Complete critical-line kernel and leading series are summable when
the inverse-square weights are summable. Actual zero providers discharge
these hypotheses; no arithmetic explicit formula is assumed here. -/
theorem zeroKernel_leading_series_summable
    {I : Type*} (rho : I -> Complex) (hRe : forall i : I, (rho i).re = (1 / 2 : Real))
    (hWeight : Summable (fun i : I => (Inv.inv (norm (rho i))) ^ 2))
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    And (Summable (fun i : I => Robin1984.robinZeroKernel n (rho i) x / rho i))
      (Summable (fun i : I => zeroKernelLeadingTerm n (rho i) x)) := by
  let R : Real := x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x ^ 2) +
    2 * ((-x ^ ((1 / 2 : Real) - (n : Real)) / ((1 / 2 : Real) - (n : Real))) *
      Inv.inv (Real.log x ^ 3))
  let K : Real := (n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) + R
  have hRho (i : I) : Not (rho i = 0) := by
    intro h
    have hi := hRe i
    rw [h, Complex.zero_re] at hi
    norm_num at hi
  have hKernel : Summable (fun i : I => Robin1984.robinZeroKernel n (rho i) x / rho i) := by
    apply (hWeight.mul_right K).of_norm_bounded
    intro i
    exact Robin1984.norm_robinZeroKernel_div_rho_le_robinXiZeroWeight hn (hRho i) (hRe i) hx
  have hRemainder : Summable (fun i : I => Robin1984.robinZeroKernelRemainder n (rho i) x / rho i) := by
    apply (hWeight.mul_right R).of_norm_bounded
    intro i
    exact Robin1984.norm_robinZeroKernelRemainder_div_rho_le hn (hRho i) (hRe i) hx
  refine And.intro hKernel ?_
  apply (hKernel.sub hRemainder).congr
  intro i
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn
  have hi : (rho i).re < n := by rw [hRe i]; linarith
  rw [zeroKernel_div_eq_leading_add_remainder hn hx hi, add_sub_cancel_right]

/-- Explicit logarithmic error for the complete zero-kernel sum relative
to its complete leading series, with the full inverse-square mass. -/
theorem norm_zeroKernel_sum_leading_error_scaled_le
    {I : Type*} (rho : I -> Complex) (hRe : forall i : I, (rho i).re = (1 / 2 : Real))
    (hWeight : Summable (fun i : I => (Inv.inv (norm (rho i))) ^ 2))
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    norm (((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) *
      (tsum (fun i : I => Robin1984.robinZeroKernel n (rho i) x / rho i) -
        tsum (fun i : I => zeroKernelLeadingTerm n (rho i) x))) <=
      tsum (fun i : I => (Inv.inv (norm (rho i))) ^ 2) *
        (Inv.inv (Real.log x) + (2 / ((n : Real) - 1 / 2)) * Inv.inv (Real.log x) ^ 2) := by
  let C : Real := Inv.inv (Real.log x) + (2 / ((n : Real) - 1 / 2)) * Inv.inv (Real.log x) ^ 2
  have hSeries := zeroKernel_leading_series_summable rho hRe hWeight hn hx
  have hError := (hSeries.1.sub hSeries.2).mul_left
    (((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex))
  rw [<- hSeries.1.tsum_sub hSeries.2, <- tsum_mul_left]
  calc
    _ <= tsum (fun i : I => norm (((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) *
        (Robin1984.robinZeroKernel n (rho i) x / rho i - zeroKernelLeadingTerm n (rho i) x))) :=
      norm_tsum_le_tsum_norm hError.norm
    _ <= tsum (fun i : I => (Inv.inv (norm (rho i))) ^ 2 * C) :=
      hError.norm.tsum_le_tsum (fun i => norm_zeroKernel_leading_error_scaled_le hn (hRe i) hx)
        (hWeight.mul_right C)
    _ = _ := by rw [tsum_mul_right]

/-- The difference between the complete kernel and leading zero sums
vanishes at the critical normalization; the leading sum itself remains. -/
theorem zeroKernel_sum_leading_error_scaled_tendsto
    {I : Type*} (rho : I -> Complex) (hRe : forall i : I, (rho i).re = (1 / 2 : Real))
    (hWeight : Summable (fun i : I => (Inv.inv (norm (rho i))) ^ 2))
    {n : Nat} (hn : 1 <= n) :
    Tendsto (fun x : Real => ((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) *
      (tsum (fun i : I => Robin1984.robinZeroKernel n (rho i) x / rho i) -
        tsum (fun i : I => zeroKernelLeadingTerm n (rho i) x))) atTop (nhds (0 : Complex)) := by
  have hInv : Tendsto (fun x : Real => Inv.inv (Real.log x)) atTop (nhds (0 : Real)) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hUpper : Tendsto (fun x : Real => tsum (fun i : I => (Inv.inv (norm (rho i))) ^ 2) *
      (Inv.inv (Real.log x) + (2 / ((n : Real) - 1 / 2)) * Inv.inv (Real.log x) ^ 2))
      atTop (nhds (0 : Real)) := by
    simpa only [zero_pow (by norm_num : Not ((2 : Nat) = 0)), mul_zero, add_zero] using
      (hInv.add ((hInv.pow 2).const_mul (2 / ((n : Real) - 1 / 2)))).const_mul
        (tsum (fun i : I => (Inv.inv (norm (rho i))) ^ 2))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_gt_atTop (1 : Real)] with x hx
  exact norm_zeroKernel_sum_leading_error_scaled_le rho hRe hWeight hn hx

/-- Exact critical normalization of each leading zero atom. No point
is discarded, and this identity does not require a critical-line premise. -/
theorem zeroKernelLeadingTerm_scaled_eq
    (n : Nat) (rho : Complex) {x : Real} (hx : 1 < x) :
    ((x ^ ((n : Real) - 1 / 2) * Real.log x : Real) : Complex) * zeroKernelLeadingTerm n rho x =
      (n : Complex) / (rho * ((n : Complex) - rho)) * (x : Complex) ^ (rho - 1 / 2) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hxC : Not ((x : Complex) = 0) := Complex.ofReal_ne_zero.mpr hxPos.ne'
  have hLog : Not ((Real.log x : Complex) = 0) := Complex.ofReal_ne_zero.mpr (Real.log_pos hx).ne'
  have hPowers : (x : Complex) ^ (((n : Real) - 1 / 2 : Real) : Complex) *
      (x : Complex) ^ (rho - (n : Complex)) = (x : Complex) ^ (rho - 1 / 2) := by
    rw [<- Complex.cpow_add _ _ hxC]
    congr 1
    push_cast
    ring
  have hLogCancel : (Real.log x : Complex) * Inv.inv (Real.log x : Complex) = 1 := by field_simp [hLog]
  unfold zeroKernelLeadingTerm
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hxPos.le]
  calc
    _ = (((n : Complex) / ((n : Complex) - rho)) / rho) *
        ((x : Complex) ^ (((n : Real) - 1 / 2 : Real) : Complex) * (x : Complex) ^ (rho - (n : Complex))) *
          ((Real.log x : Complex) * Inv.inv (Real.log x : Complex)) := by ring
    _ = _ := by
      rw [hPowers, hLogCancel, mul_one]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Exact phase pullback to a positive real root, with the complete
complex exponent rather than a real-part proxy. -/
theorem zeroKernelLeadingTerm_root_phase_eq
    (k : Nat) (rho : Complex) {x : Real} (hx : 1 < x) (hk : 0 < k) :
    (((x ^ (Inv.inv (k : Real))) ^ ((k : Real) - 1 / 2) *
      Real.log (x ^ (Inv.inv (k : Real))) : Real) : Complex) *
        zeroKernelLeadingTerm k rho (x ^ (Inv.inv (k : Real))) =
      (k : Complex) / (rho * ((k : Complex) - rho)) *
        (x : Complex) ^ ((rho - 1 / 2) / (k : Complex)) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hkPos : (0 : Real) < k := by exact_mod_cast hk
  have hRoot : 1 < x ^ (Inv.inv (k : Real)) := Real.one_lt_rpow hx (inv_pos.mpr hkPos)
  rw [zeroKernelLeadingTerm_scaled_eq k rho hRoot,
    <- Complex.cpow_mul_ofReal_nonneg hxPos.le]
  congr 2
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

/-- Exact full-series normalization at a real root. The identity keeps
the complete complex phase and the precise factor from root substitution. -/
theorem zeroKernelLeadingSum_root_scaled_eq
    {I : Type*} (rho : I -> Complex) (k : Nat) (hk : 0 < k) {x : Real} (hx : 1 < x) :
    ((x ^ (1 - Inv.inv ((2 * k : Nat) : Real)) * Real.log x : Real) : Complex) *
      (Inv.inv (k : Real) : Complex) *
        tsum (fun i : I => zeroKernelLeadingTerm k (rho i) (x ^ (Inv.inv (k : Real)))) =
      tsum (fun i : I => (k : Complex) / (rho i * ((k : Complex) - rho i)) *
        (x : Complex) ^ ((rho i - 1 / 2) / (k : Complex))) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hkPos : (0 : Real) < k := by exact_mod_cast hk
  have hPower : (x ^ (Inv.inv (k : Real))) ^ ((k : Real) - 1 / 2) =
      x ^ (1 - Inv.inv ((2 * k : Nat) : Real)) := by
    rw [<- Real.rpow_mul hxPos.le]
    congr 1
    push_cast
    field_simp [hkPos.ne']
  have hScalar : (((x ^ (Inv.inv (k : Real))) ^ ((k : Real) - 1 / 2) *
      Real.log (x ^ (Inv.inv (k : Real))) : Real) : Complex) =
        ((x ^ (1 - Inv.inv ((2 * k : Nat) : Real)) * Real.log x : Real) : Complex) *
          (Inv.inv (k : Real) : Complex) := by
    rw [hPower, Real.log_rpow hxPos]
    simp only [Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  rw [<- hScalar, <- tsum_mul_left]
  apply tsum_congr
  intro i
  exact zeroKernelLeadingTerm_root_phase_eq k (rho i) hx hk

/-- Complete root-phase series are summable for critical-line families
with summable inverse-square weights; central points are included. -/
theorem zeroKernelRootPhase_summable
    {I : Type*} (rho : I -> Complex) (hRe : forall i : I, (rho i).re = (1 / 2 : Real))
    (hWeight : Summable (fun i : I => (Inv.inv (norm (rho i))) ^ 2))
    (k : Nat) (hk : 0 < k) {x : Real} (hx : 1 < x) :
    Summable (fun i : I => (k : Complex) / (rho i * ((k : Complex) - rho i)) *
      (x : Complex) ^ ((rho i - 1 / 2) / (k : Complex))) := by
  have hkPos : (0 : Real) < k := by exact_mod_cast hk
  have hRoot : 1 < x ^ (Inv.inv (k : Real)) := Real.one_lt_rpow hx (inv_pos.mpr hkPos)
  have hSeries := (zeroKernel_leading_series_summable rho hRe hWeight (by omega : 1 <= k) hRoot).2
  let F : Real := (x ^ (Inv.inv (k : Real))) ^ ((k : Real) - 1 / 2) *
    Real.log (x ^ (Inv.inv (k : Real)))
  apply (hSeries.mul_left (F : Complex)).congr
  intro i
  exact zeroKernelLeadingTerm_root_phase_eq k (rho i) hx hk

end

end RobinBV.NumberField
