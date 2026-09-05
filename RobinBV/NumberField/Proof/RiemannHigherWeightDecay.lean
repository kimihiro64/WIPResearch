import Robin1984.Equivalence.RobinLemmaTwo

/-!
# Higher-weight rational error decay under RH

The actual Robin all-exponent bounds imply decay above the half-line.
Both the full zero scalar and the explicit trivial correction are kept;
no pointwise Chebyshev estimate or additional analytic premise is used.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Filter

noncomputable section

private theorem riemannHigherScalar_scaled_tendsto
    {n : Nat} (hn : 1 <= n) {s : Real} (hs : 1 / 2 < s) :
    Tendsto (fun x : Real => (x ^ ((n : Real) - s) * Real.log x) *
      Robin1984.robinPsiWeightedErrorScalar n x) atTop (nhds (0 : Real)) := by
  have hInv : Tendsto (fun x : Real => Inv.inv (Real.log x)) atTop (nhds (0 : Real)) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hCoefficient : Tendsto (fun x : Real => (n : Real) + Inv.inv (Real.log x) +
      (4 * Inv.inv ((2 * n - 1 : Nat) : Real)) * Inv.inv (Real.log x) ^ 2)
      atTop (nhds (n : Real)) := by
    convert (hInv.const_add (n : Real)).add
      ((hInv.pow 2).const_mul (4 * Inv.inv ((2 * n - 1 : Nat) : Real))) using 1
    norm_num
  have hPower : Tendsto (fun x : Real => x ^ ((1 / 2 : Real) - s)) atTop (nhds (0 : Real)) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hs)
  have h := (hPower.mul hCoefficient).const_mul
    (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : Real)] with x hx
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLog : Not (Real.log x = 0) := (Real.log_pos hx).ne'
  have hDen : Not (((2 * n - 1 : Nat) : Real) = 0) := by
    exact_mod_cast (show Not (2 * n - 1 = 0) by omega)
  have hPowers : x ^ ((n : Real) - s) * x ^ ((1 / 2 : Real) - (n : Real)) =
      x ^ ((1 / 2 : Real) - s) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  rw [<- hPowers]
  unfold Robin1984.robinPsiWeightedErrorScalar
  field_simp [hLog, hDen]

/-- The actual rational Robin error integral has full higher-weight
power-saving decay under RH for every exponent n>=1 and s>1/2. -/
theorem riemannPsiWeightedErrorIntegral_scaled_tendsto
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) {s : Real} (hs : 1 / 2 < s) :
    Tendsto (fun x : Real => (x ^ ((n : Real) - s) * Real.log x) *
      Robin1984.robinPsiWeightedErrorIntegral n x) atTop (nhds (0 : Real)) := by
  have hPower : Tendsto (fun x : Real => x ^ (-s)) atTop (nhds (0 : Real)) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hUpper : Tendsto (fun x : Real =>
      (x ^ ((n : Real) - s) * Real.log x) * Robin1984.robinPsiWeightedErrorScalar n x +
        Real.log (2 * Real.pi) * x ^ (-s)) atTop (nhds (0 : Real)) := by
    simpa only [mul_zero, add_zero] using
      (riemannHigherScalar_scaled_tendsto hn hs).add (hPower.const_mul (Real.log (2 * Real.pi)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_ge_atTop (2 : Real)] with x hx
  have hxOne : 1 < x := by linarith
  have hxPos : 0 < x := by linarith
  have hScale : 0 <= x ^ ((n : Real) - s) * Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_pos hxOne).le
  have hLog : Not (Real.log x = 0) := (Real.log_pos hxOne).ne'
  have hC : 0 <= Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hCorrection : 0 <= Real.log (2 * Real.pi) * x ^ (-(n : Real)) * Inv.inv (Real.log x) := by
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hxPos.le _)) (inv_pos.mpr (Real.log_pos hxOne)).le
  have hBounds := Robin1984.robinPsiWeightedErrorIntegral_bounds_all hRH hn hx
  have hAbs : abs (Robin1984.robinPsiWeightedErrorIntegral n x) <=
      Robin1984.robinPsiWeightedErrorScalar n x +
        Real.log (2 * Real.pi) * x ^ (-(n : Real)) * Inv.inv (Real.log x) := by
    apply abs_le.mpr
    constructor <;> linarith [hBounds.1, hBounds.2]
  have hPowers : x ^ ((n : Real) - s) * x ^ (-(n : Real)) = x ^ (-s) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hScale, Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left hAbs hScale).trans_eq
  rw [mul_add]
  congr 1
  calc
    _ = Real.log (2 * Real.pi) *
        (x ^ ((n : Real) - s) * x ^ (-(n : Real))) := by field_simp [hLog]
    _ = _ := by rw [hPowers]

end

end RobinBV.NumberField
