import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Robin1984.NicolasLandau.WeightedEndpoint

/-!
# Quantitative bounds for Robin's endpoint reweighting

The boundary ratio decreases, and the derivative lies below that same ratio.
Keeping it yields a coefficient tending to one rather than an avoidable
factor two when transferring a reciprocal-square remainder to exponent one.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set

/-- The boundary weight is the endpoint variable times its exact ratio. -/
theorem robinEndpointReweight_eq_mul_ratio (t : Real) :
    Robin1984.robinEndpointReweight t =
      t * ((Real.log t + 1) / (2 * Real.log t + 1)) := by
  unfold Robin1984.robinEndpointReweight
  ring

/-- The normalized boundary weight decreases on the positive logarithmic ray. -/
theorem robinEndpointRatio_antitone
    {x t : Real} (hx : 1 < x) (hxt : x <= t) :
    (Real.log t + 1) / (2 * Real.log t + 1) <=
      (Real.log x + 1) / (2 * Real.log x + 1) := by
  have hxLog := Real.log_pos hx
  have htLog := Real.log_pos (lt_of_lt_of_le hx hxt)
  have hLog := Real.log_le_log (lt_trans zero_lt_one hx) hxt
  have hRatio (L : Real) (hL : 0 < L) :
      (L + 1) / (2 * L + 1) = 1 / 2 + (1 / (2 * L + 1)) / 2 := by
    have hDen : Not (2 * L + 1 = 0) := by positivity
    field_simp [hDen]
    ring
  rw [hRatio _ htLog, hRatio _ hxLog]
  have hInv := one_div_le_one_div_of_le
    (show 0 < 2 * Real.log x + 1 by positivity)
    (show 2 * Real.log x + 1 <= 2 * Real.log t + 1 by linarith)
  linarith

/-- The derivative is below the boundary ratio at every earlier endpoint. -/
theorem robinEndpointReweightDerivative_le_ratio
    {x t : Real} (hx : 1 < x) (hxt : x <= t) :
    Robin1984.robinEndpointReweightDerivative t <=
      (Real.log x + 1) / (2 * Real.log x + 1) := by
  have htLog := Real.log_pos (lt_of_lt_of_le hx hxt)
  have hIdentity : Robin1984.robinEndpointReweightDerivative t =
      (Real.log t + 1) / (2 * Real.log t + 1) -
        1 / (2 * Real.log t + 1) ^ 2 := by
    unfold Robin1984.robinEndpointReweightDerivative
    have hDen : Not (2 * Real.log t + 1 = 0) := by positivity
    field_simp [hDen]
    ring
  rw [hIdentity]
  exact (sub_le_self _ (by positivity)).trans (robinEndpointRatio_antitone hx hxt)

/-- A reciprocal-square majorant transfers with an asymptotically unit
coefficient, retaining a logarithmic gain in its second component. -/
theorem norm_robinEndpointReweight_remainder_le
    {x B C : Real} (hx : 1 < x) (hB : 0 <= B) (hC : 0 <= C)
    {R : Real -> Complex}
    (hR : forall t : Real, x <= t ->
      norm (R t) <= t ^ (-(2 : Real)) * (B + C / Real.log t))
    (hInt : IntegrableOn (fun t : Real =>
      (Robin1984.robinEndpointReweightDerivative t : Complex) * R t) (Ioi x)) :
    norm ((Robin1984.robinEndpointReweight x : Complex) * R x +
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) * R t)) <=
      (1 + 1 / (2 * Real.log x + 1)) *
        (B + C / Real.log x) * x ^ (-(1 : Real)) := by
  let r : Real := (Real.log x + 1) / (2 * Real.log x + 1)
  let A : Real := B + C / Real.log x
  have hxPos : 0 < x := lt_trans zero_lt_one hx
  have hxLog := Real.log_pos hx
  have hr : 0 <= r := by dsimp [r]; positivity
  have hA : 0 <= A := by dsimp [A]; positivity
  have hWeight : Robin1984.robinEndpointReweight x = x * r :=
    robinEndpointReweight_eq_mul_ratio x
  have hWeightNonneg : 0 <= Robin1984.robinEndpointReweight x := by
    rw [hWeight]
    positivity
  have hPower : x * x ^ (-(2 : Real)) = x ^ (-(1 : Real)) := by
    calc
      x * x ^ (-(2 : Real)) = x ^ (1 : Real) * x ^ (-(2 : Real)) := by
        rw [Real.rpow_one]
      _ = x ^ ((1 : Real) + (-(2 : Real))) := (Real.rpow_add hxPos _ _).symm
      _ = _ := by norm_num
  have hBoundary :
      norm ((Robin1984.robinEndpointReweight x : Complex) * R x) <=
        r * A * x ^ (-(1 : Real)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeightNonneg]
    calc
      Robin1984.robinEndpointReweight x * norm (R x) <=
          Robin1984.robinEndpointReweight x * (x ^ (-(2 : Real)) * A) :=
        mul_le_mul_of_nonneg_left (hR x le_rfl) hWeightNonneg
      _ = r * A * (x * x ^ (-(2 : Real))) := by rw [hWeight]; ring
      _ = _ := by rw [hPower]
  have hTailBound (t : Real) (ht : x <= t) :
      norm (R t) <= t ^ (-(2 : Real)) * A := by
    apply (hR t ht).trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hxPos.le.trans ht) _)
    have hLog := Real.log_le_log hxPos ht
    have hInv := div_le_div_of_nonneg_left hC hxLog hLog
    dsimp only [A]
    linarith
  have hMajor : IntegrableOn (fun t : Real => (r * A) * t ^ (-(2 : Real)))
      (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(2 : Real)) < -1) hxPos).const_mul (r * A)
  have hIntegral :
      norm (integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) * R t)) <=
        r * A * x ^ (-(1 : Real)) := by
    calc
      _ <= integral (volume.restrict (Ioi x)) (fun t : Real =>
          norm ((Robin1984.robinEndpointReweightDerivative t : Complex) * R t)) :=
        norm_integral_le_integral_norm _
      _ <= integral (volume.restrict (Ioi x)) (fun t : Real =>
          (r * A) * t ^ (-(2 : Real))) := by
        apply integral_mono_ae hInt.norm hMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hvNonneg := (Robin1984.robinEndpointReweightDerivative_bounds (lt_trans hx ht)).1
        have hvBound := robinEndpointReweightDerivative_le_ratio hx ht.le
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hvNonneg]
        calc
          Robin1984.robinEndpointReweightDerivative t * norm (R t) <=
              r * (t ^ (-(2 : Real)) * A) :=
            mul_le_mul hvBound (hTailBound t ht.le) (norm_nonneg _) hr
          _ = _ := by ring
      _ = r * A * x ^ (-(1 : Real)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hxPos]
        ring_nf
  have hRatio : 2 * r = 1 + 1 / (2 * Real.log x + 1) := by
    dsimp only [r]
    have hDen : Not (2 * Real.log x + 1 = 0) := by positivity
    field_simp [hDen]
    ring
  calc
    _ <= norm ((Robin1984.robinEndpointReweight x : Complex) * R x) +
        norm (integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Robin1984.robinEndpointReweightDerivative t : Complex) * R t)) := norm_add_le _ _
    _ <= r * A * x ^ (-(1 : Real)) + r * A * x ^ (-(1 : Real)) :=
      add_le_add hBoundary hIntegral
    _ = (2 * r) * A * x ^ (-(1 : Real)) := by ring
    _ = _ := by rw [hRatio]

end RobinBV.NumberField
