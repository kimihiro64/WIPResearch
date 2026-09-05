import RobinBV.NumberField.Proof.QuadraticCharacterEndpoint
import RobinBV.NumberField.Proof.QuadraticCharacterWeightedFormula
import RobinBV.NumberField.Proof.QuadraticDedekindEndpointZeros
import RobinBV.NumberField.Proof.QuadraticDedekindNicolasOmega
import RobinBV.NumberField.Proof.QuadraticRationalEndpoint

/-!
# Quadratic Dedekind ERH weighted endpoint identity

The rational and primitive quadratic-character weighted formulas are assembled
at exponent two and reweighted to the Nicolas endpoint. Under quadratic
Dedekind ERH, the endpoint error is the complete Dedekind zero sum plus an
explicit rational correction and a canonical character correction.
-/

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

theorem quadraticDedekindWeightedErrorIntegral_two_eq_explicit
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {x : Real} (hx : 2 <= x) :
    (quadraticDedekindWeightedErrorIntegral D 2 x : Complex) =
      -tsum (fun p : QuadraticDedekindZeroIndex D =>
        Robin1984.robinZeroKernel 2
          (quadraticDedekindZeroValue p) x /
            quadraticDedekindZeroValue p) -
      (Robin1984.robinTrivialZeroCorrection 2 x : Complex) -
      quadraticCharacterCorrection D 2 x := by
  have hFactors := (quadraticDedekindERH_iff D).1 hFieldERH
  exact quadraticDedekindWeightedErrorIntegral_eq_zero_sum_of_component_formulas
    D hFieldERH (by norm_num) hx
    (Robin1984.robinTrivialZeroCorrection 2 x)
    (quadraticRationalWeightedErrorIntegral_eq_zero_sum_correction
      hFactors.1 (by norm_num) hx)
    (quadraticCharacterCorrection D 2 x)
    (quadraticCharacterWeightedIntegral_eq_zero_sum_sub_correction
      D hFactors.2 (by norm_num) (by linarith))

theorem quadraticDedekindWeightedErrorIntegral_one_reweight
    (D : NumberField.OddFundamentalDiscriminant)
    {x : Real} (hx : 3 <= x) :
    And
      (IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          (quadraticDedekindWeightedErrorIntegral D 2 t : Complex))
        (Ioi x))
      ((quadraticDedekindWeightedErrorIntegral D 1 x : Complex) =
        (Robin1984.robinEndpointReweight x : Complex) *
          (quadraticDedekindWeightedErrorIntegral D 2 x : Complex) +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Robin1984.robinEndpointReweightDerivative t : Complex) *
            (quadraticDedekindWeightedErrorIntegral D 2 t : Complex))) := by
  have hxOne : 1 < x := by linarith
  have hRationalOne : IntegrableOn (fun t : Real =>
      ((Chebyshev.psi t - t : Real) : Complex) *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
    have hCast : IntegrableOn (fun t : Real =>
        (((Chebyshev.psi t - t) *
          Robin1984.robinRealWeight 1 t : Real) : Complex))
        (Ioi x) :=
      (integrableOn_quadraticRationalWeightedError_one
        (by linarith)).ofReal
    simpa only [Complex.ofReal_mul] using! hCast
  have hCharacterOne : IntegrableOn (fun t : Real =>
      (quadraticCharacterChebyshevStep D t : Complex) *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
    have hBase :=
      integrableOn_quadraticCharacterChebyshevStep_mul_weight_one D
    have hRestricted := hBase.mono_set
      (Ioi_subset_Ioi hx)
    have hCast : IntegrableOn (fun t : Real =>
        ((quadraticCharacterChebyshevStep D t *
          Robin1984.robinRealWeight 1 t : Real) : Complex))
        (Ioi x) := hRestricted.ofReal
    simpa only [Complex.ofReal_mul] using! hCast
  have hOne : IntegrableOn (fun t : Real =>
      ((quadraticDedekindChebyshevStep D t - t : Real) : Complex) *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
    apply (hRationalOne.add hCharacterOne).congr_fun _
      measurableSet_Ioi
    intro t ht
    simp only [Pi.add_apply]
    rw [quadraticDedekindChebyshevStep_eq]
    push_cast
    ring
  have hRationalTwo : IntegrableOn (fun t : Real =>
      ((Chebyshev.psi t - t : Real) : Complex) *
        (Robin1984.robinRealWeight 2 t : Complex)) (Ioi x) := by
    have hCast : IntegrableOn (fun t : Real =>
        (((Chebyshev.psi t - t) *
          Robin1984.robinRealWeight 2 t : Real) : Complex))
        (Ioi x) :=
      (integrableOn_quadraticRationalWeightedError
        (by norm_num) hxOne).ofReal
    simpa only [Complex.ofReal_mul] using! hCast
  have hCharacterTwo : IntegrableOn (fun t : Real =>
      (quadraticCharacterChebyshevStep D t : Complex) *
        (Robin1984.robinRealWeight 2 t : Complex)) (Ioi x) := by
    have hCast : IntegrableOn (fun t : Real =>
        ((quadraticCharacterChebyshevStep D t *
          Robin1984.robinRealWeight 2 t : Real) : Complex))
        (Ioi x) :=
      (integrableOn_quadraticCharacterChebyshevStep_mul_weight
        D (n := 2) (by norm_num : 2 <= (2 : Nat)) hxOne).ofReal
    simpa only [Complex.ofReal_mul] using! hCast
  have hTwo : IntegrableOn (fun t : Real =>
      ((quadraticDedekindChebyshevStep D t - t : Real) : Complex) *
        (Robin1984.robinRealWeight 2 t : Complex)) (Ioi x) := by
    apply (hRationalTwo.add hCharacterTwo).congr_fun _
      measurableSet_Ioi
    intro t ht
    simp only [Pi.add_apply]
    rw [quadraticDedekindChebyshevStep_eq]
    push_cast
    ring
  have hStepMeasurable :
      Measurable (quadraticCharacterChebyshevStep D) := by
    unfold quadraticCharacterChebyshevStep
    exact (measurable_of_countable (fun k : Nat =>
      (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum
        k D.character).re)).comp Nat.measurable_floor
  have hGMeasurable : Measurable (fun t : Real =>
      ((quadraticDedekindChebyshevStep D t - t : Real) : Complex)) := by
    apply Complex.continuous_ofReal.measurable.comp
    rw [show (fun t : Real =>
        quadraticDedekindChebyshevStep D t - t) =
      (fun t : Real =>
        Chebyshev.psi t + quadraticCharacterChebyshevStep D t - t) by
          funext t
          rw [quadraticDedekindChebyshevStep_eq]]
    exact (Chebyshev.psi_mono.measurable.add hStepMeasurable).sub
      measurable_id
  have hRaw := Robin1984.robin_weighted_integral_reweight hxOne
    (G := fun t : Real =>
      ((quadraticDedekindChebyshevStep D t - t : Real) : Complex))
    hGMeasurable hOne hTwo
  simpa only [complex_integral_mul_quadraticRationalWeight,
    quadraticDedekindWeightedErrorIntegral] using! hRaw

def quadraticCharacterEndpointCorrection
    (D : NumberField.OddFundamentalDiscriminant)
    (x : Real) : Complex :=
  (Robin1984.robinEndpointReweight x : Complex) *
      quadraticCharacterCorrection D 2 x +
    integral (volume.restrict (Ioi x)) (fun t : Real =>
      (Robin1984.robinEndpointReweightDerivative t : Complex) *
        quadraticCharacterCorrection D 2 t)

theorem integrableOn_quadraticCharacterEndpointCorrection
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {x : Real} (hx : 3 <= x) :
    IntegrableOn (fun t : Real =>
      (Robin1984.robinEndpointReweightDerivative t : Complex) *
        quadraticCharacterCorrection D 2 t) (Ioi x) := by
  have hxOne : 1 < x := by linarith
  let Z (t : Real) : Complex :=
    tsum (fun p : QuadraticDedekindZeroIndex D =>
      Robin1984.robinZeroKernel 2
        (quadraticDedekindZeroValue p) t /
          quadraticDedekindZeroValue p)
  have hJ :=
    quadraticDedekindWeightedErrorIntegral_one_reweight D hx
  have hZ :=
    quadraticDedekind_complete_zero_sum_one_reweight
      D hFieldERH hxOne
  have hR :=
    quadraticRationalTrivialZeroCorrection_one_reweight
      (by linarith : 2 <= x)
  have hCandidate : IntegrableOn (fun t : Real =>
      -((Robin1984.robinEndpointReweightDerivative t : Complex) *
        (quadraticDedekindWeightedErrorIntegral D 2 t : Complex)) -
      (Robin1984.robinEndpointReweightDerivative t : Complex) * Z t -
      (Robin1984.robinEndpointReweightDerivative t : Complex) *
        (Robin1984.robinTrivialZeroCorrection 2 t : Complex))
      (Ioi x) :=
    (hJ.1.neg.sub hZ.1).sub hR.1
  apply hCandidate.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only [Z]
  rw [quadraticDedekindWeightedErrorIntegral_two_eq_explicit
    D hFieldERH (le_trans (by linarith : 2 <= x) ht.le)]
  ring

theorem quadraticDedekindWeightedErrorIntegral_one_eq_explicit
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {x : Real} (hx : 3 <= x) :
    (quadraticDedekindWeightedErrorIntegral D 1 x : Complex) =
      -tsum (fun p : QuadraticDedekindZeroIndex D =>
        Robin1984.robinZeroKernel 1
          (quadraticDedekindZeroValue p) x /
            quadraticDedekindZeroValue p) -
      (Robin1984.robinTrivialZeroCorrection 1 x : Complex) -
      quadraticCharacterEndpointCorrection D x := by
  have hxOne : 1 < x := by linarith
  let Z (t : Real) : Complex :=
    tsum (fun p : QuadraticDedekindZeroIndex D =>
      Robin1984.robinZeroKernel 2
        (quadraticDedekindZeroValue p) t /
          quadraticDedekindZeroValue p)
  let R (t : Real) : Complex :=
    (Robin1984.robinTrivialZeroCorrection 2 t : Complex)
  let C (t : Real) : Complex :=
    quadraticCharacterCorrection D 2 t
  have hJ :=
    quadraticDedekindWeightedErrorIntegral_one_reweight D hx
  have hZ :=
    quadraticDedekind_complete_zero_sum_one_reweight
      D hFieldERH hxOne
  have hR :=
    quadraticRationalTrivialZeroCorrection_one_reweight
      (by linarith : 2 <= x)
  have hC :
      IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          C t) (Ioi x) := by
    simpa [C] using!
      integrableOn_quadraticCharacterEndpointCorrection
        D hFieldERH hx
  have hInside :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          (quadraticDedekindWeightedErrorIntegral D 2 t : Complex)) =
      -integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          Z t) -
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          R t) -
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          C t) := by
    calc
      _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
          -((Robin1984.robinEndpointReweightDerivative t : Complex) *
            Z t) -
          (Robin1984.robinEndpointReweightDerivative t : Complex) *
            R t -
          (Robin1984.robinEndpointReweightDerivative t : Complex) *
            C t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only [Z, R, C]
        rw [quadraticDedekindWeightedErrorIntegral_two_eq_explicit
          D hFieldERH
            (le_trans (by linarith : 2 <= x) ht.le)]
        ring
      _ = _ := by
        have hNegZ : IntegrableOn (fun t : Real =>
            -((Robin1984.robinEndpointReweightDerivative t : Complex) *
              Z t)) (Ioi x) := hZ.1.neg
        have hRInt : IntegrableOn (fun t : Real =>
            (Robin1984.robinEndpointReweightDerivative t : Complex) *
              R t) (Ioi x) := by
          simpa [R] using! hR.1
        have hSubZR := integral_sub hNegZ hRInt
        have hSubC := integral_sub (hNegZ.sub hRInt) hC
        simp only [Pi.sub_apply] at hSubZR hSubC
        rw [hSubC, hSubZR, integral_neg]
  rw [hJ.2,
    quadraticDedekindWeightedErrorIntegral_two_eq_explicit
      D hFieldERH (by linarith : 2 <= x),
    hInside, hZ.2, hR.2]
  unfold quadraticCharacterEndpointCorrection
  dsimp only [Z, R, C]
  ring


theorem robinEndpointReweight_bounds
    {t : Real} (ht : 1 < t) :
    And (0 <= Robin1984.robinEndpointReweight t)
      (Robin1984.robinEndpointReweight t <= t) := by
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  have hLog : 0 < Real.log t := Real.log_pos ht
  have hDen : 0 < 2 * Real.log t + 1 := by positivity
  unfold Robin1984.robinEndpointReweight
  refine And.intro ?_ ?_
  . positivity
  . calc
      t * (Real.log t + 1) / (2 * Real.log t + 1) <=
          (t * (2 * Real.log t + 1)) / (2 * Real.log t + 1) := by
        apply (div_le_div_iff_of_pos_right hDen).2
        nlinarith
      _ = t := by field_simp

theorem exists_quadraticCharacterEndpointCorrection_bound
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D) :
    Exists fun A : Real => And (0 <= A)
      (forall x : Real, 3 <= x ->
        norm (quadraticCharacterEndpointCorrection D x) <=
          2 * A * x ^ (-(1 : Real))) := by
  choose A hA hCorrection using exists_quadraticCharacterCorrection_bound D
  refine Exists.intro A (And.intro hA ?_)
  intro x hx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : Real) < 3) hx
  have hxOne : 1 < x := by linarith
  have hReweight := robinEndpointReweight_bounds hxOne
  have hPower : x * x ^ (-(2 : Real)) = x ^ (-(1 : Real)) := by
    calc
      x * x ^ (-(2 : Real)) =
          x ^ (1 : Real) * x ^ (-(2 : Real)) := by rw [Real.rpow_one]
      _ = x ^ ((1 : Real) + (-(2 : Real))) :=
        (Real.rpow_add hxPos (1 : Real) (-(2 : Real))).symm
      _ = _ := by norm_num
  have hBoundary :
      norm ((Robin1984.robinEndpointReweight x : Complex) *
        quadraticCharacterCorrection D 2 x) <=
        A * x ^ (-(1 : Real)) := by
    have hCorrectionX := hCorrection x (by linarith)
    calc
      norm ((Robin1984.robinEndpointReweight x : Complex) *
          quadraticCharacterCorrection D 2 x) =
        Robin1984.robinEndpointReweight x *
          norm (quadraticCharacterCorrection D 2 x) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hReweight.1]
      _ <= x * (A * x ^ (-(2 : Real))) :=
        mul_le_mul hReweight.2 hCorrectionX (norm_nonneg _) hxPos.le
      _ = A * x ^ (-(1 : Real)) := by
        rw [show x * (A * x ^ (-(2 : Real))) =
          A * (x * x ^ (-(2 : Real))) by ring, hPower]
  have hIntegrable := integrableOn_quadraticCharacterEndpointCorrection
    D hFieldERH hx
  have hMajor : IntegrableOn (fun t : Real => A * t ^ (-(2 : Real)))
      (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-(2 : Real)) < -1) hxPos).const_mul A
  have hIntegral :
      norm (integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          quadraticCharacterCorrection D 2 t)) <=
        A * x ^ (-(1 : Real)) := by
    calc
      norm (integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Robin1984.robinEndpointReweightDerivative t : Complex) *
            quadraticCharacterCorrection D 2 t)) <=
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          norm ((Robin1984.robinEndpointReweightDerivative t : Complex) *
            quadraticCharacterCorrection D 2 t)) :=
        norm_integral_le_integral_norm _
      _ <= integral (volume.restrict (Ioi x))
          (fun t : Real => A * t ^ (-(2 : Real))) := by
        apply integral_mono_ae hIntegrable.norm hMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have htOne : 1 < t := lt_trans hxOne ht
        have htTwo : 2 <= t := le_trans (by linarith : 2 <= x) ht.le
        have hDerivative :=
          Robin1984.robinEndpointReweightDerivative_bounds htOne
        have hCorrectionT := hCorrection t htTwo
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hDerivative.1]
        calc
          Robin1984.robinEndpointReweightDerivative t *
              norm (quadraticCharacterCorrection D 2 t) <=
            norm (quadraticCharacterCorrection D 2 t) := by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right
                hDerivative.2 (norm_nonneg _)
          _ <= A * t ^ (-(2 : Real)) := hCorrectionT
      _ = A * x ^ (-(1 : Real)) := by
        rw [integral_const_mul,
          integral_Ioi_rpow_of_lt (by norm_num) hxPos]
        ring_nf
  unfold quadraticCharacterEndpointCorrection
  calc
    norm ((Robin1984.robinEndpointReweight x : Complex) *
          quadraticCharacterCorrection D 2 x +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Robin1984.robinEndpointReweightDerivative t : Complex) *
            quadraticCharacterCorrection D 2 t)) <=
      norm ((Robin1984.robinEndpointReweight x : Complex) *
          quadraticCharacterCorrection D 2 x) +
        norm (integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Robin1984.robinEndpointReweightDerivative t : Complex) *
            quadraticCharacterCorrection D 2 t)) := norm_add_le _ _
    _ <= A * x ^ (-(1 : Real)) + A * x ^ (-(1 : Real)) :=
      add_le_add hBoundary hIntegral
    _ = _ := by ring

theorem eventually_norm_quadraticCharacterEndpointCorrection_le
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      norm (quadraticCharacterEndpointCorrection D x) <=
        epsilon / (Real.sqrt x * Real.log x)) Filter.atTop := by
  choose A hA hEndpoint using
    exists_quadraticCharacterEndpointCorrection_bound D hFieldERH
  by_cases hAZero : A = 0
  next =>
    filter_upwards [Filter.eventually_ge_atTop (3 : Real)] with x hx
    have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : Real) < 3) hx
    have hLogPos : 0 < Real.log x := Real.log_pos (by linarith)
    have hDenPos : 0 < Real.sqrt x * Real.log x :=
      mul_pos (Real.sqrt_pos.2 hxPos) hLogPos
    have hZero : norm (quadraticCharacterEndpointCorrection D x) <= 0 := by
      simpa only [hAZero, mul_zero, zero_mul] using hEndpoint x hx
    exact hZero.trans (div_nonneg hEpsilon.le hDenPos.le)
  next =>
    have hAPos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAZero)
    let delta : Real := epsilon / (2 * A)
    have hDelta : 0 < delta := by
      dsimp only [delta]
      positivity
    have hLogSqrt :=
      (isLittleO_log_rpow_atTop
        (by norm_num : (0 : Real) < 1 / 2)).bound hDelta
    filter_upwards [hLogSqrt,
      Filter.eventually_ge_atTop (3 : Real)] with x hLog hx
    have hxPos : 0 < x :=
      lt_of_lt_of_le (by norm_num : (0 : Real) < 3) hx
    have hxOne : 1 < x := by linarith
    have hLogPos : 0 < Real.log x := Real.log_pos hxOne
    have hSqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxPos
    have hLog' : Real.log x <= delta * Real.sqrt x := by
      have hRpowPos : 0 < x ^ (1 / 2 : Real) :=
        Real.rpow_pos_of_pos hxPos _
      simpa only [Real.norm_eq_abs, abs_of_pos hLogPos,
        abs_of_pos hRpowPos, Real.sqrt_eq_rpow] using hLog
    have hScaled :
        2 * A * Real.log x <= epsilon * Real.sqrt x := by
      have hMul := mul_le_mul_of_nonneg_left hLog'
        (mul_nonneg (by norm_num : (0 : Real) <= 2) hA)
      have hDeltaEq : 2 * A * delta = epsilon := by
        dsimp only [delta]
        field_simp [ne_of_gt hAPos]
      calc
        2 * A * Real.log x <= 2 * A * (delta * Real.sqrt x) := by
          simpa only [mul_assoc] using hMul
        _ = epsilon * Real.sqrt x := by rw [<- mul_assoc, hDeltaEq]
    have hRatioNonneg : 0 <= Real.sqrt x / x := by positivity
    have hKey :
        (2 * A * x ^ (-(1 : Real))) *
            (Real.sqrt x * Real.log x) <= epsilon := by
      have hMul := mul_le_mul_of_nonneg_right hScaled hRatioNonneg
      have hSqrtSq : Real.sqrt x * Real.sqrt x = x :=
        Real.mul_self_sqrt hxPos.le
      calc
        (2 * A * x ^ (-(1 : Real))) *
            (Real.sqrt x * Real.log x) =
          (2 * A * Real.log x) * (Real.sqrt x / x) := by
            rw [Real.rpow_neg_one]
            field_simp [ne_of_gt hxPos]
        _ <= (epsilon * Real.sqrt x) * (Real.sqrt x / x) := hMul
        _ = epsilon := by
          rw [div_eq_mul_inv]
          calc
            (epsilon * Real.sqrt x) * (Real.sqrt x * Inv.inv x) =
                epsilon * (Real.sqrt x * Real.sqrt x) * Inv.inv x := by ring
            _ = epsilon * x * Inv.inv x := by rw [hSqrtSq]
            _ = epsilon := by field_simp [ne_of_gt hxPos]
    have hDenPos : 0 < Real.sqrt x * Real.log x :=
      mul_pos hSqrtPos hLogPos
    calc
      norm (quadraticCharacterEndpointCorrection D x) <=
          2 * A * x ^ (-(1 : Real)) := hEndpoint x hx
      _ = ((2 * A * x ^ (-(1 : Real))) *
          (Real.sqrt x * Real.log x)) /
            (Real.sqrt x * Real.log x) := by
        field_simp [ne_of_gt hDenPos]
      _ <= epsilon / (Real.sqrt x * Real.log x) :=
        (div_le_div_iff_of_pos_right hDenPos).2 hKey


theorem eventually_robinTrivialZeroCorrection_one_le
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      Robin1984.robinTrivialZeroCorrection 1 x <=
        epsilon / (Real.sqrt x * Real.log x)) Filter.atTop := by
  let C : Real := Real.log (2 * Real.pi)
  have hC : 0 < C := by
    dsimp only [C]
    apply Real.log_pos
    nlinarith [Real.pi_gt_three]
  have hLarge := (tendsto_rpow_atTop
    (by norm_num : (0 : Real) < 1 / 2)).eventually
      (Filter.eventually_ge_atTop (C / epsilon))
  filter_upwards [hLarge,
    Filter.eventually_ge_atTop (2 : Real)] with x hLarge hx
  have hxPos : 0 < x :=
    lt_of_lt_of_le (by norm_num : (0 : Real) < 2) hx
  have hxOne : 1 < x := by linarith
  have hLogPos : 0 < Real.log x := Real.log_pos hxOne
  have hSqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxPos
  have hSqrtLarge : C / epsilon <= Real.sqrt x := by
    simpa only [Real.sqrt_eq_rpow] using hLarge
  have hScale : C <= epsilon * Real.sqrt x := by
    have hMul := mul_le_mul_of_nonneg_left hSqrtLarge hEpsilon.le
    have hEpsilonNe : Not (epsilon = 0) := ne_of_gt hEpsilon
    calc
      C = epsilon * (C / epsilon) := by field_simp [hEpsilonNe]
      _ <= epsilon * Real.sqrt x := hMul
  have hCorr := Robin1984.robinTrivialZeroCorrection_bounds
    (n := 1) (by norm_num : 1 <= (1 : Nat)) hx
  have hSqrtSq : Real.sqrt x * Real.sqrt x = x :=
    Real.mul_self_sqrt hxPos.le
  have hDenPos : 0 < x * Real.log x := mul_pos hxPos hLogPos
  have hCriticalEq :
      epsilon / (Real.sqrt x * Real.log x) =
        (epsilon * Real.sqrt x) / (x * Real.log x) := by
    field_simp [ne_of_gt hxPos, ne_of_gt hLogPos, ne_of_gt hSqrtPos]
    nlinarith
  calc
    Robin1984.robinTrivialZeroCorrection 1 x <=
        C * x ^ (-(1 : Real)) * Inv.inv (Real.log x) := by
      simpa only [C, Nat.cast_one] using hCorr.2
    _ = C / (x * Real.log x) := by
      rw [Real.rpow_neg_one]
      field_simp [ne_of_gt hxPos, ne_of_gt hLogPos]
    _ <= (epsilon * Real.sqrt x) / (x * Real.log x) :=
      (div_le_div_iff_of_pos_right hDenPos).2 hScale
    _ = epsilon / (Real.sqrt x * Real.log x) := hCriticalEq.symm

theorem eventually_norm_quadraticDedekindWeightedErrorIntegral_one_le
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      norm (quadraticDedekindWeightedErrorIntegral D 1 x : Complex) <=
        (quadraticDedekindZeroMass D + epsilon) /
          (Real.sqrt x * Real.log x)) Filter.atTop := by
  let delta : Real := epsilon / 3
  have hDelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hZero :=
    eventually_norm_tsum_quadraticDedekind_robinZeroKernel_one_le_div
      D hFieldERH hDelta
  have hRational :=
    eventually_robinTrivialZeroCorrection_one_le hDelta
  have hCharacter :=
    eventually_norm_quadraticCharacterEndpointCorrection_le
      D hFieldERH hDelta
  filter_upwards [hZero, hRational, hCharacter,
    Filter.eventually_ge_atTop (3 : Real)] with x hZero hRational hCharacter hx
  let Z : Complex := tsum (fun p : QuadraticDedekindZeroIndex D =>
    Robin1984.robinZeroKernel 1 (quadraticDedekindZeroValue p) x /
      quadraticDedekindZeroValue p)
  let R : Complex := (Robin1984.robinTrivialZeroCorrection 1 x : Complex)
  let C : Complex := quadraticCharacterEndpointCorrection D x
  have hFormula :=
    quadraticDedekindWeightedErrorIntegral_one_eq_explicit D hFieldERH hx
  have hRNonneg := (Robin1984.robinTrivialZeroCorrection_bounds
    (n := 1) (by norm_num : 1 <= (1 : Nat)) (by linarith : 2 <= x)).1
  have hRNorm : norm R = Robin1984.robinTrivialZeroCorrection 1 x := by
    dsimp only [R]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hRNonneg]
  rw [hFormula]
  change norm (-Z - R - C) <= _
  calc
    norm (-Z - R - C) <= norm (-Z - R) + norm C := norm_sub_le _ _
    _ <= (norm (-Z) + norm R) + norm C :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ = norm Z + Robin1984.robinTrivialZeroCorrection 1 x + norm C := by
      rw [norm_neg, hRNorm]
    _ <= (quadraticDedekindZeroMass D + delta) /
          (Real.sqrt x * Real.log x) +
        delta / (Real.sqrt x * Real.log x) +
        delta / (Real.sqrt x * Real.log x) :=
      add_le_add (add_le_add hZero hRational) hCharacter
    _ = (quadraticDedekindZeroMass D + epsilon) /
          (Real.sqrt x * Real.log x) := by
      dsimp only [delta]
      ring

theorem eventually_norm_quadraticDedekindWeightedErrorIntegral_one_le_of_zetaERH
    (D : NumberField.OddFundamentalDiscriminant)
    (hZetaERH : QuadraticDedekindZetaERH D)
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      norm (quadraticDedekindWeightedErrorIntegral D 1 x : Complex) <=
        (quadraticDedekindZeroMass D + epsilon) /
          (Real.sqrt x * Real.log x)) Filter.atTop := by
  exact eventually_norm_quadraticDedekindWeightedErrorIntegral_one_le
    D ((quadraticDedekindZetaERH_iff_carrierERH D).1 hZetaERH) hEpsilon


def QuadraticDedekindCriticalJBound
    (D : NumberField.OddFundamentalDiscriminant) : Prop :=
  Exists fun C : Real => And (0 <= C)
    (Filter.Eventually (fun x : Real =>
      norm (quadraticDedekindNicolasJ D x) <=
        C / (Real.sqrt x * Real.log x)) Filter.atTop)

theorem not_atTopOmegaMinus_of_isLittleO
    {f h : Real -> Real}
    (hPos : Filter.Eventually (fun x : Real => 0 < h x) Filter.atTop)
    (hLittle : Asymptotics.IsLittleO Filter.atTop f h) :
    Not (Robin1984.AtTopOmegaMinus f h) := by
  intro hOmega
  unfold Robin1984.AtTopOmegaMinus at hOmega
  unfold Asymptotics.AtTopOmegaMinus Asymptotics.AtTopOmegaPlus at hOmega
  choose c hc hExcursion using hOmega
  have hSmall := hLittle.bound (half_pos hc)
  choose X hX using Filter.eventually_atTop.mp (hSmall.and hPos)
  choose x hx hExcursionX using hExcursion X
  have hData := hX x hx
  have hScalePos := hData.2
  have hSmallX : abs (f x) <= (c / 2) * h x := by
    simpa only [Real.norm_eq_abs, abs_of_pos hScalePos] using hData.1
  have hNegUpper : -f x <= abs (f x) := neg_le_abs (f x)
  nlinarith

theorem quadraticDedekindCriticalJBound_of_zetaERH
    (D : NumberField.OddFundamentalDiscriminant)
    (hZetaERH : QuadraticDedekindZetaERH D) :
    QuadraticDedekindCriticalJBound D := by
  let C : Real := quadraticDedekindZeroMass D + 1
  have hC : 0 <= C := by
    dsimp only [C]
    have hMass := quadraticDedekindZeroMass_nonneg D
    linarith
  have hWeighted :=
    eventually_norm_quadraticDedekindWeightedErrorIntegral_one_le_of_zetaERH
      D hZetaERH (by norm_num : (0 : Real) < 1)
  refine Exists.intro C (And.intro hC ?_)
  filter_upwards [hWeighted,
    Filter.eventually_ge_atTop (1 : Real)] with x hWeighted hx
  rw [quadraticDedekindWeightedErrorIntegral_one_eq_nicolasJ D hx] at hWeighted
  simpa only [C, Complex.norm_real, Real.norm_eq_abs] using hWeighted

theorem quadraticDedekindZetaERH_of_criticalJBound
    (D : NumberField.OddFundamentalDiscriminant)
    (hCritical : QuadraticDedekindCriticalJBound D) :
    QuadraticDedekindZetaERH D := by
  choose C hC hBound using hCritical
  have hBigO : Asymptotics.IsBigO Filter.atTop
      (quadraticDedekindNicolasJ D)
      (fun x : Real => x ^ (-(1 / 2 : Real))) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hBound,
      Filter.eventually_ge_atTop (Real.exp 1)] with x hBound hx
    have hxPos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
    have hLogOne : 1 <= Real.log x := by
      have hLog := Real.log_le_log (Real.exp_pos 1) hx
      simpa only [Real.log_exp] using hLog
    have hInvLog : Inv.inv (Real.log x) <= 1 := by
      simpa only [one_div, inv_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hLogOne
    have hPowerNonneg : 0 <= x ^ (-(1 / 2 : Real)) :=
      Real.rpow_nonneg hxPos.le _
    calc
      norm (quadraticDedekindNicolasJ D x) <=
          C / (Real.sqrt x * Real.log x) := hBound
      _ = C * (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) := by
        rw [quadraticCriticalKernelBase_eq hxPos.le]
        ring
      _ <= C * x ^ (-(1 / 2 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hInvLog hPowerNonneg
      _ = C * norm (x ^ (-(1 / 2 : Real))) := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxPos _)]
  by_contra hNotERH
  choose b hbPos hbHalf hOmega using
    exists_quadraticDedekindNicolasJ_omegaMinus_of_not_ERH D hNotERH
  have hLittle : Asymptotics.IsLittleO Filter.atTop
      (quadraticDedekindNicolasJ D) (fun x : Real => x ^ (-b)) :=
    hBigO.trans_isLittleO
      (Robin1984.rpow_neg_oneHalf_isLittleO_rpow_neg hbHalf)
  have hScalePos : Filter.Eventually
      (fun x : Real => 0 < x ^ (-b)) Filter.atTop := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    exact Real.rpow_pos_of_pos hx _
  exact (not_atTopOmegaMinus_of_isLittleO hScalePos hLittle) hOmega

theorem quadraticDedekindZetaERH_iff_criticalJBound
    (D : NumberField.OddFundamentalDiscriminant) :
    QuadraticDedekindZetaERH D <-> QuadraticDedekindCriticalJBound D :=
  Iff.intro (quadraticDedekindCriticalJBound_of_zetaERH D)
    (quadraticDedekindZetaERH_of_criticalJBound D)


end

end RobinBV.NumberField
