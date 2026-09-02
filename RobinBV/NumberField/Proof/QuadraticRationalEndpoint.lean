import RobinBV.NumberField.Proof.QuadraticDedekindWeightedError
import Robin1984.NicolasLandau.NicolasOscillation
import Robin1984.NicolasLandau.WeightedEndpointZeros
import Robin1984.NicolasLandau.WeightedTrivialCorrection

/-!
# Collision-free rational endpoint formula

Robin1984 proves the weighted Chebyshev-error formula at the endpoint `n = 1`,
but its monolithic endpoint arithmetic module cannot coexist with the current
Bombieri-Vinogradov dependency because both dependency trees declare a global
prime-counting function. This module reconstructs only that arithmetic wrapper
from compatible proved components. It then removes the rational-component
hypothesis from the quadratic Dedekind endpoint assembly.
-/

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

theorem quadraticRationalRealWeight_one_eq_nicolasTailKernel
    {t : Real} (ht : 1 < t) :
    Robin1984.robinRealWeight 1 t = Robin1984.nicolasTailKernel t := by
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  unfold Robin1984.robinRealWeight Robin1984.nicolasTailKernel
  norm_num [Real.rpow_neg htPos.le]
  field_simp [htPos.ne', (Real.log_pos ht).ne'] <;> ring

theorem integrableOn_quadraticRationalWeightedError_one
    {x : Real} (hx : 2 <= x) :
    IntegrableOn (fun t : Real =>
      (Chebyshev.psi t - t) * Robin1984.robinRealWeight 1 t) (Ioi x) := by
  have hTail : IntegrableOn (fun t : Real =>
      (Chebyshev.psi t - t) * Robin1984.robinRealWeight 1 t) (Ioi 3) := by
    apply Robin1984.nicolasPsiTail_integrableOn_Ioi_three.congr_fun _
      measurableSet_Ioi
    intro t ht
    dsimp only [Robin1984.nicolasPsiError]
    rw [quadraticRationalRealWeight_one_eq_nicolasTailKernel
      (lt_trans (by norm_num : (1 : Real) < 3) ht)]
  have hWeight : IntegrableOn (Robin1984.robinRealWeight 1) (Ioc 2 3) :=
    (Robin1984.integrableOn_robinRealWeight
      (by norm_num : 1 <= (1 : Nat)) (by norm_num : (1 : Real) < 2)).mono_set
        Ioc_subset_Ioi_self
  have hProduct : IntegrableOn (fun t : Real =>
      Robin1984.robinRealWeight 1 t * (Chebyshev.psi t - t)) (Ioc 2 3) := by
    apply hWeight.mul_bdd (c := Chebyshev.psi 3 + 3)
    next =>
      exact (Chebyshev.psi_mono.measurable.sub measurable_id).aestronglyMeasurable
    next =>
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs]
      calc
        abs (Chebyshev.psi t - t) <=
            abs (Chebyshev.psi t) + abs t := abs_sub _ _
        _ = Chebyshev.psi t + t := by
          rw [abs_of_nonneg (Chebyshev.psi_nonneg t),
            abs_of_nonneg (by linarith [ht.1])]
        _ <= Chebyshev.psi 3 + 3 :=
          add_le_add (Chebyshev.psi_mono ht.2) ht.2
  have hCompact : IntegrableOn (fun t : Real =>
      (Chebyshev.psi t - t) * Robin1984.robinRealWeight 1 t) (Ioc 2 3) := by
    simpa only [mul_comm] using hProduct
  have hAll := hCompact.union hTail
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (2 : Real) <= 3)] at hAll
  exact hAll.mono_set (Ioi_subset_Ioi hx)

theorem complex_integral_mul_quadraticRationalWeight
    (g : Real -> Real) (n : Nat) (x : Real) :
    integral (volume.restrict (Ioi x)) (fun t : Real =>
        (g t : Complex) * (Robin1984.robinRealWeight n t : Complex)) =
      ((integral (volume.restrict (Ioi x)) (fun t : Real =>
        g t * Robin1984.robinRealWeight n t) : Real) : Complex) := by
  simp_rw [<- Complex.ofReal_mul]
  exact integral_complex_ofReal

theorem quadraticRationalZeroKernel_one_eq_integral_t_weight
    (n : Nat) {x : Real} (hx : 1 < x) :
    Robin1984.robinZeroKernel n 1 x =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        ((t * Robin1984.robinRealWeight n t : Real) : Complex)) := by
  rw [Robin1984.robinZeroKernel_eq_integral_cpow_weight n 1 hx]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp

theorem quadraticRationalWeightedErrorIntegral_eq_zero_sum_correction
    (hRH : RiemannHypothesis) {n : Nat} (hn : 2 <= n)
    {x : Real} (hx : 2 <= x) :
    (quadraticRationalWeightedErrorIntegral n x : Complex) =
      -tsum (fun p : RiemannXiDivisorZeroIndex =>
        Robin1984.robinZeroKernel n (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p) -
        (Robin1984.robinTrivialZeroCorrection n x : Complex) := by
  have hxOne : 1 < x := by linarith
  have hnOne : 1 <= n := by omega
  have hPsi := Robin1984.integrableOn_complex_psi_robinRealWeight hn hxOne
  have hErrorReal := integrableOn_quadraticRationalWeightedError hn hxOne
  have hError : IntegrableOn (fun t : Real =>
      (((Chebyshev.psi t - t) * Robin1984.robinRealWeight n t : Real) :
        Complex)) (Ioi x) := hErrorReal.ofReal
  have hMainRaw := hPsi.sub hError
  have hMain : IntegrableOn (fun t : Real =>
      ((t * Robin1984.robinRealWeight n t : Real) : Complex)) (Ioi x) := by
    apply hMainRaw.congr_fun _ measurableSet_Ioi
    intro t ht
    simp only [Pi.sub_apply]
    push_cast
    ring
  have hErrorIdentity :
      (quadraticRationalWeightedErrorIntegral n x : Complex) =
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          ((Chebyshev.psi t * Robin1984.robinRealWeight n t : Real) :
            Complex)) -
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          ((t * Robin1984.robinRealWeight n t : Real) : Complex)) := by
    rw [quadraticRationalWeightedErrorIntegral, <- integral_complex_ofReal]
    have hFunction : (fun t : Real =>
        (((Chebyshev.psi t - t) * Robin1984.robinRealWeight n t : Real) :
          Complex)) =
        (fun t : Real =>
          ((Chebyshev.psi t * Robin1984.robinRealWeight n t : Real) :
            Complex) -
          ((t * Robin1984.robinRealWeight n t : Real) : Complex)) := by
      funext t
      push_cast
      ring
    rw [hFunction]
    exact integral_sub hPsi hMain
  rw [hErrorIdentity,
    <- Robin1984.robinPrimePowerSum_eq_integral_psi_weight hn hxOne,
    <- quadraticRationalZeroKernel_one_eq_integral_t_weight n hxOne,
    Robin1984.robinPrimePowerSum_eq_weighted_explicit_series hRH hn hxOne]
  have hCorrection := Robin1984.robin_explicit_correction_eq hnOne hx
  linear_combination hCorrection

theorem quadraticRationalWeightedErrorIntegral_one_reweight
    {x : Real} (hx : 2 <= x) :
    And
      (IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          (quadraticRationalWeightedErrorIntegral 2 t : Complex)) (Ioi x))
      ((quadraticRationalWeightedErrorIntegral 1 x : Complex) =
        (Robin1984.robinEndpointReweight x : Complex) *
            (quadraticRationalWeightedErrorIntegral 2 x : Complex) +
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            (Robin1984.robinEndpointReweightDerivative t : Complex) *
              (quadraticRationalWeightedErrorIntegral 2 t : Complex))) := by
  have hxOne : 1 < x := by linarith
  have hOne : IntegrableOn (fun t : Real =>
      ((Chebyshev.psi t - t : Real) : Complex) *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
    have hCast : IntegrableOn (fun t : Real =>
        (((Chebyshev.psi t - t) * Robin1984.robinRealWeight 1 t : Real) :
          Complex)) (Ioi x) :=
      (integrableOn_quadraticRationalWeightedError_one hx).ofReal
    simpa only [Complex.ofReal_mul] using! hCast
  have hTwo : IntegrableOn (fun t : Real =>
      ((Chebyshev.psi t - t : Real) : Complex) *
        (Robin1984.robinRealWeight 2 t : Complex)) (Ioi x) := by
    have hCast : IntegrableOn (fun t : Real =>
        (((Chebyshev.psi t - t) * Robin1984.robinRealWeight 2 t : Real) :
          Complex)) (Ioi x) :=
      (integrableOn_quadraticRationalWeightedError
        (by norm_num : 2 <= (2 : Nat)) hxOne).ofReal
    simpa only [Complex.ofReal_mul] using! hCast
  have hRaw := Robin1984.robin_weighted_integral_reweight hxOne
    (G := fun t : Real => ((Chebyshev.psi t - t : Real) : Complex))
    (Complex.continuous_ofReal.measurable.comp
      (Chebyshev.psi_mono.measurable.sub measurable_id)) hOne hTwo
  simpa only [complex_integral_mul_quadraticRationalWeight,
    quadraticRationalWeightedErrorIntegral] using! hRaw

theorem quadraticRationalTrivialZeroCorrection_one_reweight
    {x : Real} (hx : 2 <= x) :
    And
      (IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          (Robin1984.robinTrivialZeroCorrection 2 t : Complex)) (Ioi x))
      ((Robin1984.robinTrivialZeroCorrection 1 x : Complex) =
        (Robin1984.robinEndpointReweight x : Complex) *
            (Robin1984.robinTrivialZeroCorrection 2 x : Complex) +
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            (Robin1984.robinEndpointReweightDerivative t : Complex) *
              (Robin1984.robinTrivialZeroCorrection 2 t : Complex))) := by
  have hxOne : 1 < x := by linarith
  have hInt (n : Nat) (hn : 1 <= n) : IntegrableOn (fun t : Real =>
      (Robin1984.robinTrivialZeroCorrectionFactor t : Complex) *
        (Robin1984.robinRealWeight n t : Complex)) (Ioi x) := by
    have hCast : IntegrableOn (fun t : Real =>
        ((Robin1984.robinRealWeight n t *
          Robin1984.robinTrivialZeroCorrectionFactor t : Real) : Complex))
        (Ioi x) :=
      (Robin1984.integrableOn_robinTrivialZeroCorrection_integrand hn hx).ofReal
    simpa only [Complex.ofReal_mul, mul_comm] using! hCast
  have hEq (n : Nat) (a : Real) :
      integral (volume.restrict (Ioi a)) (fun t : Real =>
        (Robin1984.robinTrivialZeroCorrectionFactor t : Complex) *
          (Robin1984.robinRealWeight n t : Complex)) =
        (Robin1984.robinTrivialZeroCorrection n a : Complex) := by
    rw [complex_integral_mul_quadraticRationalWeight]
    unfold Robin1984.robinTrivialZeroCorrection
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    exact mul_comm _ _
  have hRaw := Robin1984.robin_weighted_integral_reweight hxOne
    (G := fun t : Real =>
      (Robin1984.robinTrivialZeroCorrectionFactor t : Complex))
    (by unfold Robin1984.robinTrivialZeroCorrectionFactor; fun_prop)
    (hInt 1 (by norm_num)) (hInt 2 (by norm_num))
  simpa only [hEq] using! hRaw

theorem quadraticRationalWeightedErrorIntegral_one_eq_zero_sum_correction
    (hRH : RiemannHypothesis) {x : Real} (hx : 2 <= x) :
    (quadraticRationalWeightedErrorIntegral 1 x : Complex) =
      -tsum (fun p : RiemannXiDivisorZeroIndex =>
        Robin1984.robinZeroKernel 1 (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p) -
        (Robin1984.robinTrivialZeroCorrection 1 x : Complex) := by
  have hxOne : 1 < x := by linarith
  let Z (t : Real) : Complex := tsum (fun p : RiemannXiDivisorZeroIndex =>
    Robin1984.robinZeroKernel 2 (riemannXiDivisorZeroValue p) t /
      riemannXiDivisorZeroValue p)
  have hJ := quadraticRationalWeightedErrorIntegral_one_reweight hx
  have hC := quadraticRationalTrivialZeroCorrection_one_reweight hx
  have hZ := Robin1984.robin_complete_zero_sum_one_reweight hRH hxOne
  have hInside : integral (volume.restrict (Ioi x)) (fun t : Real =>
      (Robin1984.robinEndpointReweightDerivative t : Complex) *
        (quadraticRationalWeightedErrorIntegral 2 t : Complex)) =
      -integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) * Z t) -
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Robin1984.robinEndpointReweightDerivative t : Complex) *
            (Robin1984.robinTrivialZeroCorrection 2 t : Complex)) := by
    calc
      _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
          -((Robin1984.robinEndpointReweightDerivative t : Complex) * Z t) -
            (Robin1984.robinEndpointReweightDerivative t : Complex) *
              (Robin1984.robinTrivialZeroCorrection 2 t : Complex)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [quadraticRationalWeightedErrorIntegral_eq_zero_sum_correction
          hRH (by norm_num : 2 <= (2 : Nat)) (le_trans hx ht.le)]
        dsimp only [Z]
        ring
      _ = _ := by
        have hNeg : IntegrableOn (fun t : Real =>
            -((Robin1984.robinEndpointReweightDerivative t : Complex) * Z t))
            (Ioi x) := hZ.1.neg
        rw [integral_sub hNeg hC.1, integral_neg]
  rw [hJ.2,
    quadraticRationalWeightedErrorIntegral_eq_zero_sum_correction hRH
      (by norm_num : 2 <= (2 : Nat)) hx,
    hInside, hZ.2, hC.2]
  dsimp only [Z]
  ring

theorem quadraticRationalWeightedErrorIntegral_eq_zero_sum_correction_all
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n)
    {x : Real} (hx : 2 <= x) :
    (quadraticRationalWeightedErrorIntegral n x : Complex) =
      -tsum (fun p : RiemannXiDivisorZeroIndex =>
        Robin1984.robinZeroKernel n (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p) -
        (Robin1984.robinTrivialZeroCorrection n x : Complex) := by
  by_cases hOne : n = 1
  next =>
    subst n
    exact quadraticRationalWeightedErrorIntegral_one_eq_zero_sum_correction
      hRH hx
  next =>
    exact quadraticRationalWeightedErrorIntegral_eq_zero_sum_correction
      hRH (by omega) hx

theorem quadraticDedekindWeightedErrorIntegral_one_eq_add
    (D : NumberField.OddFundamentalDiscriminant)
    {x : Real} (hx : 2 <= x)
    (hCharacter : IntegrableOn (fun t : Real =>
      quadraticCharacterChebyshevStep D t *
        Robin1984.robinRealWeight 1 t) (Ioi x)) :
    quadraticDedekindWeightedErrorIntegral D 1 x =
      quadraticRationalWeightedErrorIntegral 1 x +
        quadraticCharacterWeightedIntegral D 1 x := by
  have hRational := integrableOn_quadraticRationalWeightedError_one hx
  unfold quadraticDedekindWeightedErrorIntegral
  unfold quadraticRationalWeightedErrorIntegral
  unfold quadraticCharacterWeightedIntegral
  have hFunction : (fun t : Real =>
      (quadraticDedekindChebyshevStep D t - t) *
        Robin1984.robinRealWeight 1 t) =
      (fun t : Real =>
        (Chebyshev.psi t - t) * Robin1984.robinRealWeight 1 t +
          quadraticCharacterChebyshevStep D t *
            Robin1984.robinRealWeight 1 t) := by
    funext t
    rw [quadraticDedekindChebyshevStep_eq]
    ring
  rw [hFunction, integral_add hRational hCharacter]

theorem quadraticDedekindWeightedErrorIntegral_one_eq_zero_sum_of_character_formula
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {x : Real} (hx : 2 <= x)
    (hCharacterIntegrable : IntegrableOn (fun t : Real =>
      quadraticCharacterChebyshevStep D t *
        Robin1984.robinRealWeight 1 t) (Ioi x))
    (characterCorrection : Complex)
    (hCharacterFormula :
      (quadraticCharacterWeightedIntegral D 1 x : Complex) =
        -tsum (fun p : QuadraticLZeroIndex D.character =>
          Robin1984.robinZeroKernel 1 (quadraticLZeroValue p) x /
            quadraticLZeroValue p) - characterCorrection) :
    (quadraticDedekindWeightedErrorIntegral D 1 x : Complex) =
      -tsum (fun p : QuadraticDedekindZeroIndex D =>
        Robin1984.robinZeroKernel 1 (quadraticDedekindZeroValue p) x /
          quadraticDedekindZeroValue p) -
        (Robin1984.robinTrivialZeroCorrection 1 x : Complex) -
        characterCorrection := by
  have hFactors := (quadraticDedekindERH_iff D).1 hFieldERH
  have hPrimeSplit :=
    quadraticDedekindWeightedErrorIntegral_one_eq_add D hx
      hCharacterIntegrable
  have hRationalFormula :=
    quadraticRationalWeightedErrorIntegral_one_eq_zero_sum_correction
      hFactors.1 hx
  have hZeroSplit :=
    tsum_quadraticDedekind_robinZeroKernel_eq_add
      D hFieldERH (n := 1) (x := x) (by norm_num) (by linarith)
  rw [hPrimeSplit, Complex.ofReal_add, hRationalFormula,
    hCharacterFormula, hZeroSplit]
  ring

end

end RobinBV.NumberField
