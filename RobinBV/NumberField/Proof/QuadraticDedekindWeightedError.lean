import Robin1984.NicolasLandau.WeightedPsiIntegral
import RobinBV.NumberField.Proof.QuadraticDedekindPrimeSide
import RobinBV.NumberField.Proof.QuadraticDedekindZeroMass

/-!
# Weighted quadratic Dedekind Chebyshev error

This module carries the exact rational-plus-character Chebyshev split through
Robin's weighted tail transform. It also proves ERH summability of the same
Robin zero kernel over quadratic L-zeros and combines the two zero families
through the multiplicity-preserving quadratic Dedekind zero-index equivalence.
The final theorem is a modular field explicit formula: once a character-side
weighted formula is supplied, the full quadratic Dedekind formula follows.
-/

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

def quadraticDedekindChebyshevStep
    (D : NumberField.OddFundamentalDiscriminant) (t : Real) : Real :=
  (quadraticDedekindChebyshevSum D (Nat.floor t)).re

def quadraticCharacterChebyshevStep
    (D : NumberField.OddFundamentalDiscriminant) (t : Real) : Real :=
  (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum
    (Nat.floor t) D.character).re

theorem quadraticDedekindChebyshevStep_eq
    (D : NumberField.OddFundamentalDiscriminant) (t : Real) :
    quadraticDedekindChebyshevStep D t =
      Chebyshev.psi t + quadraticCharacterChebyshevStep D t := by
  unfold quadraticDedekindChebyshevStep
  unfold quadraticCharacterChebyshevStep
  rw [quadraticDedekindChebyshevSum_re_eq]
  congr 1
  exact (Chebyshev.psi_eq_psi_coe_floor t).symm

theorem norm_quadraticCharacterChebyshevSum_le_psi
    (D : NumberField.OddFundamentalDiscriminant) (x : Nat) :
    norm (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum
      x D.character) <= Chebyshev.psi x := by
  have hAll : forall S : Finset Nat,
      norm (S.sum fun n =>
        (ArithmeticFunction.vonMangoldt n : Complex) * D.character n) <=
      S.sum fun n => ArithmeticFunction.vonMangoldt n := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert n S hn ih =>
      rw [Finset.sum_insert hn, Finset.sum_insert hn]
      apply le_trans (norm_add_le _ _)
      apply add_le_add
      next =>
        rcases D.character_isQuadratic n with hZero | hOne | hNeg
        next => rw [hZero]; simp [ArithmeticFunction.vonMangoldt_nonneg]
        next =>
          rw [hOne]
          simp only [mul_one, norm_real, Real.norm_eq_abs]
          rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        next =>
          rw [hNeg]
          simp only [mul_neg, mul_one, norm_neg, norm_real, Real.norm_eq_abs]
          rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      next => exact ih
  have hBound := hAll (Finset.Icc 1 x)
  have hPsi := rationalChebyshevSum_eq_psi x
  unfold rationalChebyshevSum at hPsi
  norm_cast at hPsi
  rw [hPsi] at hBound
  unfold BombieriVinogradov.SiegelWalfisz.characterChebyshevSum
  unfold BombieriVinogradov.VaughanMeanValue.psiCharacterSum
  exact hBound

theorem abs_quadraticCharacterChebyshevStep_le_psi
    (D : NumberField.OddFundamentalDiscriminant) (t : Real) :
    abs (quadraticCharacterChebyshevStep D t) <= Chebyshev.psi t := by
  unfold quadraticCharacterChebyshevStep
  calc
    abs (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum
        (Nat.floor t) D.character).re <=
        norm (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum
          (Nat.floor t) D.character) := Complex.abs_re_le_norm _
    _ <= Chebyshev.psi (Nat.floor t) :=
      norm_quadraticCharacterChebyshevSum_le_psi D (Nat.floor t)
    _ = Chebyshev.psi t := (Chebyshev.psi_eq_psi_coe_floor t).symm

def quadraticCharacterWeightedIntegral
    (D : NumberField.OddFundamentalDiscriminant)
    (n : Nat) (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) fun t : Real =>
    quadraticCharacterChebyshevStep D t * Robin1984.robinRealWeight n t

def quadraticRationalWeightedErrorIntegral (n : Nat) (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) fun t : Real =>
    (Chebyshev.psi t - t) * Robin1984.robinRealWeight n t

def quadraticDedekindWeightedErrorIntegral
    (D : NumberField.OddFundamentalDiscriminant)
    (n : Nat) (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) fun t : Real =>
    (quadraticDedekindChebyshevStep D t - t) *
      Robin1984.robinRealWeight n t

private theorem complex_t_mul_robinRealWeight_eq
    (n : Nat) {t : Real} (ht : 1 < t) :
    ((t * Robin1984.robinRealWeight n t : Real) : Complex) =
      (t : Complex) ^ (-(n : Complex)) *
        (((n : Real) * Real.log t + 1) / (Real.log t) ^ 2 : Real) := by
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  have hPower : t * t ^ (-(n : Real) - 1) = t ^ (-(n : Real)) := by
    calc
      t * t ^ (-(n : Real) - 1) =
          t ^ (1 : Real) * t ^ (-(n : Real) - 1) := by
        rw [Real.rpow_one]
      _ = t ^ ((1 : Real) + (-(n : Real) - 1)) :=
        (Real.rpow_add htPos _ _).symm
      _ = _ := by congr 1 <;> ring
  have hReal : t * Robin1984.robinRealWeight n t =
      t ^ (-(n : Real)) *
        (((n : Real) * Real.log t + 1) / (Real.log t) ^ 2) := by
    unfold Robin1984.robinRealWeight
    rw [<- mul_assoc, hPower]
  rw [hReal, Complex.ofReal_mul, Complex.ofReal_cpow htPos.le]
  simp

private theorem integrableOn_complex_t_mul_robinRealWeight
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real =>
      ((t * Robin1984.robinRealWeight n t : Real) : Complex)) (Ioi x) := by
  have hExp : (-(n : Complex)).re < -1 := by
    simp
    exact_mod_cast hn
  have hOne := Robin1984.integrableOn_cpow_div_log_pow hx hExp 1
  have hTwo := Robin1984.integrableOn_cpow_div_log_pow hx hExp 2
  have hInt : IntegrableOn (fun t : Real =>
      (n : Complex) * ((t : Complex) ^ (-(n : Complex)) *
        (((Inv.inv ((Real.log t) ^ 1) : Real) : Complex))) +
      (t : Complex) ^ (-(n : Complex)) *
        (((Inv.inv ((Real.log t) ^ 2) : Real) : Complex))) (Ioi x) :=
    (hOne.const_mul (n : Complex)).add hTwo
  apply hInt.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [complex_t_mul_robinRealWeight_eq n (lt_trans hx ht)]
  simp only [pow_one]
  push_cast
  have hLog : Not (((Real.log t : Real) : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.log_pos (lt_trans hx ht)))
  field_simp [hLog] <;> ring

theorem integrableOn_quadraticRationalWeightedError
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real =>
      (Chebyshev.psi t - t) * Robin1984.robinRealWeight n t) (Ioi x) := by
  have hPsi := Robin1984.integrableOn_complex_psi_robinRealWeight hn hx
  have hMain := integrableOn_complex_t_mul_robinRealWeight hn hx
  have hRaw := (hPsi.sub hMain).re
  have hInt : IntegrableOn (fun t : Real =>
      (((Chebyshev.psi t * Robin1984.robinRealWeight n t : Real) : Complex) -
        ((t * Robin1984.robinRealWeight n t : Real) : Complex)).re) (Ioi x) := by
    simpa only [Pi.sub_apply, RCLike.re_to_complex] using! hRaw
  apply hInt.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  simp only [Complex.sub_re, Complex.ofReal_re]
  ring

theorem integrableOn_quadraticCharacterChebyshevStep_mul_weight
    (D : NumberField.OddFundamentalDiscriminant)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real =>
      quadraticCharacterChebyshevStep D t *
        Robin1984.robinRealWeight n t) (Ioi x) := by
  have hPsiComplex :=
    Robin1984.integrableOn_complex_psi_robinRealWeight hn hx
  have hPsi : IntegrableOn (fun t : Real =>
      Chebyshev.psi t * Robin1984.robinRealWeight n t) (Ioi x) := by
    change Integrable (fun t : Real =>
      Chebyshev.psi t * Robin1984.robinRealWeight n t)
        (volume.restrict (Ioi x))
    simpa using hPsiComplex.re
  have hStepMeasurable :
      Measurable (quadraticCharacterChebyshevStep D) := by
    unfold quadraticCharacterChebyshevStep
    exact (measurable_of_countable (fun k : Nat =>
      (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum
        k D.character).re)).comp Nat.measurable_floor
  have hWeightMeasurable :
      Measurable (Robin1984.robinRealWeight n) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  apply hPsi.mono'
  next =>
    exact (hStepMeasurable.mul hWeightMeasurable).aestronglyMeasurable
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Robin1984.robinRealWeight_nonneg (lt_trans hx ht))]
    exact mul_le_mul_of_nonneg_right
      (abs_quadraticCharacterChebyshevStep_le_psi D t)
      (Robin1984.robinRealWeight_nonneg (lt_trans hx ht))

theorem quadraticDedekindWeightedErrorIntegral_eq_add
    (D : NumberField.OddFundamentalDiscriminant)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    quadraticDedekindWeightedErrorIntegral D n x =
      quadraticRationalWeightedErrorIntegral n x +
        quadraticCharacterWeightedIntegral D n x := by
  have hRational := integrableOn_quadraticRationalWeightedError hn hx
  have hCharacter :=
    integrableOn_quadraticCharacterChebyshevStep_mul_weight D hn hx
  unfold quadraticDedekindWeightedErrorIntegral
  unfold quadraticRationalWeightedErrorIntegral
  unfold quadraticCharacterWeightedIntegral
  have hFunction : (fun t : Real =>
      (quadraticDedekindChebyshevStep D t - t) *
        Robin1984.robinRealWeight n t) =
      (fun t : Real =>
        (Chebyshev.psi t - t) * Robin1984.robinRealWeight n t +
          quadraticCharacterChebyshevStep D t *
            Robin1984.robinRealWeight n t) := by
    funext t
    rw [quadraticDedekindChebyshevStep_eq]
    ring
  rw [hFunction, integral_add hRational hCharacter]

theorem summable_quadraticL_robinZeroKernel_div
    (D : NumberField.OddFundamentalDiscriminant)
    (hERH : DirichletERH D.character)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    Summable (fun p : QuadraticLZeroIndex D.character =>
      Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
        quadraticLZeroValue p) := by
  let C : Real :=
    (n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
        Inv.inv (Real.log x) +
      (x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 *
          ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                ((1 / 2 : Real) - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat))))
  have hMajor : Summable (fun p : QuadraticLZeroIndex D.character =>
      (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat) * C) :=
    (summable_quadraticLZeroWeight
      (quadraticCharacter_ne_one D) D.character_isPrimitive).mul_right C
  apply hMajor.of_norm_bounded
  intro p
  dsimp [C]
  apply Robin1984.norm_robinZeroKernel_div_rho_le_robinXiZeroWeight hn
  next => exact p.2
  next =>
    exact quadraticLZeroValue_re_eq_half_of_dirichletERH
      (quadraticCharacter_ne_one D) D.character_isPrimitive hERH p
  next => exact hx

theorem tsum_quadraticDedekind_robinZeroKernel_eq_add
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    tsum (fun p : QuadraticDedekindZeroIndex D =>
        Robin1984.robinZeroKernel n (quadraticDedekindZeroValue p) x /
          quadraticDedekindZeroValue p) =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
          Robin1984.robinZeroKernel n (riemannXiDivisorZeroValue p) x /
            riemannXiDivisorZeroValue p) +
        tsum (fun p : QuadraticLZeroIndex D.character =>
          Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
            quadraticLZeroValue p) := by
  have hFactors := (quadraticDedekindERH_iff D).1 hFieldERH
  exact tsum_quadraticDedekindZeroKernel_eq_add D
    (fun rho => Robin1984.robinZeroKernel n rho x / rho)
    (Robin1984.summable_robinZeroKernel_div_rho hFactors.1 hn hx)
    (summable_quadraticL_robinZeroKernel_div D hFactors.2 hn hx)

theorem quadraticDedekindZeroValue_re_eq_half_of_ERH
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    (p : QuadraticDedekindZeroIndex D) :
    (quadraticDedekindZeroValue p).re = (1 / 2 : Real) := by
  have hFactors := (quadraticDedekindERH_iff D).1 hFieldERH
  have hValue := quadraticDedekindZeroIndexEquiv_value D p
  cases hImage : quadraticDedekindZeroIndexEquiv D p with
  | inl q =>
    rw [hImage] at hValue
    simp only [Sum.elim_inl] at hValue
    rw [<- hValue]
    exact Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis
      hFactors.1 q
  | inr q =>
    rw [hImage] at hValue
    simp only [Sum.elim_inr] at hValue
    rw [<- hValue]
    exact quadraticLZeroValue_re_eq_half_of_dirichletERH
      (quadraticCharacter_ne_one D) D.character_isPrimitive hFactors.2 q

def quadraticRobinZeroKernelScale (n : Nat) (x : Real) : Real :=
  (n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
      Inv.inv (Real.log x) +
    (x ^ ((1 / 2 : Real) - (n : Real)) *
        Inv.inv ((Real.log x) ^ (2 : Nat)) +
      2 *
        ((-x ^ ((1 / 2 : Real) - (n : Real)) /
              ((1 / 2 : Real) - (n : Real))) *
          Inv.inv ((Real.log x) ^ (3 : Nat))))

def quadraticRobinZeroKernelCorrection (x : Real) : Real :=
  1 + Inv.inv (Real.log x) + 4 * Inv.inv (Real.log x) ^ (2 : Nat)

theorem quadraticRobinZeroKernelScale_one_eq (x : Real) :
    quadraticRobinZeroKernelScale 1 x =
      x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) *
        quadraticRobinZeroKernelCorrection x := by
  unfold quadraticRobinZeroKernelScale
  unfold quadraticRobinZeroKernelCorrection
  norm_num
  ring

theorem tendsto_quadraticRobinZeroKernelCorrection :
    Filter.Tendsto quadraticRobinZeroKernelCorrection Filter.atTop
      (nhds 1) := by
  have hInv : Filter.Tendsto
      (fun x : Real => Inv.inv (Real.log x)) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  unfold quadraticRobinZeroKernelCorrection
  convert (tendsto_const_nhds.add hInv).add
    ((hInv.pow 2).const_mul 4) using 1 <;> norm_num

theorem eventually_quadraticRobinZeroKernelScale_one_le
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      quadraticRobinZeroKernelScale 1 x <=
        (1 + epsilon) *
          (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)))
      Filter.atTop := by
  have hCorrection : Filter.Eventually (fun x : Real =>
      quadraticRobinZeroKernelCorrection x < 1 + epsilon) Filter.atTop :=
    (tendsto_order.1 tendsto_quadraticRobinZeroKernelCorrection).2
      (1 + epsilon) (by linarith)
  filter_upwards [hCorrection,
    Filter.eventually_gt_atTop (1 : Real)] with x hCorr hx
  rw [quadraticRobinZeroKernelScale_one_eq x]
  have hBase : 0 <=
      x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) := by
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (inv_nonneg.mpr (Real.log_nonneg (le_of_lt hx)))
  calc
    x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) *
        quadraticRobinZeroKernelCorrection x <=
      x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) *
        (1 + epsilon) := mul_le_mul_of_nonneg_left hCorr.le hBase
    _ = (1 + epsilon) *
        (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) := by ring

theorem norm_tsum_quadraticDedekind_robinZeroKernel_div_le
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    norm (tsum (fun p : QuadraticDedekindZeroIndex D =>
      Robin1984.robinZeroKernel n (quadraticDedekindZeroValue p) x /
        quadraticDedekindZeroValue p)) <=
      quadraticDedekindZeroMass D * quadraticRobinZeroKernelScale n x := by
  let C := quadraticRobinZeroKernelScale n x
  have hMajor : Summable (fun p : QuadraticDedekindZeroIndex D =>
      (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat) * C) :=
    (summable_quadraticDedekindZeroWeight D).mul_right C
  have hPointwise : forall p : QuadraticDedekindZeroIndex D,
      norm (Robin1984.robinZeroKernel n (quadraticDedekindZeroValue p) x /
        quadraticDedekindZeroValue p) <=
      (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat) * C := by
    intro p
    dsimp [C, quadraticRobinZeroKernelScale]
    exact Robin1984.norm_robinZeroKernel_div_rho_le_robinXiZeroWeight hn
      p.2 (quadraticDedekindZeroValue_re_eq_half_of_ERH D hFieldERH p) hx
  have hSeries : Summable (fun p : QuadraticDedekindZeroIndex D =>
      Robin1984.robinZeroKernel n (quadraticDedekindZeroValue p) x /
        quadraticDedekindZeroValue p) :=
    hMajor.of_norm_bounded hPointwise
  have hNormSeries := hSeries.norm
  calc
    norm (tsum (fun p : QuadraticDedekindZeroIndex D =>
      Robin1984.robinZeroKernel n (quadraticDedekindZeroValue p) x /
        quadraticDedekindZeroValue p)) <=
        tsum (fun p : QuadraticDedekindZeroIndex D =>
          norm (Robin1984.robinZeroKernel n
            (quadraticDedekindZeroValue p) x /
              quadraticDedekindZeroValue p)) :=
      norm_tsum_le_tsum_norm hNormSeries
    _ <= tsum (fun p : QuadraticDedekindZeroIndex D =>
        (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat) * C) :=
      hNormSeries.tsum_le_tsum hPointwise hMajor
    _ = (tsum (fun p : QuadraticDedekindZeroIndex D =>
          (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat))) * C := by
      rw [tsum_mul_right]
    _ = quadraticDedekindZeroMass D * quadraticRobinZeroKernelScale n x := by
      rfl

theorem eventually_norm_tsum_quadraticDedekind_robinZeroKernel_one_le
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      norm (tsum (fun p : QuadraticDedekindZeroIndex D =>
        Robin1984.robinZeroKernel 1 (quadraticDedekindZeroValue p) x /
          quadraticDedekindZeroValue p)) <=
        (quadraticDedekindZeroMass D + epsilon) *
          (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)))
      Filter.atTop := by
  let Z := quadraticDedekindZeroMass D
  have hZ : 0 <= Z := quadraticDedekindZeroMass_nonneg D
  have hDelta : 0 < epsilon / (Z + 1) := by
    exact div_pos hEpsilon (by linarith)
  have hScale := eventually_quadraticRobinZeroKernelScale_one_le hDelta
  filter_upwards [hScale,
    Filter.eventually_gt_atTop (1 : Real)] with x hScale hx
  have hKernel := norm_tsum_quadraticDedekind_robinZeroKernel_div_le
    D hFieldERH (n := 1) (x := x) (by norm_num) hx
  have hBase : 0 <=
      x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) := by
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (inv_nonneg.mpr (Real.log_nonneg (le_of_lt hx)))
  have hDen : 0 < Z + 1 := by linarith
  have hFrac : Z / (Z + 1) <= 1 :=
    (div_le_one hDen).2 (by linarith)
  have hEpsFrac : epsilon * (Z / (Z + 1)) <= epsilon := by
    simpa using mul_le_mul_of_nonneg_left hFrac hEpsilon.le
  have hCoefficient : Z * (1 + epsilon / (Z + 1)) <= Z + epsilon := by
    calc
      Z * (1 + epsilon / (Z + 1)) =
          Z + epsilon * (Z / (Z + 1)) := by ring
      _ <= Z + epsilon := by linarith
  calc
    norm (tsum (fun p : QuadraticDedekindZeroIndex D =>
      Robin1984.robinZeroKernel 1 (quadraticDedekindZeroValue p) x /
        quadraticDedekindZeroValue p)) <=
        Z * quadraticRobinZeroKernelScale 1 x := hKernel
    _ <= Z * ((1 + epsilon / (Z + 1)) *
        (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x))) :=
      mul_le_mul_of_nonneg_left hScale hZ
    _ = (Z * (1 + epsilon / (Z + 1))) *
        (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) := by ring
    _ <= (Z + epsilon) *
        (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) :=
      mul_le_mul_of_nonneg_right hCoefficient hBase

theorem quadraticCriticalKernelBase_eq
    {x : Real} (hx : 0 <= x) :
    x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) =
      1 / (Real.sqrt x * Real.log x) := by
  rw [Real.rpow_neg hx, <- Real.sqrt_eq_rpow, one_div, mul_inv]

theorem eventually_norm_tsum_quadraticDedekind_robinZeroKernel_one_le_div
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      norm (tsum (fun p : QuadraticDedekindZeroIndex D =>
        Robin1984.robinZeroKernel 1 (quadraticDedekindZeroValue p) x /
          quadraticDedekindZeroValue p)) <=
        (quadraticDedekindZeroMass D + epsilon) /
          (Real.sqrt x * Real.log x)) Filter.atTop := by
  have hBound :=
    eventually_norm_tsum_quadraticDedekind_robinZeroKernel_one_le
      D hFieldERH hEpsilon
  filter_upwards [hBound,
    Filter.eventually_gt_atTop (1 : Real)] with x hBound hx
  rw [quadraticCriticalKernelBase_eq
    (le_of_lt (lt_trans Real.zero_lt_one hx))] at hBound
  simpa [div_eq_mul_inv] using hBound

theorem eventually_norm_tsum_quadraticDedekind_robinZeroKernel_one_le_div_of_zetaERH
    (D : NumberField.OddFundamentalDiscriminant)
    (hZetaERH : QuadraticDedekindZetaERH D)
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      norm (tsum (fun p : QuadraticDedekindZeroIndex D =>
        Robin1984.robinZeroKernel 1 (quadraticDedekindZeroValue p) x /
          quadraticDedekindZeroValue p)) <=
        (quadraticDedekindZeroMass D + epsilon) /
          (Real.sqrt x * Real.log x)) Filter.atTop := by
  exact eventually_norm_tsum_quadraticDedekind_robinZeroKernel_one_le_div
    D ((quadraticDedekindZetaERH_iff_carrierERH D).1 hZetaERH) hEpsilon

theorem quadraticDedekindWeightedErrorIntegral_eq_zero_sum_of_component_formulas
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 2 <= x)
    (rationalCorrection : Complex)
    (hRationalFormula :
      (quadraticRationalWeightedErrorIntegral n x : Complex) =
        -tsum (fun p : RiemannXiDivisorZeroIndex =>
          Robin1984.robinZeroKernel n (riemannXiDivisorZeroValue p) x /
            riemannXiDivisorZeroValue p) - rationalCorrection)
    (characterCorrection : Complex)
    (hCharacterFormula :
      (quadraticCharacterWeightedIntegral D n x : Complex) =
        -tsum (fun p : QuadraticLZeroIndex D.character =>
          Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
            quadraticLZeroValue p) - characterCorrection) :
    (quadraticDedekindWeightedErrorIntegral D n x : Complex) =
      -tsum (fun p : QuadraticDedekindZeroIndex D =>
        Robin1984.robinZeroKernel n (quadraticDedekindZeroValue p) x /
          quadraticDedekindZeroValue p) -
        rationalCorrection - characterCorrection := by
  have hPrimeSplit :=
    quadraticDedekindWeightedErrorIntegral_eq_add D hn
      (by linarith)
  have hZeroSplit :=
    tsum_quadraticDedekind_robinZeroKernel_eq_add
      D hFieldERH (n := n) (x := x) (by omega) (by linarith)
  rw [hPrimeSplit, Complex.ofReal_add, hRationalFormula, hCharacterFormula,
    hZeroSplit]
  ring

end

end RobinBV.NumberField
