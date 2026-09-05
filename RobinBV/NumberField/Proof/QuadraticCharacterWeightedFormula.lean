import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeZeroSum
import Robin1984.NicolasLandau.WeightedTrivialCorrection
import RobinBV.NumberField.Proof.QuadraticCharacterGammaCorrectionBounds

/-!
# Quadratic character weighted explicit formula

The safe-line twisted Mangoldt identity is combined with the completed
quadratic L-function Hadamard expansion. Under Dirichlet ERH, the complete zero
series is paired with Robin's kernel and the even or odd gamma factor is
retained as an explicit canonical lower-order correction.
-/

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set

noncomputable section

theorem integrable_quadraticCharacter_gamma_test
    (D : NumberField.OddFundamentalDiscriminant)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    Integrable (fun t : Real =>
      mellin (Robin1984.robinCutoffMellinTest n x)
          ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
        logDeriv D.character.gammaFactor
          ((3 / 2 : Complex) + (t : Complex) * Complex.I)) := by
  choose C hC hBound using
    Robin1984.exists_robinCutoffMellin_safeLine_majorant hn hx
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcLt : (3 / 2 : Real) < n := by linarith
  let H : Real -> Complex := fun t =>
    mellin (Robin1984.robinCutoffMellinTest n x)
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using!
      Robin1984.verticalIntegrable_mellin_robinCutoffMellinTest
        hnOne hx (by norm_num : (0 : Real) < 3 / 2) hcLt
  rcases D.character.even_or_odd with hEven | hOdd
  next =>
    let C0 : Complex :=
      -(Real.log Real.pi : Complex) / 2 -
        (Real.eulerMascheroniConstant : Complex) / 2
    let G : Real -> Complex := fun t =>
      H t * ((1 / 2 : Complex) * Complex.digamma
        (((3 / 2 : Complex) + (t : Complex) * Complex.I) / 2 + 1) +
          (Real.eulerMascheroniConstant : Complex) / 2)
    let O : Real -> Complex := fun t =>
      H t / ((3 / 2 : Complex) + (t : Complex) * Complex.I)
    have hG : Integrable G := by
      simpa [G, H] using!
        Robin1984.integrable_shifted_gamma_test hH hC hBound
    have hO : Integrable O := by
      simpa [O] using!
        Robin1984.integrable_vertical_resolvent hH
          (c := (3 / 2 : Real)) (rho := 0) (by norm_num)
    have hConst : Integrable (fun t : Real => C0 * H t) :=
      hH.const_mul C0
    apply ((hConst.add hG).sub hO).congr
    filter_upwards with t
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [logDeriv_gammaFactor_of_even_eq_shifted hEven
      (by norm_num)]
    dsimp only [C0, G, O]
    ring
  next =>
    let C0 : Complex :=
      -(Real.log Real.pi : Complex) / 2 -
        (Real.eulerMascheroniConstant : Complex) / 2
    let G : Real -> Complex := fun t =>
      H t * ((1 / 2 : Complex) * Complex.digamma
        (((3 / 2 : Complex) + (t : Complex) * Complex.I + 1) / 2) +
        (Real.eulerMascheroniConstant : Complex) / 2)
    have hG : Integrable G := by
      have hNorm :=
        summable_integral_norm_quadraticOddGammaAtoms
          hH hC hBound
      have hSeries := Robin1984.integrable_complex_series_of_integral_norm
        (integrable_quadraticOddGammaAtom hH) hNorm
      apply hSeries.congr
      filter_upwards with t
      dsimp only [G]
      rw [tsum_mul_left,
        half_digamma_odd_eq_gammaAtoms
          (by simp; norm_num)]
      ring
    have hConst : Integrable (fun t : Real => C0 * H t) :=
      hH.const_mul C0
    apply (hConst.add hG).congr
    filter_upwards with t
    simp only [Pi.add_apply]
    rw [logDeriv_gammaFactor_of_odd hOdd (by norm_num)]
    dsimp only [C0, G]
    ring

theorem integrable_quadraticCharacter_zero_test
    (D : NumberField.OddFundamentalDiscriminant)
    (hERH : DirichletERH D.character)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    Integrable (fun t : Real =>
      mellin (Robin1984.robinCutoffMellinTest n x)
          ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
        tsum (fun p : QuadraticLZeroIndex D.character =>
          1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I -
            quadraticLZeroValue p) +
          1 / quadraticLZeroValue p)) := by
  choose C hC hBound using
    Robin1984.exists_robinCutoffMellin_safeLine_majorant hn hx
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcLt : (3 / 2 : Real) < n := by linarith
  let H : Real -> Complex := fun t =>
    mellin (Robin1984.robinCutoffMellinTest n x)
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using!
      Robin1984.verticalIntegrable_mellin_robinCutoffMellinTest
        hnOne hx (by norm_num : (0 : Real) < 3 / 2) hcLt
  let _ : Countable (QuadraticLZeroIndex D.character) := by
    have hSupport : Function.support
        (fun p : QuadraticLZeroIndex D.character =>
          (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat)) =
        Set.univ := by
      ext p
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact pow_ne_zero _ (inv_ne_zero
        (norm_ne_zero_iff.mpr p.property))
    have hCount :=
      (summable_quadraticLZeroWeight
        (quadraticCharacter_ne_one D)
        D.character_isPrimitive).countable_support
    rw [hSupport] at hCount
    exact Set.countable_univ_iff.mp hCount
  have hSeries := Robin1984.integrable_complex_series_of_integral_norm
    (fun p => Robin1984.integrable_paired_xi_atom hH
      (quadraticLZeroValue_re_eq_half_of_dirichletERH
        (quadraticCharacter_ne_one D) D.character_isPrimitive
        hERH p))
    (summable_integral_norm_quadraticL_paired_atoms
      (quadraticCharacter_ne_one D) D.character_isPrimitive
      hERH hH hC hBound)
  apply hSeries.congr
  filter_upwards with t
  rw [tsum_mul_left]

theorem quadraticCharacterWeightedIntegral_eq_explicit_of_gamma_pairing
    (D : NumberField.OddFundamentalDiscriminant)
    (hERH : DirichletERH D.character)
    {B : Complex}
    (hB : IsCompletedLFunctionHadamardConstant D.character B)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x)
    (gammaRemainder : Complex)
    (hGammaPairing :
      (((1 / (2 * Real.pi) : Real) : Complex)) *
          integral volume (fun t : Real =>
            mellin (Robin1984.robinCutoffMellinTest n x)
                ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
              logDeriv D.character.gammaFactor
                ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
        gammaRemainder) :
    (quadraticCharacterWeightedIntegral D n x : Complex) =
      -tsum (fun p : QuadraticLZeroIndex D.character =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
          quadraticLZeroValue p) +
      ((Real.log D.modulus : Complex) / 2 - B) *
        Robin1984.robinCutoffMellinTest n x 1 +
      gammaRemainder := by
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hc : (1 : Real) < 3 / 2 := by norm_num
  have hcPos : (0 : Real) < 3 / 2 := by norm_num
  have hcLt : (3 / 2 : Real) < n := by linarith
  let K : Complex := (((1 / (2 * Real.pi) : Real) : Complex))
  let H : Real -> Complex := fun t =>
    mellin (Robin1984.robinCutoffMellinTest n x)
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let A : Complex := (Real.log D.modulus : Complex) / 2 - B
  let G : Real -> Complex := fun t =>
    H t * logDeriv D.character.gammaFactor
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let Z : Real -> Complex := fun t =>
    H t * tsum (fun p : QuadraticLZeroIndex D.character =>
      1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I -
        quadraticLZeroValue p) +
      1 / quadraticLZeroValue p)
  have hArithmetic :
      (quadraticCharacterWeightedIntegral D n x : Complex) =
        K * integral volume (fun t : Real =>
          (-logDeriv D.character.LFunction
            ((3 / 2 : Complex) + (t : Complex) * Complex.I)) *
            H t) := by
    rw [<- quadraticCharacterPrimePowerSum_eq_weightedIntegral
      D hn hx]
    simpa [K, H] using!
      quadraticCharacterPrimePowerSum_eq_safeLineIntegral
        D hnOne hx hc hcLt
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using!
      Robin1984.verticalIntegrable_mellin_robinCutoffMellinTest
        hnOne hx hcPos hcLt
  have hG : Integrable G := by
    simpa [G, H] using!
      integrable_quadraticCharacter_gamma_test D hn hx
  have hZ : Integrable Z := by
    simpa [Z, H] using!
      integrable_quadraticCharacter_zero_test
        D hERH hn hx
  have hConst : Integrable (fun t : Real => A * H t) :=
    hH.const_mul A
  have hSource : forall t : Real,
      (-logDeriv D.character.LFunction
        ((3 / 2 : Complex) + (t : Complex) * Complex.I)) *
          H t =
        A * H t + G t - Z t := by
    intro t
    rw [logDeriv_LFunction_eq_hadamardConstant_add_zero_sum
      (quadraticCharacter_ne_one D) D.character_isPrimitive
      hB (by norm_num)]
    dsimp only [A, G, Z]
    ring
  have hIntegral :
      integral volume (fun t : Real =>
        (-logDeriv D.character.LFunction
          ((3 / 2 : Complex) + (t : Complex) * Complex.I)) *
            H t) =
      A * integral volume H + integral volume G -
        integral volume Z := by
    calc
      _ = integral volume (fun t : Real =>
          A * H t + G t - Z t) :=
        integral_congr_ae (Filter.Eventually.of_forall hSource)
      _ = _ := by
        have hSub := integral_sub (hConst.add hG) hZ
        have hAdd := integral_add hConst hG
        simp only [Pi.add_apply] at hSub hAdd
        rw [hSub, hAdd, integral_const_mul]
  have hAtOne :
      K * integral volume H =
        Robin1984.robinCutoffMellinTest n x 1 := by
    have h := Robin1984.mellinInv_mellin_robinCutoffMellinTest
      hnOne hx hcPos hcLt Real.zero_lt_one
    simpa [mellinInv, RCLike.real_smul_eq_coe_mul,
      smul_eq_mul, H, K] using! h
  have hZeros :
      K * integral volume Z =
        tsum (fun p : QuadraticLZeroIndex D.character =>
          Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
            quadraticLZeroValue p) := by
    simpa [K, Z, H] using!
      quadraticCharacter_robinCutoffMellin_complete_zero_pairing
        D hERH hn hx
  have hGamma : K * integral volume G = gammaRemainder := by
    simpa [K, G, H] using! hGammaPairing
  rw [hArithmetic, hIntegral]
  rw [show K * (A * integral volume H + integral volume G -
      integral volume Z) =
    A * (K * integral volume H) + K * integral volume G -
      K * integral volume Z by ring]
  rw [hAtOne, hGamma, hZeros]
  dsimp only [A]
  ring

def quadraticCharacterEvenWeightedRemainder
    (D : NumberField.OddFundamentalDiscriminant)
    (B : Complex) (n : Nat) (x : Real) : Complex :=
  ((Real.log D.modulus : Complex) / 2 - B -
      (Real.log Real.pi : Complex) / 2 -
      (Real.eulerMascheroniConstant : Complex) / 2) *
      Robin1984.robinCutoffMellinTest n x 1 +
    tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n
          (-(2 * ((k : Complex) + 1))) x /
        (2 * ((k : Complex) + 1))) -
    quadraticCharacterEvenOriginCorrection n x

def quadraticCharacterOddWeightedRemainder
    (D : NumberField.OddFundamentalDiscriminant)
    (B : Complex) (n : Nat) (x : Real) : Complex :=
  ((Real.log D.modulus : Complex) / 2 - B -
      (Real.log Real.pi : Complex) / 2 -
      (Real.eulerMascheroniConstant : Complex) / 2 +
      quadraticOddGammaConstant) *
      Robin1984.robinCutoffMellinTest n x 1 +
    tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n
          (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1))

theorem quadraticCharacterWeightedIntegral_eq_even_explicit
    (D : NumberField.OddFundamentalDiscriminant)
    (hEven : DirichletCharacter.Even D.character)
    (hERH : DirichletERH D.character)
    {B : Complex}
    (hB : IsCompletedLFunctionHadamardConstant D.character B)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    (quadraticCharacterWeightedIntegral D n x : Complex) =
      -tsum (fun p : QuadraticLZeroIndex D.character =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
          quadraticLZeroValue p) +
      quadraticCharacterEvenWeightedRemainder D B n x := by
  let gammaRemainder : Complex :=
    (-(Real.log Real.pi : Complex) / 2 -
        (Real.eulerMascheroniConstant : Complex) / 2) *
      Robin1984.robinCutoffMellinTest n x 1 +
    tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n
          (-(2 * ((k : Complex) + 1))) x /
        (2 * ((k : Complex) + 1))) -
    quadraticCharacterEvenOriginCorrection n x
  have hGamma :
      (((1 / (2 * Real.pi) : Real) : Complex)) *
          integral volume (fun t : Real =>
            mellin (Robin1984.robinCutoffMellinTest n x)
                ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
              logDeriv D.character.gammaFactor
                ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
        gammaRemainder := by
    simpa [gammaRemainder] using!
      quadraticCharacter_even_gamma_pairing hEven hn hx
  have hFormula :=
    quadraticCharacterWeightedIntegral_eq_explicit_of_gamma_pairing
      D hERH hB hn hx gammaRemainder hGamma
  rw [hFormula]
  unfold quadraticCharacterEvenWeightedRemainder
  dsimp only [gammaRemainder]
  ring

theorem quadraticCharacterWeightedIntegral_eq_odd_explicit
    (D : NumberField.OddFundamentalDiscriminant)
    (hOdd : DirichletCharacter.Odd D.character)
    (hERH : DirichletERH D.character)
    {B : Complex}
    (hB : IsCompletedLFunctionHadamardConstant D.character B)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    (quadraticCharacterWeightedIntegral D n x : Complex) =
      -tsum (fun p : QuadraticLZeroIndex D.character =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
          quadraticLZeroValue p) +
      quadraticCharacterOddWeightedRemainder D B n x := by
  let gammaRemainder : Complex :=
    (-(Real.log Real.pi : Complex) / 2 -
        (Real.eulerMascheroniConstant : Complex) / 2 +
        quadraticOddGammaConstant) *
      Robin1984.robinCutoffMellinTest n x 1 +
    tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n
          (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1))
  have hGamma :
      (((1 / (2 * Real.pi) : Real) : Complex)) *
          integral volume (fun t : Real =>
            mellin (Robin1984.robinCutoffMellinTest n x)
                ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
              logDeriv D.character.gammaFactor
                ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
        gammaRemainder := by
    simpa [gammaRemainder] using!
      quadraticCharacter_odd_gamma_pairing hOdd hn hx
  have hFormula :=
    quadraticCharacterWeightedIntegral_eq_explicit_of_gamma_pairing
      D hERH hB hn hx gammaRemainder hGamma
  rw [hFormula]
  unfold quadraticCharacterOddWeightedRemainder
  dsimp only [gammaRemainder]
  ring

def quadraticCharacterWeightedRemainder
    (D : NumberField.OddFundamentalDiscriminant)
    (B : Complex) (n : Nat) (x : Real) : Complex :=
  if 0 < D.value then
    quadraticCharacterEvenWeightedRemainder D B n x
  else
    quadraticCharacterOddWeightedRemainder D B n x

theorem quadraticCharacterWeightedIntegral_eq_explicit
    (D : NumberField.OddFundamentalDiscriminant)
    (hERH : DirichletERH D.character)
    {B : Complex}
    (hB : IsCompletedLFunctionHadamardConstant D.character B)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    (quadraticCharacterWeightedIntegral D n x : Complex) =
      -tsum (fun p : QuadraticLZeroIndex D.character =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
          quadraticLZeroValue p) +
      quadraticCharacterWeightedRemainder D B n x := by
  by_cases hPos : 0 < D.value
  next =>
    rw [quadraticCharacterWeightedRemainder, if_pos hPos]
    exact
      quadraticCharacterWeightedIntegral_eq_even_explicit
        D (D.character_even_of_pos hPos) hERH hB hn hx
  next =>
    have hNe : Not (D.value = 0) := by
      intro hZero
      have hLarge := D.abs_gt_one
      rw [hZero] at hLarge
      norm_num at hLarge
    have hNeg : D.value < 0 := by
      rcases lt_or_gt_of_ne hNe with hNeg | hPositive
      next => exact hNeg
      next => exact False.elim (hPos hPositive)
    rw [quadraticCharacterWeightedRemainder, if_neg hPos]
    exact
      quadraticCharacterWeightedIntegral_eq_odd_explicit
        D (D.character_odd_of_neg hNeg) hERH hB hn hx

noncomputable def quadraticCharacterHadamardConstant
    (D : NumberField.OddFundamentalDiscriminant) : Complex :=
  (existsUnique_symmetricCompletedLFunction_hadamardConstant
    (quadraticCharacter_ne_one D) D.character_isPrimitive).exists.choose

theorem quadraticCharacterHadamardConstant_spec
    (D : NumberField.OddFundamentalDiscriminant) :
    IsCompletedLFunctionHadamardConstant D.character
      (quadraticCharacterHadamardConstant D) :=
  (existsUnique_symmetricCompletedLFunction_hadamardConstant
    (quadraticCharacter_ne_one D)
    D.character_isPrimitive).exists.choose_spec

def quadraticCharacterCorrection
    (D : NumberField.OddFundamentalDiscriminant)
    (n : Nat) (x : Real) : Complex :=
  -quadraticCharacterWeightedRemainder D
    (quadraticCharacterHadamardConstant D) n x

theorem quadraticCharacterWeightedIntegral_eq_zero_sum_sub_correction
    (D : NumberField.OddFundamentalDiscriminant)
    (hERH : DirichletERH D.character)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    (quadraticCharacterWeightedIntegral D n x : Complex) =
      -tsum (fun p : QuadraticLZeroIndex D.character =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
          quadraticLZeroValue p) -
      quadraticCharacterCorrection D n x := by
  rw [quadraticCharacterCorrection, sub_neg_eq_add]
  exact quadraticCharacterWeightedIntegral_eq_explicit
    D hERH (quadraticCharacterHadamardConstant_spec D)
    hn hx


theorem norm_robinCutoffMellinTest_two_one_eq
    {x : Real} (hx : 1 < x) :
    norm (Robin1984.robinCutoffMellinTest 2 x 1) =
      x ^ (-(2 : Real)) * Inv.inv (Real.log x) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hPowNonneg : 0 <= x ^ (-(2 : Real)) :=
    Real.rpow_nonneg hxPos.le _
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  simp only [Robin1984.robinCutoffMellinTest, if_pos hx.le,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hLogPos)]
  rw [show (-((2 : Nat) : Complex)) =
    ((-(2 : Real) : Real) : Complex) by norm_num,
    <- Complex.ofReal_cpow hxPos.le, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hPowNonneg]

theorem norm_tsum_quadraticNegativeEvenKernels_two_le
    {x : Real} (hx : 2 <= x) :
    norm (tsum (fun k : Nat =>
      Robin1984.robinZeroKernel 2
          (-(2 * ((k : Complex) + 1))) x /
        (2 * ((k : Complex) + 1)))) <=
      2 * Real.log (2 * Real.pi) *
        x ^ (-(2 : Real)) * Inv.inv (Real.log x) := by
  have hEq := Robin1984.robin_explicit_correction_eq
    (n := 2) (by norm_num : 1 <= (2 : Nat)) hx
  have hCorr := Robin1984.robinTrivialZeroCorrection_bounds
    (n := 2) (by norm_num : 1 <= (2 : Nat)) hx
  have hLogPos : 0 < Real.log (2 * Real.pi) := by
    apply Real.log_pos
    nlinarith [Real.pi_gt_three]
  let S : Complex := tsum (fun k : Nat =>
    Robin1984.robinZeroKernel 2
        (-(2 * ((k : Complex) + 1))) x /
      (2 * ((k : Complex) + 1)))
  have hSolve : S =
      (Real.log (2 * Real.pi) : Complex) *
          Robin1984.robinCutoffMellinTest 2 x 1 -
        (Robin1984.robinTrivialZeroCorrection 2 x : Complex) := by
    dsimp only [S]
    linear_combination hEq
  change norm S <= _
  rw [hSolve]
  calc
    norm ((Real.log (2 * Real.pi) : Complex) *
          Robin1984.robinCutoffMellinTest 2 x 1 -
        (Robin1984.robinTrivialZeroCorrection 2 x : Complex)) <=
      norm ((Real.log (2 * Real.pi) : Complex) *
          Robin1984.robinCutoffMellinTest 2 x 1) +
        norm (Robin1984.robinTrivialZeroCorrection 2 x : Complex) :=
      norm_sub_le _ _
    _ = Real.log (2 * Real.pi) *
          (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) +
        Robin1984.robinTrivialZeroCorrection 2 x := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hLogPos,
        norm_robinCutoffMellinTest_two_one_eq (by linarith),
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCorr.1]
    _ <= Real.log (2 * Real.pi) *
          (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) +
        Real.log (2 * Real.pi) * x ^ (-(2 : Real)) *
          Inv.inv (Real.log x) := add_le_add le_rfl hCorr.2
    _ = _ := by ring

theorem norm_tsum_quadraticNegativeOddKernels_two_le_explicit
    {x : Real} (hx : 2 <= x) :
    norm (tsum (fun k : Nat =>
      Robin1984.robinZeroKernel 2 (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1))) <=
      x ^ (-(2 : Real)) * Inv.inv (Real.log x) := by
  calc
    norm (tsum (fun k : Nat =>
        Robin1984.robinZeroKernel 2 (-(2 * (k : Complex) + 1)) x /
          (2 * (k : Complex) + 1))) <=
      integral (volume.restrict (Ioi x)) (Robin1984.robinRealWeight 2) :=
      norm_tsum_quadraticNegativeOddKernels_le (by norm_num) hx
    _ = _ := Robin1984.integral_robinRealWeight
      (by norm_num) (by linarith)

theorem norm_quadraticCharacterEvenWeightedRemainder_two_le
    (D : NumberField.OddFundamentalDiscriminant) (B : Complex)
    {x : Real} (hx : 2 <= x) :
    norm (quadraticCharacterEvenWeightedRemainder D B 2 x) <=
      x ^ (-(2 : Real)) +
        (norm ((Real.log D.modulus : Complex) / 2 - B -
            (Real.log Real.pi : Complex) / 2 -
            (Real.eulerMascheroniConstant : Complex) / 2) +
          2 * Real.log (2 * Real.pi) + 1 / 2) *
          (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) := by
  let C : Complex := (Real.log D.modulus : Complex) / 2 - B -
    (Real.log Real.pi : Complex) / 2 -
    (Real.eulerMascheroniConstant : Complex) / 2
  let T : Complex := Robin1984.robinCutoffMellinTest 2 x 1
  let S : Complex := tsum (fun k : Nat =>
    Robin1984.robinZeroKernel 2
        (-(2 * ((k : Complex) + 1))) x /
      (2 * ((k : Complex) + 1)))
  let O : Complex := quadraticCharacterEvenOriginCorrection 2 x
  change norm (C * T + S - O) <= _
  have hT := norm_robinCutoffMellinTest_two_one_eq
    (by linarith : 1 < x)
  have hS := norm_tsum_quadraticNegativeEvenKernels_two_le hx
  have hO := norm_quadraticCharacterEvenOriginCorrection_le
    (by linarith : 1 < x)
  have hFirst : norm (C * T + S) <= norm (C * T) + norm S :=
    norm_add_le _ _
  calc
    norm (C * T + S - O) <= norm (C * T + S) + norm O :=
      norm_sub_le _ _
    _ <= (norm (C * T) + norm S) + norm O :=
      add_le_add hFirst le_rfl
    _ = (norm C * (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) + norm S) +
        norm O := by rw [norm_mul, hT]
    _ <= (norm C * (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) +
          2 * Real.log (2 * Real.pi) * x ^ (-(2 : Real)) *
            Inv.inv (Real.log x)) +
        (x ^ (-(2 : Real)) +
          (x ^ (-(2 : Real)) / 2) * Inv.inv (Real.log x)) := by
      exact add_le_add (add_le_add le_rfl hS) hO
    _ = _ := by
      dsimp only [C]
      ring

theorem norm_quadraticCharacterOddWeightedRemainder_two_le
    (D : NumberField.OddFundamentalDiscriminant) (B : Complex)
    {x : Real} (hx : 2 <= x) :
    norm (quadraticCharacterOddWeightedRemainder D B 2 x) <=
      (norm ((Real.log D.modulus : Complex) / 2 - B -
          (Real.log Real.pi : Complex) / 2 -
          (Real.eulerMascheroniConstant : Complex) / 2 +
          quadraticOddGammaConstant) + 1) *
        (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) := by
  let C : Complex := (Real.log D.modulus : Complex) / 2 - B -
    (Real.log Real.pi : Complex) / 2 -
    (Real.eulerMascheroniConstant : Complex) / 2 +
    quadraticOddGammaConstant
  let T : Complex := Robin1984.robinCutoffMellinTest 2 x 1
  let S : Complex := tsum (fun k : Nat =>
    Robin1984.robinZeroKernel 2 (-(2 * (k : Complex) + 1)) x /
      (2 * (k : Complex) + 1))
  change norm (C * T + S) <= _
  have hT := norm_robinCutoffMellinTest_two_one_eq
    (by linarith : 1 < x)
  have hS := norm_tsum_quadraticNegativeOddKernels_two_le_explicit hx
  calc
    norm (C * T + S) <= norm (C * T) + norm S := norm_add_le _ _
    _ = norm C * (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) +
        norm S := by rw [norm_mul, hT]
    _ <= norm C * (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) +
        x ^ (-(2 : Real)) * Inv.inv (Real.log x) :=
      add_le_add le_rfl hS
    _ = _ := by
      dsimp only [C]
      ring

theorem inv_log_le_inv_log_two
    {x : Real} (hx : 2 <= x) :
    Inv.inv (Real.log x) <= Inv.inv (Real.log 2) := by
  have hLog : Real.log 2 <= Real.log x :=
    Real.log_le_log (by norm_num) hx
  simpa only [one_div] using one_div_le_one_div_of_le
    (Real.log_pos (by norm_num)) hLog

theorem exists_quadraticCharacterCorrection_bound
    (D : NumberField.OddFundamentalDiscriminant) :
    Exists fun A : Real => And (0 <= A) (forall x : Real, 2 <= x ->
      norm (quadraticCharacterCorrection D 2 x) <=
        A * x ^ (-(2 : Real))) := by
  let B : Complex := quadraticCharacterHadamardConstant D
  let Ce : Complex := (Real.log D.modulus : Complex) / 2 - B -
    (Real.log Real.pi : Complex) / 2 -
    (Real.eulerMascheroniConstant : Complex) / 2
  let Co : Complex := (Real.log D.modulus : Complex) / 2 - B -
    (Real.log Real.pi : Complex) / 2 -
    (Real.eulerMascheroniConstant : Complex) / 2 +
    quadraticOddGammaConstant
  let Q : Real := norm Ce + norm Co +
    2 * abs (Real.log (2 * Real.pi)) + 2
  let A : Real := 1 + Q * Inv.inv (Real.log 2)
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLogTwoPi : 0 < Real.log (2 * Real.pi) := by
    apply Real.log_pos
    nlinarith [Real.pi_gt_three]
  have hQ : 0 <= Q := by
    dsimp only [Q]
    positivity
  have hA : 0 <= A := by
    dsimp only [A]
    positivity
  refine Exists.intro A (And.intro hA ?_)
  intro x hx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : Real) < 2) hx
  have hPow : 0 <= x ^ (-(2 : Real)) := Real.rpow_nonneg hxPos.le _
  have hInv : Inv.inv (Real.log x) <= Inv.inv (Real.log 2) :=
    inv_log_le_inv_log_two hx
  have hInvNonneg : 0 <= Inv.inv (Real.log x) := by
    exact inv_nonneg.mpr (Real.log_pos (by linarith)).le
  have hBase :
      x ^ (-(2 : Real)) * Inv.inv (Real.log x) <=
        x ^ (-(2 : Real)) * Inv.inv (Real.log 2) :=
    mul_le_mul_of_nonneg_left hInv hPow
  by_cases hPos : 0 < D.value
  next =>
    have hRem := norm_quadraticCharacterEvenWeightedRemainder_two_le
      D B hx
    have hCoeff :
        norm Ce + 2 * Real.log (2 * Real.pi) + 1 / 2 <= Q := by
      dsimp only [Q]
      rw [abs_of_pos hLogTwoPi]
      nlinarith [norm_nonneg Co]
    have hCoeffNonneg :
        0 <= norm Ce + 2 * Real.log (2 * Real.pi) + 1 / 2 := by
      positivity
    calc
      norm (quadraticCharacterCorrection D 2 x) =
          norm (quadraticCharacterEvenWeightedRemainder D B 2 x) := by
        simp only [quadraticCharacterCorrection,
          quadraticCharacterWeightedRemainder, if_pos hPos, norm_neg]
        rfl
      _ <= x ^ (-(2 : Real)) +
          (norm Ce + 2 * Real.log (2 * Real.pi) + 1 / 2) *
            (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) := by
        simpa only [Ce] using hRem
      _ <= x ^ (-(2 : Real)) +
          Q * (x ^ (-(2 : Real)) * Inv.inv (Real.log 2)) := by
        apply add_le_add le_rfl
        exact mul_le_mul hCoeff hBase
          (mul_nonneg hPow hInvNonneg) hQ
      _ = A * x ^ (-(2 : Real)) := by
        dsimp only [A]
        ring
  next =>
    have hRem := norm_quadraticCharacterOddWeightedRemainder_two_le
      D B hx
    have hCoeff : norm Co + 1 <= Q := by
      dsimp only [Q]
      nlinarith [norm_nonneg Ce, abs_nonneg (Real.log (2 * Real.pi))]
    have hCoeffNonneg : 0 <= norm Co + 1 := by positivity
    have hProduct :
        (norm Co + 1) *
            (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) <=
          Q * (x ^ (-(2 : Real)) * Inv.inv (Real.log 2)) :=
      mul_le_mul hCoeff hBase
        (mul_nonneg hPow hInvNonneg) hQ
    calc
      norm (quadraticCharacterCorrection D 2 x) =
          norm (quadraticCharacterOddWeightedRemainder D B 2 x) := by
        simp only [quadraticCharacterCorrection,
          quadraticCharacterWeightedRemainder, if_neg hPos, norm_neg]
        rfl
      _ <= (norm Co + 1) *
          (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) := by
        simpa only [Co] using hRem
      _ <= Q * (x ^ (-(2 : Real)) * Inv.inv (Real.log 2)) := hProduct
      _ <= A * x ^ (-(2 : Real)) := by
        dsimp only [A]
        nlinarith [mul_nonneg hQ (inv_nonneg.mpr hLogTwo.le)]


end

end RobinBV.NumberField
