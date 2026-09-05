import RobinBV.NumberField.Proof.PairedDirichletZeroMass
import RobinBV.NumberField.Proof.QuadraticCharacterWeightedFormula

/-!
# Primitive complex-character Robin weighted formula

The complete weighted prime-power formula for any nonprincipal primitive
complex character. The even and odd archimedean terms remain exact.
The arithmetic input is a convergent Mellin cutoff sum, before the endpoint
tail reweighting needed for a critical-scale equivalence.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set

noncomputable section

def primitiveCharacterPrimePowerSum
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (n : Nat) (x : Real) : Complex :=
  tsum (fun m : Nat => twistedMangoldtSequence chi m *
    Robin1984.robinCutoffMellinTest n x (m : Real))

theorem integrable_primitiveCharacter_gamma_test
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    Integrable (fun t : Real =>
      mellin (Robin1984.robinCutoffMellinTest n x)
          ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
        logDeriv chi.gammaFactor
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
  rcases chi.even_or_odd with hEven | hOdd
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

theorem integrable_primitiveCharacter_zero_test
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    Integrable (fun t : Real =>
      mellin (Robin1984.robinCutoffMellinTest n x)
          ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
        tsum (fun p : QuadraticLZeroIndex chi =>
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
  let _ : Countable (QuadraticLZeroIndex chi) := by
    have hSupport : Function.support
        (fun p : QuadraticLZeroIndex chi =>
          (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat)) =
        Set.univ := by
      ext p
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact pow_ne_zero _ (inv_ne_zero
        (norm_ne_zero_iff.mpr p.property))
    have hCount :=
      (summable_quadraticLZeroWeight
        hchi
        hPrimitive).countable_support
    rw [hSupport] at hCount
    exact Set.countable_univ_iff.mp hCount
  have hSeries := Robin1984.integrable_complex_series_of_integral_norm
    (fun p => Robin1984.integrable_paired_xi_atom hH
      (quadraticLZeroValue_re_eq_half_of_dirichletERH
        hchi hPrimitive
        hERH p))
    (summable_integral_norm_quadraticL_paired_atoms
      hchi hPrimitive
      hERH hH hC hBound)
  apply hSeries.congr
  filter_upwards with t
  rw [tsum_mul_left]

theorem primitiveCharacterPrimePowerSum_eq_explicit_of_gamma_pairing
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi)
    {B : Complex}
    (hB : IsCompletedLFunctionHadamardConstant chi B)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x)
    (gammaRemainder : Complex)
    (hGammaPairing :
      (((1 / (2 * Real.pi) : Real) : Complex)) *
          integral volume (fun t : Real =>
            mellin (Robin1984.robinCutoffMellinTest n x)
                ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
              logDeriv chi.gammaFactor
                ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
        gammaRemainder) :
    primitiveCharacterPrimePowerSum chi n x =
      -tsum (fun p : QuadraticLZeroIndex chi =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
          quadraticLZeroValue p) +
      ((Real.log N : Complex) / 2 - B) *
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
  let A : Complex := (Real.log N : Complex) / 2 - B
  let G : Real -> Complex := fun t =>
    H t * logDeriv chi.gammaFactor
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let Z : Real -> Complex := fun t =>
    H t * tsum (fun p : QuadraticLZeroIndex chi =>
      1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I -
        quadraticLZeroValue p) +
      1 / quadraticLZeroValue p)
  have hArithmetic :
      primitiveCharacterPrimePowerSum chi n x =
        K * integral volume (fun t : Real =>
          (-logDeriv chi.LFunction
            ((3 / 2 : Complex) + (t : Complex) * Complex.I)) *
            H t) := by
    simpa [K, H, primitiveCharacterPrimePowerSum] using!
      primitiveCharacterPrimePowerSum_eq_safeLineIntegral
        chi hnOne hx hc hcLt
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using!
      Robin1984.verticalIntegrable_mellin_robinCutoffMellinTest
        hnOne hx hcPos hcLt
  have hG : Integrable G := by
    simpa [G, H] using!
      integrable_primitiveCharacter_gamma_test chi hn hx
  have hZ : Integrable Z := by
    simpa [Z, H] using!
      integrable_primitiveCharacter_zero_test
        hchi hPrimitive hERH hn hx
  have hConst : Integrable (fun t : Real => A * H t) :=
    hH.const_mul A
  have hSource : forall t : Real,
      (-logDeriv chi.LFunction
        ((3 / 2 : Complex) + (t : Complex) * Complex.I)) *
          H t =
        A * H t + G t - Z t := by
    intro t
    rw [logDeriv_LFunction_eq_hadamardConstant_add_zero_sum
      hchi hPrimitive
      hB (by norm_num)]
    dsimp only [A, G, Z]
    ring
  have hIntegral :
      integral volume (fun t : Real =>
        (-logDeriv chi.LFunction
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
        tsum (fun p : QuadraticLZeroIndex chi =>
          Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
            quadraticLZeroValue p) := by
    simpa [K, Z, H] using!
      primitiveCharacter_robinCutoffMellin_complete_zero_pairing
        hchi hPrimitive hERH hn hx
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

def primitiveCharacterEvenWeightedRemainder
    (N : Nat)
    (B : Complex) (n : Nat) (x : Real) : Complex :=
  ((Real.log N : Complex) / 2 - B -
      (Real.log Real.pi : Complex) / 2 -
      (Real.eulerMascheroniConstant : Complex) / 2) *
      Robin1984.robinCutoffMellinTest n x 1 +
    tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n
          (-(2 * ((k : Complex) + 1))) x /
        (2 * ((k : Complex) + 1))) -
    quadraticCharacterEvenOriginCorrection n x

def primitiveCharacterOddWeightedRemainder
    (N : Nat)
    (B : Complex) (n : Nat) (x : Real) : Complex :=
  ((Real.log N : Complex) / 2 - B -
      (Real.log Real.pi : Complex) / 2 -
      (Real.eulerMascheroniConstant : Complex) / 2 +
      quadraticOddGammaConstant) *
      Robin1984.robinCutoffMellinTest n x 1 +
    tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n
          (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1))

theorem primitiveCharacterPrimePowerSum_eq_even_explicit
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hEven : DirichletCharacter.Even chi)
    (hERH : DirichletERH chi)
    {B : Complex}
    (hB : IsCompletedLFunctionHadamardConstant chi B)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    primitiveCharacterPrimePowerSum chi n x =
      -tsum (fun p : QuadraticLZeroIndex chi =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
          quadraticLZeroValue p) +
      primitiveCharacterEvenWeightedRemainder N B n x := by
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
              logDeriv chi.gammaFactor
                ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
        gammaRemainder := by
    simpa [gammaRemainder] using!
      quadraticCharacter_even_gamma_pairing hEven hn hx
  have hFormula :=
    primitiveCharacterPrimePowerSum_eq_explicit_of_gamma_pairing
      hchi hPrimitive hERH hB hn hx gammaRemainder hGamma
  rw [hFormula]
  unfold primitiveCharacterEvenWeightedRemainder
  dsimp only [gammaRemainder]
  ring

theorem primitiveCharacterPrimePowerSum_eq_odd_explicit
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hOdd : DirichletCharacter.Odd chi)
    (hERH : DirichletERH chi)
    {B : Complex}
    (hB : IsCompletedLFunctionHadamardConstant chi B)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    primitiveCharacterPrimePowerSum chi n x =
      -tsum (fun p : QuadraticLZeroIndex chi =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
          quadraticLZeroValue p) +
      primitiveCharacterOddWeightedRemainder N B n x := by
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
              logDeriv chi.gammaFactor
                ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
        gammaRemainder := by
    simpa [gammaRemainder] using!
      quadraticCharacter_odd_gamma_pairing hOdd hn hx
  have hFormula :=
    primitiveCharacterPrimePowerSum_eq_explicit_of_gamma_pairing
      hchi hPrimitive hERH hB hn hx gammaRemainder hGamma
  rw [hFormula]
  unfold primitiveCharacterOddWeightedRemainder
  dsimp only [gammaRemainder]
  ring


/-- Conjugating the Mellin cutoff leaves it fixed. -/
theorem primitiveCharacterCutoff_conj (n : Nat) (x t : Real) :
    (starRingEnd Complex) (Robin1984.robinCutoffMellinTest n x t) =
      Robin1984.robinCutoffMellinTest n x t := by
  unfold Robin1984.robinCutoffMellinTest
  split_ifs <;> simp [Complex.cpow_neg, Complex.cpow_natCast]

theorem primitiveCharacterPrimePowerSum_inv
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (n : Nat) (x : Real) :
    primitiveCharacterPrimePowerSum (Inv.inv chi) n x =
      (starRingEnd Complex) (primitiveCharacterPrimePowerSum chi n x) := by
  symm
  unfold primitiveCharacterPrimePowerSum
  rw [RCLike.conj_tsum]
  apply tsum_congr
  intro m
  rw [map_mul, primitiveCharacterCutoff_conj]
  unfold twistedMangoldtSequence
  rw [map_mul, BombieriVinogradov.DirichletCharacter.conj_apply_eq_inv_apply]
  simp

def pairedDirichletPrimePowerSum
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (n : Nat) (x : Real) : Complex :=
  primitiveCharacterPrimePowerSum chi n x +
    primitiveCharacterPrimePowerSum (Inv.inv chi) n x

theorem pairedDirichletPrimePowerSum_eq_two_re
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (n : Nat) (x : Real) :
    pairedDirichletPrimePowerSum chi n x =
      ((2 * (primitiveCharacterPrimePowerSum chi n x).re : Real) : Complex) := by
  rw [pairedDirichletPrimePowerSum, primitiveCharacterPrimePowerSum_inv]
  exact Complex.add_conj _

theorem tsum_pairedDirichletZeroKernel_eq_sum
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (f : Complex -> Complex)
    (hLeft : Summable (fun p : QuadraticLZeroIndex chi =>
      f (quadraticLZeroValue p)))
    (hRight : Summable (fun p : QuadraticLZeroIndex (Inv.inv chi) =>
      f (quadraticLZeroValue p))) :
    tsum (fun p : PairedDirichletZeroIndex chi =>
      f (pairedDirichletZeroValue p)) =
        tsum (fun p : QuadraticLZeroIndex chi => f (quadraticLZeroValue p)) +
        tsum (fun p : QuadraticLZeroIndex (Inv.inv chi) =>
          f (quadraticLZeroValue p)) := by
  let e := pairedDirichletZeroIndexEquiv hchi
  let F : Sum (QuadraticLZeroIndex chi)
      (QuadraticLZeroIndex (Inv.inv chi)) -> Complex :=
    Sum.elim (fun p => f (quadraticLZeroValue p))
      (fun p => f (quadraticLZeroValue p))
  have hValue : forall p : PairedDirichletZeroIndex chi,
      f (pairedDirichletZeroValue p) = F (e p) := by
    intro p
    rw [pairedDirichletZeroIndexEquiv_value hchi p]
    change f (Sum.elim (fun q => quadraticLZeroValue q)
      (fun q => quadraticLZeroValue q) (e p)) = F (e p)
    cases e p <;> rfl
  calc
    _ = tsum (fun p : PairedDirichletZeroIndex chi => F (e p)) :=
      tsum_congr hValue
    _ = tsum F := e.tsum_eq F
    _ = _ := hLeft.tsum_sum hRight

theorem summable_primitiveCharacter_robinZeroKernel_div
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    Summable (fun p : QuadraticLZeroIndex chi =>
      Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
        quadraticLZeroValue p) := by
  let C : Real :=
    (n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
        Inv.inv (Real.log x) +
      (x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 * ((-x ^ ((1 / 2 : Real) - (n : Real)) /
              ((1 / 2 : Real) - (n : Real))) *
          Inv.inv ((Real.log x) ^ (3 : Nat))))
  have hMajor : Summable (fun p : QuadraticLZeroIndex chi =>
      (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat) * C) :=
    (summable_quadraticLZeroWeight hchi hPrimitive).mul_right C
  apply hMajor.of_norm_bounded
  intro p
  exact Robin1984.norm_robinZeroKernel_div_rho_le_robinXiZeroWeight
    hn p.property
    (quadraticLZeroValue_re_eq_half_of_dirichletERH
      hchi hPrimitive hERH p) hx

theorem primitiveCharacter_endpoint_isHadamardConstant
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    IsCompletedLFunctionHadamardConstant chi
      (logDeriv (symmetricCompletedLFunction chi) 0) := by
  choose B hB using
    (existsUnique_symmetricCompletedLFunction_hadamardConstant
      hchi hPrimitive).exists
  rw [logDeriv_symmetricCompletedLFunction_zero_eq_hadamardConstant
    hchi hPrimitive hB]
  exact hB

theorem pairedDirichlet_endpoint_constants_eq_neg_mass
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) :
    logDeriv (symmetricCompletedLFunction chi) 0 +
      logDeriv (symmetricCompletedLFunction (Inv.inv chi)) 0 =
        -(quadraticLZeroMass chi : Complex) := by
  rw [logDeriv_symmetricCompletedLFunction_inv_eq_conj_conj hchi,
    map_zero, Complex.add_conj]
  rw [quadraticLZeroMass_eq_neg_two_mul_re_logDeriv_zero
    hchi hPrimitive hERH]
  push_cast
  ring

theorem pairedDirichletPrimePowerSum_eq_even_explicit
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hEven : DirichletCharacter.Even chi) (hERH : DirichletERH chi)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    pairedDirichletPrimePowerSum chi n x =
      -tsum (fun p : PairedDirichletZeroIndex chi =>
        Robin1984.robinZeroKernel n (pairedDirichletZeroValue p) x /
          pairedDirichletZeroValue p) +
      ((Real.log N + quadraticLZeroMass chi -
        Real.eulerMascheroniConstant - Real.log Real.pi : Real) : Complex) *
          Robin1984.robinCutoffMellinTest n x 1 +
      2 * tsum (fun k : Nat =>
        Robin1984.robinZeroKernel n (-(2 * ((k : Complex) + 1))) x /
          (2 * ((k : Complex) + 1))) -
      2 * quadraticCharacterEvenOriginCorrection n x := by
  have hi := BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hp := BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive
  have he := (dirichletERH_inv_iff_of_isPrimitive hPrimitive).2 hERH
  have hnOne : 1 <= n := by omega
  have hSplit := tsum_pairedDirichletZeroKernel_eq_sum hchi
    (fun rho => Robin1984.robinZeroKernel n rho x / rho)
    (summable_primitiveCharacter_robinZeroKernel_div hchi hPrimitive hERH hnOne hx)
    (summable_primitiveCharacter_robinZeroKernel_div hi hp he hnOne hx)
  have hConstants :=
    pairedDirichlet_endpoint_constants_eq_neg_mass hchi hPrimitive hERH
  rw [pairedDirichletPrimePowerSum,
    primitiveCharacterPrimePowerSum_eq_even_explicit hchi hPrimitive hEven hERH
      (primitiveCharacter_endpoint_isHadamardConstant hchi hPrimitive) hn hx,
    primitiveCharacterPrimePowerSum_eq_even_explicit hi hp
      (BombieriVinogradov.DirichletCharacter.Even.inv hEven) he
      (primitiveCharacter_endpoint_isHadamardConstant hi hp) hn hx,
    hSplit]
  unfold primitiveCharacterEvenWeightedRemainder
  push_cast
  linear_combination
    -(Robin1984.robinCutoffMellinTest n x 1) * hConstants

theorem pairedDirichletPrimePowerSum_eq_odd_explicit
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hOdd : DirichletCharacter.Odd chi) (hERH : DirichletERH chi)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    pairedDirichletPrimePowerSum chi n x =
      -tsum (fun p : PairedDirichletZeroIndex chi =>
        Robin1984.robinZeroKernel n (pairedDirichletZeroValue p) x /
          pairedDirichletZeroValue p) +
      ((Real.log N + quadraticLZeroMass chi -
        Real.eulerMascheroniConstant - Real.log Real.pi : Real) : Complex) *
          Robin1984.robinCutoffMellinTest n x 1 +
      2 * quadraticOddGammaConstant * Robin1984.robinCutoffMellinTest n x 1 +
      2 * tsum (fun k : Nat =>
        Robin1984.robinZeroKernel n (-(2 * (k : Complex) + 1)) x /
          (2 * (k : Complex) + 1)) := by
  have hi := BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hp := BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive
  have he := (dirichletERH_inv_iff_of_isPrimitive hPrimitive).2 hERH
  have hnOne : 1 <= n := by omega
  have hSplit := tsum_pairedDirichletZeroKernel_eq_sum hchi
    (fun rho => Robin1984.robinZeroKernel n rho x / rho)
    (summable_primitiveCharacter_robinZeroKernel_div hchi hPrimitive hERH hnOne hx)
    (summable_primitiveCharacter_robinZeroKernel_div hi hp he hnOne hx)
  have hConstants :=
    pairedDirichlet_endpoint_constants_eq_neg_mass hchi hPrimitive hERH
  rw [pairedDirichletPrimePowerSum,
    primitiveCharacterPrimePowerSum_eq_odd_explicit hchi hPrimitive hOdd hERH
      (primitiveCharacter_endpoint_isHadamardConstant hchi hPrimitive) hn hx,
    primitiveCharacterPrimePowerSum_eq_odd_explicit hi hp
      (BombieriVinogradov.DirichletCharacter.Odd.inv hOdd) he
      (primitiveCharacter_endpoint_isHadamardConstant hi hp) hn hx,
    hSplit]
  unfold primitiveCharacterOddWeightedRemainder
  push_cast
  linear_combination
    -(Robin1984.robinCutoffMellinTest n x 1) * hConstants

theorem norm_primitiveCharacterEvenWeightedRemainder_two_le
    (N : Nat) (B : Complex)
    {x : Real} (hx : 2 <= x) :
    norm (primitiveCharacterEvenWeightedRemainder N B 2 x) <=
      x ^ (-(2 : Real)) +
        (norm ((Real.log N : Complex) / 2 - B -
            (Real.log Real.pi : Complex) / 2 -
            (Real.eulerMascheroniConstant : Complex) / 2) +
          2 * Real.log (2 * Real.pi) + 1 / 2) *
          (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) := by
  let C : Complex := (Real.log N : Complex) / 2 - B -
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

theorem norm_primitiveCharacterOddWeightedRemainder_two_le
    (N : Nat) (B : Complex)
    {x : Real} (hx : 2 <= x) :
    norm (primitiveCharacterOddWeightedRemainder N B 2 x) <=
      (norm ((Real.log N : Complex) / 2 - B -
          (Real.log Real.pi : Complex) / 2 -
          (Real.eulerMascheroniConstant : Complex) / 2 +
          quadraticOddGammaConstant) + 1) *
        (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) := by
  let C : Complex := (Real.log N : Complex) / 2 - B -
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

end

end RobinBV.NumberField
