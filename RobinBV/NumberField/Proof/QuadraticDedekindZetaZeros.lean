import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedProductFormula
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber
import Robin1984.NicolasLandau.XiDivisorCriticalLine
import RobinBV.NumberField.Definitions.QuadraticDedekindZeta

/-!
# Zeros of the canonical continued quadratic Dedekind zeta

This file proves exact critical-strip zero equivalence and additive
multiplicity and divisor formulas for the entire quadratic zero carrier.
-/

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex

noncomputable section

theorem quadraticDedekindZeroCarrier_eq_zero_iff
    (D : NumberField.OddFundamentalDiscriminant) (s : Complex) :
    quadraticDedekindZeroCarrier D s = 0 <->
      Or (riemannXi s = 0)
        (symmetricCompletedLFunction D.character s = 0) := by
  exact mul_eq_zero

theorem analyticOrderNatAt_quadraticDedekindZeroCarrier
    (D : NumberField.OddFundamentalDiscriminant) (s : Complex) :
    analyticOrderNatAt (quadraticDedekindZeroCarrier D) s =
      analyticOrderNatAt riemannXi s +
        analyticOrderNatAt (symmetricCompletedLFunction D.character) s := by
  apply analyticOrderNatAt_mul
  next => exact differentiable_riemannXi.analyticAt s
  next =>
    exact (differentiable_symmetricCompletedLFunction
      (quadraticCharacter_ne_one D)).analyticAt s
  next =>
    exact Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero
      differentiable_riemannXi riemannXi_nontrivial s
  next =>
    exact Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero
      (differentiable_symmetricCompletedLFunction
        (quadraticCharacter_ne_one D))
      (Exists.intro 2
        (symmetricCompletedLFunction_two_ne_zero
          (quadraticCharacter_ne_one D))) s

theorem divisor_quadraticDedekindZeroCarrier
    (D : NumberField.OddFundamentalDiscriminant) :
    MeromorphicOn.divisor (quadraticDedekindZeroCarrier D)
        (Set.univ : Set Complex) =
      MeromorphicOn.divisor riemannXi (Set.univ : Set Complex) +
        MeromorphicOn.divisor
          (symmetricCompletedLFunction D.character)
          (Set.univ : Set Complex) := by
  ext s
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
    (differentiable_quadraticDedekindZeroCarrier D) s]
  change
    (analyticOrderNatAt (quadraticDedekindZeroCarrier D) s : Int) =
      MeromorphicOn.divisor riemannXi (Set.univ : Set Complex) s +
        MeromorphicOn.divisor
          (symmetricCompletedLFunction D.character)
          (Set.univ : Set Complex) s
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
    differentiable_riemannXi s]
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
    (differentiable_symmetricCompletedLFunction
      (quadraticCharacter_ne_one D)) s]
  rw [analyticOrderNatAt_quadraticDedekindZeroCarrier D s]
  simp

theorem riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
    {s : Complex} (hsPos : 0 < s.re) (hsLt : s.re < 1) :
    riemannXi s = 0 <-> riemannZeta s = 0 := by
  have hsZero : Not (s = 0) := by
    intro hZero
    subst s
    norm_num at hsPos
  have hsOne : Not (s = 1) := by
    intro hOne
    subst s
    norm_num at hsLt
  constructor
  next =>
    exact Robin1984.riemannZeta_eq_zero_of_riemannXi_eq_zero
      hsZero hsOne
  next =>
    intro hZeta
    have hsHalfPos : 0 < (s / 2).re := by
      norm_num [Complex.div_re]
      linarith
    have hGamma : Not (Complex.Gamma (s / 2) = 0) :=
      Complex.Gamma_ne_zero_of_re_pos hsHalfPos
    have hCompleted : completedRiemannZeta s = 0 := by
      rw [completedRiemannZeta_eq_cpow_mul_Gamma_mul_riemannZeta
        hsZero hGamma, hZeta, mul_zero]
    rw [riemannXi_eq_mul_completedRiemannZeta hsZero hsOne,
      hCompleted, mul_zero, zero_div]

theorem symmetricCompletedLFunction_eq_zero_iff_LFunction_eq_zero_of_re_pos
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hsPos : 0 < s.re) :
    symmetricCompletedLFunction D.character s = 0 <->
      D.character.LFunction s = 0 := by
  have hN : Not ((D.modulus : Complex) = 0) := by
    exact_mod_cast NeZero.ne D.modulus
  have hPower : Not ((D.modulus : Complex) ^ (s / 2) = 0) :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hN)
  have hGamma : Not (D.character.gammaFactor s = 0) :=
    DirichletCharacter.gammaFactor_ne_zero_of_re_pos D.character hsPos
  rw [symmetricCompletedLFunction,
    DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
      D.character hsPos]
  constructor
  next =>
    intro hZero
    have hInner := (mul_eq_zero.mp hZero).resolve_left hPower
    exact (mul_eq_zero.mp hInner).resolve_right hGamma
  next =>
    intro hZero
    rw [hZero, zero_mul, mul_zero]

theorem quadraticDedekindZeroCarrier_eq_zero_iff_continuation_eq_zero
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hsPos : 0 < s.re) (hsLt : s.re < 1) :
    quadraticDedekindZeroCarrier D s = 0 <->
      quadraticDedekindZetaContinuation D s = 0 := by
  rw [quadraticDedekindZeroCarrier_eq_zero_iff D s]
  rw [riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
    hsPos hsLt]
  rw [symmetricCompletedLFunction_eq_zero_iff_LFunction_eq_zero_of_re_pos D
    hsPos]
  unfold quadraticDedekindZetaContinuation
  exact mul_eq_zero.symm


end

end RobinBV.NumberField
