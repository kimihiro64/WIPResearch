import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedConjugation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLogDerivativeReflection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RobinBV.NumberField.Proof.PairedDirichletCriticalCriterion
import RobinBV.NumberField.Proof.PairedDirichletZeroIndex
import RobinBV.NumberField.Proof.QuadraticLZeroMassEvaluation

/-!
# Paired Dirichlet zero mass and sharp secondary terms

This module evaluates the multiplicity-weighted zero mass of the dual-character
carrier. It proves exact additivity, inverse-character equality under ERH, and
conductor, logarithmic-derivative, and parity-dependent archimedean formulas
without a self-duality hypothesis.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open scoped BigOperators

noncomputable section

def pairedDirichletZeroMass
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) : Real :=
  tsum fun p : PairedDirichletZeroIndex chi =>
    (Inv.inv (norm (pairedDirichletZeroValue p))) ^ (2 : Nat)

theorem pairedDirichletZeroMass_eq_sum
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    pairedDirichletZeroMass chi =
      quadraticLZeroMass chi + quadraticLZeroMass (Inv.inv chi) := by
  let e := pairedDirichletZeroIndexEquiv hchi
  let f : Sum (QuadraticLZeroIndex chi)
      (QuadraticLZeroIndex (Inv.inv chi)) -> Real :=
    Sum.elim
      (fun p => (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat))
      (fun p => (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat))
  have hInvNe : Not (Inv.inv chi = 1) :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hInvPrimitive :
      DirichletCharacter.IsPrimitive (Inv.inv chi) :=
    BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive
  have hLeft : Summable (fun p => f (Sum.inl p)) := by
    simpa [f] using
      summable_quadraticLZeroWeight hchi hPrimitive
  have hRight : Summable (fun p => f (Sum.inr p)) := by
    simpa [f] using
      summable_quadraticLZeroWeight hInvNe hInvPrimitive
  rw [pairedDirichletZeroMass]
  calc
    tsum (fun p : PairedDirichletZeroIndex chi =>
        (Inv.inv (norm (pairedDirichletZeroValue p))) ^ (2 : Nat)) =
        tsum (fun p : PairedDirichletZeroIndex chi => f (e p)) := by
      apply tsum_congr
      intro p
      cases hSide : e p with
      | inl q =>
        have hValue := pairedDirichletZeroIndexEquiv_value hchi p
        change pairedDirichletZeroIndexEquiv hchi p = Sum.inl q at hSide
        rw [hSide] at hValue
        change
          (Inv.inv (norm (pairedDirichletZeroValue p))) ^ (2 : Nat) =
            (Inv.inv (norm (quadraticLZeroValue q))) ^ (2 : Nat)
        rw [hValue]
        rfl
      | inr q =>
        have hValue := pairedDirichletZeroIndexEquiv_value hchi p
        change pairedDirichletZeroIndexEquiv hchi p = Sum.inr q at hSide
        rw [hSide] at hValue
        change
          (Inv.inv (norm (pairedDirichletZeroValue p))) ^ (2 : Nat) =
            (Inv.inv (norm (quadraticLZeroValue q))) ^ (2 : Nat)
        rw [hValue]
        rfl
    _ = tsum f := e.tsum_eq f
    _ = tsum (fun p : QuadraticLZeroIndex chi => f (Sum.inl p)) +
          tsum (fun p : QuadraticLZeroIndex (Inv.inv chi) =>
            f (Sum.inr p)) :=
      hLeft.tsum_sum hRight
    _ = quadraticLZeroMass chi +
          quadraticLZeroMass (Inv.inv chi) := by
      rfl

theorem primitiveLZeroMass_inv_eq
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) :
    quadraticLZeroMass (Inv.inv chi) = quadraticLZeroMass chi := by
  have hInvNe : Not (Inv.inv chi = 1) :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hInvPrimitive :
      DirichletCharacter.IsPrimitive (Inv.inv chi) :=
    BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive
  have hInvERH : DirichletERH (Inv.inv chi) :=
    (dirichletERH_inv_iff_of_isPrimitive hPrimitive).2 hERH
  have hMass := quadraticLZeroMass_eq_neg_two_mul_re_logDeriv_zero
    hchi hPrimitive hERH
  have hInvMass := quadraticLZeroMass_eq_neg_two_mul_re_logDeriv_zero
    hInvNe hInvPrimitive hInvERH
  have hConj :=
    logDeriv_symmetricCompletedLFunction_inv_eq_conj_conj hchi
      (0 : Complex)
  have hConjRe :
      (logDeriv (symmetricCompletedLFunction (Inv.inv chi)) 0).re =
        (logDeriv (symmetricCompletedLFunction chi) 0).re := by
    simpa using congrArg Complex.re hConj
  linarith

theorem primitiveLZeroMass_eq_log_modulus_add_logDeriv_one
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) :
    quadraticLZeroMass chi =
      Real.log N + 2 * (logDeriv chi.LFunction 1).re +
        2 * (logDeriv chi.gammaFactor 1).re := by
  have hMass := quadraticLZeroMass_eq_neg_two_mul_re_logDeriv_zero
    hchi hPrimitive hERH
  have hConj :=
    logDeriv_symmetricCompletedLFunction_inv_eq_conj_conj hchi
      (0 : Complex)
  have hConjRe :
      (logDeriv (symmetricCompletedLFunction (Inv.inv chi)) 0).re =
        (logDeriv (symmetricCompletedLFunction chi) 0).re := by
    simpa using congrArg Complex.re hConj
  have hReflection :=
    logDeriv_symmetricCompletedLFunction_one_sub hchi hPrimitive
      (0 : Complex)
  have hReflectionRe :
      (logDeriv (symmetricCompletedLFunction chi) 1).re =
        -(logDeriv
          (symmetricCompletedLFunction (Inv.inv chi)) 0).re := by
    simpa only [sub_zero, Complex.neg_re] using
      congrArg Complex.re hReflection
  have hThree :=
    logDeriv_symmetricCompletedLFunction_one_eq_three_factors hchi
  have hThreeRe :
      (logDeriv (symmetricCompletedLFunction chi) 1).re =
        Real.log N / 2 + ((logDeriv chi.LFunction 1).re +
          (logDeriv chi.gammaFactor 1).re) := by
    simpa only [Complex.add_re, Complex.div_ofNat_re,
      Complex.ofReal_re] using congrArg Complex.re hThree
  linarith

theorem primitiveLZeroMass_eq_even_explicit
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hEven : DirichletCharacter.Even chi) (hERH : DirichletERH chi) :
    quadraticLZeroMass chi =
      Real.log N + 2 * (logDeriv chi.LFunction 1).re -
        Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  have hMass := primitiveLZeroMass_eq_log_modulus_add_logDeriv_one
    hchi hPrimitive hERH
  have hGamma := logDeriv_gammaFactor_of_even hEven
    (s := (1 : Complex)) (by norm_num)
  rw [Complex.digamma_one_half] at hGamma
  have hLogTwo : Complex.log (2 : Complex) =
      (Real.log 2 : Complex) := by
    exact (Complex.ofReal_log (x := (2 : Real)) (by norm_num)).symm
  rw [hLogTwo] at hGamma
  have hGammaRe :
      (logDeriv chi.gammaFactor 1).re =
        -Real.log Real.pi / 2 +
          (1 / 2 : Real) *
            (-2 * Real.log 2 - Real.eulerMascheroniConstant) := by
    simpa only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.mul_re, Complex.add_im,
      Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, zero_div,
      sub_zero] using congrArg Complex.re hGamma
  rw [Real.log_mul (by norm_num : Not ((4 : Real) = 0))
    (by positivity : Not (Real.pi = 0))]
  have hLogFour : Real.log (4 : Real) = 2 * Real.log 2 := by
    calc
      Real.log (4 : Real) = Real.log 2 + Real.log 2 := by
        rw [show (4 : Real) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]
      _ = 2 * Real.log 2 := by ring
  rw [hLogFour]
  linarith

theorem primitiveLZeroMass_eq_odd_explicit
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hOdd : DirichletCharacter.Odd chi) (hERH : DirichletERH chi) :
    quadraticLZeroMass chi =
      Real.log N + 2 * (logDeriv chi.LFunction 1).re -
        Real.eulerMascheroniConstant - Real.log Real.pi := by
  have hMass := primitiveLZeroMass_eq_log_modulus_add_logDeriv_one
    hchi hPrimitive hERH
  have hGamma := logDeriv_gammaFactor_of_odd hOdd
    (s := (1 : Complex)) (by norm_num)
  have hGamma' :
      logDeriv chi.gammaFactor 1 =
        -(Real.log Real.pi : Complex) / 2 +
          (1 / 2 : Complex) * Complex.digamma 1 := by
    simpa using hGamma
  rw [Complex.digamma_one] at hGamma'
  have hGammaRe :
      (logDeriv chi.gammaFactor 1).re =
        -Real.log Real.pi / 2 +
          (1 / 2 : Real) * (-Real.eulerMascheroniConstant) := by
    simpa only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.mul_re, Complex.add_im,
      Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, zero_div,
      sub_zero] using congrArg Complex.re hGamma'
  linarith

theorem pairedDirichletZeroMass_eq_two_mul
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) :
    pairedDirichletZeroMass chi = 2 * quadraticLZeroMass chi := by
  have hSum := pairedDirichletZeroMass_eq_sum hchi hPrimitive
  have hInv := primitiveLZeroMass_inv_eq hchi hPrimitive hERH
  linarith

theorem pairedDirichletZeroMass_eq_even_explicit
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hEven : DirichletCharacter.Even chi) (hERH : DirichletERH chi) :
    pairedDirichletZeroMass chi =
      2 * Real.log N + 4 * (logDeriv chi.LFunction 1).re -
        2 * Real.eulerMascheroniConstant -
          2 * Real.log (4 * Real.pi) := by
  have hPair := pairedDirichletZeroMass_eq_two_mul
    hchi hPrimitive hERH
  have hSingle := primitiveLZeroMass_eq_even_explicit
    hchi hPrimitive hEven hERH
  linarith

theorem pairedDirichletZeroMass_eq_odd_explicit
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hOdd : DirichletCharacter.Odd chi) (hERH : DirichletERH chi) :
    pairedDirichletZeroMass chi =
      2 * Real.log N + 4 * (logDeriv chi.LFunction 1).re -
        2 * Real.eulerMascheroniConstant - 2 * Real.log Real.pi := by
  have hPair := pairedDirichletZeroMass_eq_two_mul
    hchi hPrimitive hERH
  have hSingle := primitiveLZeroMass_eq_odd_explicit
    hchi hPrimitive hOdd hERH
  linarith

end

end RobinBV.NumberField
