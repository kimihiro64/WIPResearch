import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardFactorization
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi
import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaFactorization

/-!
# Canonical continued quadratic Dedekind zeta

This file defines the canonical quadratic Dedekind-zeta continuation and its
entire multiplicity-preserving zero carrier.
-/

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex

noncomputable section

theorem quadraticCharacter_ne_one
    (D : NumberField.OddFundamentalDiscriminant) :
    Not (D.character = 1) := by
  intro hOne
  have hPrimitive := D.character_isPrimitive
  rw [DirichletCharacter.IsPrimitive, hOne,
    DirichletCharacter.conductor_one] at hPrimitive
  have hLarge := D.abs_gt_one
  unfold NumberField.OddFundamentalDiscriminant.modulus at hPrimitive
  omega

/-- The canonical meromorphic continuation of the quadratic Dedekind zeta
function supplied by its Riemann-zeta and primitive quadratic-L factors. -/
noncomputable def quadraticDedekindZetaContinuation
    (D : NumberField.OddFundamentalDiscriminant) (s : Complex) : Complex :=
  riemannZeta s * D.character.LFunction s

theorem quadraticDedekindZetaContinuation_eq_dedekindZeta
    (D : NumberField.OddFundamentalDiscriminant) {s : Complex}
    (hs : 1 < s.re) :
    quadraticDedekindZetaContinuation D s =
      NumberField.dedekindZeta D.QuadraticField s := by
  exact (D.dedekindZeta_quadraticField_eq_riemannZeta_mul_LFunction hs).symm

/-- An entire zero-carrier for the canonical quadratic Dedekind zeta
continuation. Its divisor retains the multiplicities of both factors. -/
noncomputable def quadraticDedekindZeroCarrier
    (D : NumberField.OddFundamentalDiscriminant) (s : Complex) : Complex :=
  riemannXi s * symmetricCompletedLFunction D.character s

theorem differentiable_quadraticDedekindZeroCarrier
    (D : NumberField.OddFundamentalDiscriminant) :
    Differentiable Complex (quadraticDedekindZeroCarrier D) := by
  exact differentiable_riemannXi.mul
    (differentiable_symmetricCompletedLFunction (quadraticCharacter_ne_one D))


end

end RobinBV.NumberField
