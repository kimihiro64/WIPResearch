import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardFactorization
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber
import RobinBV.NumberField.Definitions.PairedDirichletL

/-!
# Zero divisor of the paired Dirichlet carrier

This module proves the exact zero alternative, analytic-order sum, and
divisor sum for the dual-character completed L-function product.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex

noncomputable section

theorem pairedDirichletZeroCarrier_eq_zero_iff
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (s : Complex) :
    pairedDirichletZeroCarrier chi s = 0 <->
      Or (symmetricCompletedLFunction chi s = 0)
        (symmetricCompletedLFunction (Inv.inv chi) s = 0) := by
  exact mul_eq_zero

theorem differentiable_pairedDirichletZeroCarrier
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) :
    Differentiable Complex (pairedDirichletZeroCarrier chi) := by
  have hInv : Ne (Inv.inv chi) 1 :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  exact (differentiable_symmetricCompletedLFunction hchi).mul
    (differentiable_symmetricCompletedLFunction hInv)

theorem analyticOrderNatAt_pairedDirichletZeroCarrier
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (s : Complex) :
    analyticOrderNatAt (pairedDirichletZeroCarrier chi) s =
      analyticOrderNatAt (symmetricCompletedLFunction chi) s +
        analyticOrderNatAt
          (symmetricCompletedLFunction (Inv.inv chi)) s := by
  have hInv : Ne (Inv.inv chi) 1 :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  apply analyticOrderNatAt_mul
  next =>
    exact (differentiable_symmetricCompletedLFunction hchi).analyticAt s
  next =>
    exact (differentiable_symmetricCompletedLFunction hInv).analyticAt s
  next =>
    exact Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero
      (differentiable_symmetricCompletedLFunction hchi)
      (Exists.intro 2
        (symmetricCompletedLFunction_two_ne_zero hchi)) s
  next =>
    exact Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero
      (differentiable_symmetricCompletedLFunction hInv)
      (Exists.intro 2
        (symmetricCompletedLFunction_two_ne_zero hInv)) s

theorem divisor_pairedDirichletZeroCarrier
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) :
    MeromorphicOn.divisor (pairedDirichletZeroCarrier chi)
        (Set.univ : Set Complex) =
      MeromorphicOn.divisor (symmetricCompletedLFunction chi)
          (Set.univ : Set Complex) +
        MeromorphicOn.divisor
          (symmetricCompletedLFunction (Inv.inv chi))
          (Set.univ : Set Complex) := by
  have hInv : Ne (Inv.inv chi) 1 :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  ext s
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
    (differentiable_pairedDirichletZeroCarrier hchi) s]
  change
    (analyticOrderNatAt (pairedDirichletZeroCarrier chi) s : Int) =
      MeromorphicOn.divisor (symmetricCompletedLFunction chi)
          (Set.univ : Set Complex) s +
        MeromorphicOn.divisor
          (symmetricCompletedLFunction (Inv.inv chi))
          (Set.univ : Set Complex) s
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
    (differentiable_symmetricCompletedLFunction hchi) s]
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
    (differentiable_symmetricCompletedLFunction hInv) s]
  rw [analyticOrderNatAt_pairedDirichletZeroCarrier hchi s]
  simp

end

end RobinBV.NumberField
