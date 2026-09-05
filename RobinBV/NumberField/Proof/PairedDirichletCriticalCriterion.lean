import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedFunctionalEquation
import Mathlib.Tactic.Linarith
import RobinBV.NumberField.Proof.PairedDirichletZeroDivisor

/-!
# Critical-line criterion for a dual Dirichlet pair

This module identifies the paired-carrier critical-line assertion with the
two constituent Dirichlet ERH assertions and then uses the functional
equation to collapse the primitive pair to either one of its factors.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz

noncomputable section

theorem symmetricCompletedLFunction_eq_zero_iff_completedLFunction_eq_zero
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (s : Complex) :
    symmetricCompletedLFunction chi s = 0 <->
      chi.completedLFunction s = 0 := by
  have hN : Ne (N : Complex) 0 := by
    exact_mod_cast NeZero.ne N
  have hPower : Ne ((N : Complex) ^ (s / 2)) 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hN)
  rw [symmetricCompletedLFunction]
  constructor
  next =>
    intro hZero
    exact (mul_eq_zero.mp hZero).resolve_left hPower
  next =>
    intro hZero
    rw [hZero, mul_zero]

theorem pairedDirichletERH_iff
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    PairedDirichletERH chi <->
      And (DirichletERH chi) (DirichletERH (Inv.inv chi)) := by
  constructor
  next =>
    intro hPair
    apply And.intro
    next =>
      intro rho hZero
      have hSymmetric : symmetricCompletedLFunction chi rho = 0 :=
        (symmetricCompletedLFunction_eq_zero_iff_completedLFunction_eq_zero
          chi rho).2 hZero.1
      have hCarrier : pairedDirichletZeroCarrier chi rho = 0 :=
        (pairedDirichletZeroCarrier_eq_zero_iff chi rho).2
          (Or.inl hSymmetric)
      exact hPair rho hCarrier hZero.2.1 hZero.2.2
    next =>
      intro rho hZero
      have hSymmetric :
          symmetricCompletedLFunction (Inv.inv chi) rho = 0 :=
        (symmetricCompletedLFunction_eq_zero_iff_completedLFunction_eq_zero
          (Inv.inv chi) rho).2 hZero.1
      have hCarrier : pairedDirichletZeroCarrier chi rho = 0 :=
        (pairedDirichletZeroCarrier_eq_zero_iff chi rho).2
          (Or.inr hSymmetric)
      exact hPair rho hCarrier hZero.2.1 hZero.2.2
  next =>
    intro hFactors rho hCarrier hPos hLt
    have hCases :=
      (pairedDirichletZeroCarrier_eq_zero_iff chi rho).1 hCarrier
    cases hCases with
    | inl hChi =>
      have hCompleted : chi.completedLFunction rho = 0 :=
        (symmetricCompletedLFunction_eq_zero_iff_completedLFunction_eq_zero
          chi rho).1 hChi
      exact hFactors.1 rho
        (And.intro hCompleted (And.intro hPos hLt))
    | inr hInv =>
      have hCompleted :
          (Inv.inv chi).completedLFunction rho = 0 :=
        (symmetricCompletedLFunction_eq_zero_iff_completedLFunction_eq_zero
          (Inv.inv chi) rho).1 hInv
      exact hFactors.2 rho
        (And.intro hCompleted (And.intro hPos hLt))

theorem dirichletERH_inv_iff_of_isPrimitive
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    DirichletERH (Inv.inv chi) <-> DirichletERH chi := by
  have hInvPrimitive : DirichletCharacter.IsPrimitive (Inv.inv chi) :=
    BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive
  constructor
  next =>
    intro hInv rho hZero
    have hSymmetric : symmetricCompletedLFunction chi rho = 0 :=
      (symmetricCompletedLFunction_eq_zero_iff_completedLFunction_eq_zero
        chi rho).2 hZero.1
    have hMirrorSymmetric :
        symmetricCompletedLFunction (Inv.inv chi) (1 - rho) = 0 := by
      rw [symmetricCompletedLFunction_one_sub hInvPrimitive]
      simp only [inv_inv]
      rw [hSymmetric, mul_zero]
    have hMirrorCompleted :
        (Inv.inv chi).completedLFunction (1 - rho) = 0 :=
      (symmetricCompletedLFunction_eq_zero_iff_completedLFunction_eq_zero
        (Inv.inv chi) (1 - rho)).1 hMirrorSymmetric
    have hMirrorPos : 0 < (1 - rho).re := by
      change 0 < 1 - rho.re
      linarith [hZero.2.2]
    have hMirrorLt : (1 - rho).re < 1 := by
      change 1 - rho.re < 1
      linarith [hZero.2.1]
    have hLine := hInv (1 - rho)
      (And.intro hMirrorCompleted (And.intro hMirrorPos hMirrorLt))
    change 1 - rho.re = 1 / 2 at hLine
    linarith
  next =>
    intro hChi rho hZero
    have hSymmetric :
        symmetricCompletedLFunction (Inv.inv chi) rho = 0 :=
      (symmetricCompletedLFunction_eq_zero_iff_completedLFunction_eq_zero
        (Inv.inv chi) rho).2 hZero.1
    have hMirrorSymmetric :
        symmetricCompletedLFunction chi (1 - rho) = 0 := by
      rw [symmetricCompletedLFunction_one_sub hPrimitive]
      rw [hSymmetric, mul_zero]
    have hMirrorCompleted : chi.completedLFunction (1 - rho) = 0 :=
      (symmetricCompletedLFunction_eq_zero_iff_completedLFunction_eq_zero
        chi (1 - rho)).1 hMirrorSymmetric
    have hMirrorPos : 0 < (1 - rho).re := by
      change 0 < 1 - rho.re
      linarith [hZero.2.2]
    have hMirrorLt : (1 - rho).re < 1 := by
      change 1 - rho.re < 1
      linarith [hZero.2.1]
    have hLine := hChi (1 - rho)
      (And.intro hMirrorCompleted (And.intro hMirrorPos hMirrorLt))
    change 1 - rho.re = 1 / 2 at hLine
    linarith

theorem pairedDirichletERH_iff_dirichletERH_of_isPrimitive
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    PairedDirichletERH chi <-> DirichletERH chi := by
  constructor
  next =>
    intro hPair
    exact ((pairedDirichletERH_iff chi).1 hPair).1
  next =>
    intro hChi
    exact (pairedDirichletERH_iff chi).2
      (And.intro hChi
        ((dirichletERH_inv_iff_of_isPrimitive hPrimitive).2 hChi))

end

end RobinBV.NumberField
