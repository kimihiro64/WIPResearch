import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import RobinBV.NumberField.Proof.PairedDirichletZeroDivisor
import RobinBV.NumberField.Proof.QuadraticLZeroMass

/-!
# Multiplicity index for the paired Dirichlet carrier

This module constructs an exact value-preserving equivalence between the
nonzero divisor index of the dual-character product and the disjoint sum of
the two factor indices.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz

noncomputable section

abbrev PairedDirichletZeroIndex
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) : Type :=
  {p : Sigma fun z : Complex =>
      Fin (Int.toNat
        (MeromorphicOn.divisor (pairedDirichletZeroCarrier chi)
          (Set.univ : Set Complex) z)) // Ne p.1 0}

abbrev pairedDirichletZeroValue
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (p : PairedDirichletZeroIndex chi) : Complex :=
  p.1.1

noncomputable def pairedDirichletZeroIndexEquivData
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) :
    {e : Equiv (PairedDirichletZeroIndex chi)
        (Sum (QuadraticLZeroIndex chi)
          (QuadraticLZeroIndex (Inv.inv chi))) //
      forall p : PairedDirichletZeroIndex chi,
        pairedDirichletZeroValue p =
          Sum.elim
            (fun q : QuadraticLZeroIndex chi => quadraticLZeroValue q)
            (fun q : QuadraticLZeroIndex (Inv.inv chi) =>
              quadraticLZeroValue q) (e p)} := by
  let pairedMultiplicity : Complex -> Nat := fun z =>
    Int.toNat
      (MeromorphicOn.divisor (pairedDirichletZeroCarrier chi)
        (Set.univ : Set Complex) z)
  let leftMultiplicity : Complex -> Nat := fun z =>
    Int.toNat
      (MeromorphicOn.divisor (symmetricCompletedLFunction chi)
        (Set.univ : Set Complex) z)
  let rightMultiplicity : Complex -> Nat := fun z =>
    Int.toNat
      (MeromorphicOn.divisor
        (symmetricCompletedLFunction (Inv.inv chi))
        (Set.univ : Set Complex) z)
  have hInv : Ne (Inv.inv chi) 1 :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hCount : forall z : Complex,
      pairedMultiplicity z =
        leftMultiplicity z + rightMultiplicity z := by
    intro z
    dsimp [pairedMultiplicity, leftMultiplicity, rightMultiplicity]
    rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (differentiable_pairedDirichletZeroCarrier hchi) z]
    rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (differentiable_symmetricCompletedLFunction hchi) z]
    rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (differentiable_symmetricCompletedLFunction hInv) z]
    simp only [Int.toNat_natCast]
    exact analyticOrderNatAt_pairedDirichletZeroCarrier hchi z
  let fiberEquiv : forall z : Complex,
      Equiv (Fin (pairedMultiplicity z))
        (Sum (Fin (leftMultiplicity z))
          (Fin (rightMultiplicity z))) :=
    fun z =>
      (Equiv.cast (congrArg Fin (hCount z))).trans
        (@finSumFinEquiv (leftMultiplicity z)
          (rightMultiplicity z)).symm
  let sigmaEquiv :
      Equiv (Sigma fun z : Complex => Fin (pairedMultiplicity z))
        (Sum (Sigma fun z : Complex => Fin (leftMultiplicity z))
          (Sigma fun z : Complex => Fin (rightMultiplicity z))) :=
    (Equiv.sigmaCongrRight fiberEquiv).trans
      (Equiv.sigmaSumDistrib
        (fun z : Complex => Fin (leftMultiplicity z))
        (fun z : Complex => Fin (rightMultiplicity z)))
  let nonzeroOnSum :
      Sum (Sigma fun z : Complex => Fin (leftMultiplicity z))
          (Sigma fun z : Complex => Fin (rightMultiplicity z)) -> Prop :=
    fun p => Sum.elim (fun q => Ne q.1 0) (fun q => Ne q.1 0) p
  have hPredicate : forall p :
      Sigma fun z : Complex => Fin (pairedMultiplicity z),
      Ne p.1 0 <-> nonzeroOnSum (sigmaEquiv p) := by
    intro p
    cases p with
    | mk z k =>
      cases hFiber : fiberEquiv z k with
      | inl a =>
        simp [sigmaEquiv, nonzeroOnSum, hFiber]
      | inr b =>
        simp [sigmaEquiv, nonzeroOnSum, hFiber]
  let restricted := sigmaEquiv.subtypeEquiv hPredicate
  let distributed := restricted.trans
    (Equiv.subtypeSum (p := nonzeroOnSum))
  have hDistributedValue : forall p :
      {p : Sigma fun z : Complex => Fin (pairedMultiplicity z) //
        Ne p.1 0},
      p.1.1 =
        Sum.elim
          (fun q :
            {q : Sigma fun z : Complex => Fin (leftMultiplicity z) //
              nonzeroOnSum (Sum.inl q)} => q.1.1)
          (fun q :
            {q : Sigma fun z : Complex => Fin (rightMultiplicity z) //
              nonzeroOnSum (Sum.inr q)} => q.1.1)
          (distributed p) := by
    intro p
    cases p with
    | mk p hp =>
      cases p with
      | mk z k =>
        cases hFiber : fiberEquiv z k with
        | inl a =>
          simp [distributed, restricted, sigmaEquiv,
            Equiv.subtypeSum, hFiber]
        | inr b =>
          simp [distributed, restricted, sigmaEquiv,
            Equiv.subtypeSum, hFiber]
  let e : Equiv (PairedDirichletZeroIndex chi)
      (Sum (QuadraticLZeroIndex chi)
        (QuadraticLZeroIndex (Inv.inv chi))) := by
    change Equiv
      {p : Sigma fun z : Complex => Fin (pairedMultiplicity z) //
        Ne p.1 0}
      (Sum
        {p : Sigma fun z : Complex => Fin (leftMultiplicity z) //
          Ne p.1 0}
        {p : Sigma fun z : Complex => Fin (rightMultiplicity z) //
          Ne p.1 0})
    exact distributed
  refine Subtype.mk e ?_
  intro p
  change p.1.1 =
    Sum.elim (fun q => q.1.1) (fun q => q.1.1) (distributed p)
  exact hDistributedValue p

noncomputable def pairedDirichletZeroIndexEquiv
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) :
    Equiv (PairedDirichletZeroIndex chi)
      (Sum (QuadraticLZeroIndex chi)
        (QuadraticLZeroIndex (Inv.inv chi))) :=
  (pairedDirichletZeroIndexEquivData hchi).1

theorem pairedDirichletZeroIndexEquiv_value
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (p : PairedDirichletZeroIndex chi) :
    pairedDirichletZeroValue p =
      Sum.elim (fun q : QuadraticLZeroIndex chi => quadraticLZeroValue q)
        (fun q : QuadraticLZeroIndex (Inv.inv chi) =>
          quadraticLZeroValue q)
        (pairedDirichletZeroIndexEquiv hchi p) := by
  exact (pairedDirichletZeroIndexEquivData hchi).2 p

end

end RobinBV.NumberField
