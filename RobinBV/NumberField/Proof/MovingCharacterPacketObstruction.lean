import RobinBV.Mathlib.NumberTheory.MulChar.PowerPacket
import RobinBV.NumberField.Proof.MovingCharacterPacketCancellation

/-!
# Finite-modulus obstruction to indefinite arithmetic packet cancellation

Canceling all powered-character fibers through a complete higher-power
cycle annihilates the entire actual arithmetic correction at every cutoff.
Thus any nonzero correction has an uncancelled fiber within that cycle.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex
open scoped Classical

noncomputable section

/-- Full-cycle power-fiber cancellation erases the actual arithmetic packet,
including every level shift and complete finite moment, at every cutoff. -/
theorem centeredCharacterPacketPrefix_eq_zero_of_full_power_cycle
    {N : Nat} [NeZero N] {I : Type*}
    (s : Finset I) (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (m P : Nat)
    (hCycle : forall j : Nat, 2 <= j -> j <= Fintype.card (Units (ZMod N))+1 ->
      forall psi : DirichletCharacter Complex N,
        (s.filter (fun i => (chi i)^j=psi)).sum c=0) :
    centeredCharacterPacketPrefix s chi c m P=0 :=
  MulChar.sum_characterFunctional_eq_zero_of_full_power_cycle s chi c hCycle
    (fun eta => centeredCharacterPrefix eta m P)

/-- A nonzero actual arithmetic packet has an uncancelled character fiber
at a higher exponent bounded by one plus the unit-group cardinality. -/
theorem exists_uncancelled_power_fiber_of_prefix_ne_zero
    {N : Nat} [NeZero N] {I : Type*}
    (s : Finset I) (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (m P : Nat) (hNonzero : Not (centeredCharacterPacketPrefix s chi c m P=0)) :
    exists j : Nat, And (2 <= j) (And (j <= Fintype.card (Units (ZMod N))+1)
      (exists psi : DirichletCharacter Complex N,
        Not ((s.filter (fun i => (chi i)^j=psi)).sum c=0))) := by
  by_contra hNo
  apply hNonzero
  apply centeredCharacterPacketPrefix_eq_zero_of_full_power_cycle s chi c m P
  intro j hjLow hjHigh psi
  by_contra hFiber
  exact hNo (Exists.intro j
    (And.intro hjLow (And.intro hjHigh (Exists.intro psi hFiber))))

end

end RobinBV.NumberField
