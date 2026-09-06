import RobinBV.NumberField.Proof.MovingCharacterPacketCancellation

/-!
# A four-character packet skipping three complete prime-power layers

For a character of exact order six, the alternating packet
1-chi^2-chi^3+chi^5 cancels power fibers two, three and four.
The universal arithmetic cutoff limit comes from the full packet theorem,
not a finite numerical test.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter
open scoped Classical

noncomputable section

/-- The four actual character twists of the sixth-order packet. -/
def orderSixPacketCharacters {N : Nat} (chi : DirichletCharacter Complex N) :
    Fin 4 -> DirichletCharacter Complex N := fun i =>
  match i.val with
  | 0 => 1
  | 1 => chi^2
  | 2 => chi^3
  | _ => chi^5

/-- Alternating inclusion-exclusion weights of the four-character packet. -/
def orderSixPacketWeights : Fin 4 -> Complex := fun i =>
  match i.val with
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | _ => 1

/-- Every complete powered-character fiber cancels at indices 2,3,4. -/
theorem orderSixPacket_power_fibers_zero
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hOrder : orderOf chi=6)
    {j : Nat} (hjLow : 2 <= j) (hjHigh : j < 5) (psi : DirichletCharacter Complex N) :
    ((Finset.univ : Finset (Fin 4)).filter (fun i => (orderSixPacketCharacters chi i)^j=psi)).sum
      orderSixPacketWeights = 0 := by
  have hReduce (k : Nat) : chi^k=chi^(k%6) := by
    simpa only [hOrder] using (pow_mod_orderOf chi k).symm
  have h6 : chi^6=1 := by simpa only [hOrder] using pow_orderOf_eq_one chi
  have h8 : chi^8=chi^2 := by simpa using hReduce 8
  have h9 : chi^9=chi^3 := by simpa using hReduce 9
  have h10 : chi^10=chi^4 := by simpa using hReduce 10
  have h12 : chi^12=1 := by simpa using hReduce 12
  have h15 : chi^15=chi^3 := by simpa using hReduce 15
  have h20 : chi^20=chi^2 := by simpa using hReduce 20
  by_cases hj2 : j=2
  next =>
    subst j
    simp only [Finset.sum_filter, Fin.sum_univ_succ]
    norm_num [orderSixPacketCharacters,
      orderSixPacketWeights, <- pow_mul, h6, h10]
    split_ifs <;> ring
  next =>
    by_cases hj3 : j=3
    next =>
      subst j
      simp only [Finset.sum_filter, Fin.sum_univ_succ]
      norm_num [orderSixPacketCharacters,
        orderSixPacketWeights, <- pow_mul, h6, h9, h15]
      split_ifs <;> ring
    next =>
      have hj4 : j=4 := by omega
      subst j
      simp only [Finset.sum_filter, Fin.sum_univ_succ]
      norm_num [orderSixPacketCharacters,
        orderSixPacketWeights, <- pow_mul, h8, h12, h20]
      split_ifs <;> ring

/-- The first surviving selected layer has principal fiber weight exactly one. -/
theorem orderSixPacket_principal_fiber_five
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hOrder : orderOf chi=6) :
    ((Finset.univ : Finset (Fin 4)).filter (fun i => (orderSixPacketCharacters chi i)^5=1)).sum
      orderSixPacketWeights = 1 := by
  have hOne (k : Nat) : chi^k=1 <-> Dvd.dvd (6 : Nat) k := by
    rw [<- orderOf_dvd_iff_pow_eq_one, hOrder]
  simp only [Finset.sum_filter, Fin.sum_univ_succ]
  norm_num [orderSixPacketCharacters,
    orderSixPacketWeights, <- pow_mul, hOne]

/-- Unconditional exact arithmetic limit after the second, third and
fourth complete root layers cancel; the fifth layer supplies -5/4. -/
theorem orderSixPacket_arithmetic_asymptotic
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hOrder : orderOf chi=6) :
    Tendsto (fun P : Nat =>
      ((((P : Real)^((4 : Real)/5)*Real.log P : Real) : Complex) *
        centeredCharacterPacketPrefix (Finset.univ : Finset (Fin 4))
          (orderSixPacketCharacters chi) orderSixPacketWeights 1 P))
      atTop (nhds (-(5 : Complex)/4)) := by
  have h := centeredCharacterPacket_power_cancellation_resonance
    (Finset.univ : Finset (Fin 4)) (orderSixPacketCharacters chi) orderSixPacketWeights
    1 5 (by norm_num) (by norm_num)
    (fun j hjLow hjHigh psi => orderSixPacket_power_fibers_zero chi hOrder hjLow hjHigh psi)
  rw [orderSixPacket_principal_fiber_five chi hOrder] at h
  convert h using 1 <;> norm_num

end

end RobinBV.NumberField
