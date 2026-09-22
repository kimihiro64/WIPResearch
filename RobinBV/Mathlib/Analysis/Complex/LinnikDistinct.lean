/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LinnikRecurrence

/-!
# The B(p,a) consumer in Linnik's distinct-prefix branch

This module gives the already proved local congruence estimate its complete
finite-sum consumer. Once the source Holder step represents the distinct
square sum by these packets, the theorem at the end substitutes the explicit
`B(p,a)` cardinality bound directly into the full Vinogradov mean value.
-/

set_option autoImplicit false

namespace Finset

/-- The recurrence packet attached to `B(p,a)`: each admissible prefix pair
is weighted by the number of compatible tail pairs. -/
noncomputable def linnikShiftedRecurrencePacketCount
    (p k a X : Nat) (hp : 0 < p) (hx : X < p ^ k)
    (tailCount : linnikShiftedCongruencePairs p k a X hp hx -> Nat) : Nat :=
  Finset.univ.sum tailCount

/-- A uniform tail bound turns the recurrence packet into the product of the
`B(p,a)` cardinality and that tail bound. -/
theorem linnikShiftedRecurrencePacketCount_le_card_mul
    (p k a X M : Nat) (hp : 0 < p) (hx : X < p ^ k)
    (tailCount : linnikShiftedCongruencePairs p k a X hp hx -> Nat)
    (htail : forall b, tailCount b <= M) :
    linnikShiftedRecurrencePacketCount p k a X hp hx tailCount <=
      Fintype.card (linnikShiftedCongruencePairs p k a X hp hx) * M := by
  unfold linnikShiftedRecurrencePacketCount
  calc
    Finset.univ.sum tailCount <= Finset.univ.sum (fun _b => M) := by
      apply Finset.sum_le_sum
      intro b hb
      exact htail b
    _ = Fintype.card (linnikShiftedCongruencePairs p k a X hp hx) * M := by
      simp

/-- Substitution of the proved `B(p,a)` estimate into its recurrence packet.
No local congruence count remains on the right. -/
theorem linnikShiftedRecurrencePacketCount_le_explicit
    (p k a X M : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (hx : X < p ^ k)
    (tailCount : linnikShiftedCongruencePairs p k a X hp.pos hx -> Nat)
    (htail : forall b, tailCount b <= M) :
    linnikShiftedRecurrencePacketCount p k a X hp.pos hx tailCount <=
      (X ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) * M := by
  calc
    _ <= Fintype.card
          (linnikShiftedCongruencePairs p k a X hp.pos hx) * M :=
      linnikShiftedRecurrencePacketCount_le_card_mul
        p k a X M hp.pos hx tailCount htail
    _ <= (X ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) * M :=
      Nat.mul_le_mul_right M
        (card_linnikShiftedCongruencePairs_le p k a X hp hk hkp hx)

/-- Complete consumer from a source representation of the distinct square sum
by one `B(p,a)` recurrence packet to the full mean value. The hypothesis
`hdistinct` is precisely the remaining Holder/residue-class representation;
the local congruence cardinality is eliminated in the conclusion. -/
theorem vinogradovMeanValue_le_of_distinctPacket
    (p k r a X M E : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (hx : X < p ^ k) (hr : 0 < r) (hm : 2 <= k * r)
    (tailCount : linnikShiftedCongruencePairs p k a X hp.pos hx -> Nat)
    (htail : forall b, tailCount b <= M)
    (hdistinct : linnikDistinctSquareSum k r X hr <=
      p ^ E *
        linnikShiftedRecurrencePacketCount p k a X hp.pos hx tailCount) :
    vinogradovMeanValue k (k * r) X <=
      max
        (4 * (p ^ E *
          ((X ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) * M)))
        (4 ^ (k * r) * k ^ (4 * (k * r))) := by
  have hpacket :=
    linnikShiftedRecurrencePacketCount_le_explicit
      p k a X M hp hk hkp hx tailCount htail
  have hdistinctExplicit : linnikDistinctSquareSum k r X hr <=
      p ^ E * ((X ^ k *
        (k.factorial * p ^ (k * (k - 1) / 2))) * M) :=
    le_trans hdistinct (Nat.mul_le_mul_left _ hpacket)
  exact vinogradovMeanValue_le_max_of_distinctSquareSum_le
    k r X
      (p ^ E * ((X ^ k *
        (k.factorial * p ^ (k * (k - 1) / 2))) * M))
      hr hm hdistinctExplicit

end Finset
