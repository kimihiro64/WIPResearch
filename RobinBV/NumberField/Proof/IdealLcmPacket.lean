import RobinBV.NumberField.Definitions.IdealLcmPacket

/-!
# Prime-factor profile of the ideal lcm packet

This module identifies the normalized factor multiset of the complete
prime-ideal packet and proves that every selected prime ideal occurs with its
prescribed logarithmic exponent.
-/

open UniqueFactorizationMonoid

namespace RobinBV.NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

private def idealLcmPacketFactors (B : Nat) :
    Multiset (Ideal (NumberField.RingOfIntegers K)) :=
  (primeIdealsUpToNorm K B).val.bind fun P =>
    Multiset.replicate (Nat.log (Ideal.absNorm P) B) P

private theorem idealLcmPacketFactors_prod (B : Nat) :
    (idealLcmPacketFactors K B).prod = idealLcmPacket K B := by
  rw [idealLcmPacketFactors, Multiset.prod_bind]
  simp only [Multiset.prod_replicate]
  exact Finset.prod_map_val (primeIdealsUpToNorm K B)
    (fun P => P ^ Nat.log (Ideal.absNorm P) B)

private theorem idealLcmPacketFactors_prime
    (B : Nat) {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (idealLcmPacketFactors K B) P) : Prime P := by
  rw [idealLcmPacketFactors, Multiset.mem_bind] at hP
  choose Q hQ hPQ using hP
  rw [Multiset.mem_replicate] at hPQ
  have hQFinset : Membership.mem (primeIdealsUpToNorm K B) Q := by
    simpa using hQ
  exact hPQ.2.symm.subst (mem_primeIdealsUpToNorm_prime K hQFinset)

/-- The normalized factorization of the ideal lcm packet is the complete
multiset of selected prime ideals repeated by their prescribed exponents. -/
theorem normalizedFactors_idealLcmPacket (B : Nat) :
    normalizedFactors (idealLcmPacket K B) = idealLcmPacketFactors K B := by
  rw [(idealLcmPacketFactors_prod K B).symm]
  exact normalizedFactors_prod_of_prime
    (fun _P hP => idealLcmPacketFactors_prime K B hP)

private theorem count_idealLcmPacketFactors
    (B : Nat) {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (primeIdealsUpToNorm K B) P) :
    Multiset.count P (idealLcmPacketFactors K B) =
      Nat.log (Ideal.absNorm P) B := by
  classical
  rw [idealLcmPacketFactors, Multiset.count_bind]
  change (primeIdealsUpToNorm K B).sum
      (fun Q => Multiset.count P
        (Multiset.replicate (Nat.log (Ideal.absNorm Q) B) Q)) =
    Nat.log (Ideal.absNorm P) B
  calc
    _ = Multiset.count P
        (Multiset.replicate (Nat.log (Ideal.absNorm P) B) P) := by
      apply Finset.sum_eq_single P
      next =>
        intro Q _hQ hQP
        rw [Multiset.count_replicate]
        simp [hQP]
      next =>
        intro hNot
        exact False.elim (hNot hP)
    _ = Nat.log (Ideal.absNorm P) B :=
      Multiset.count_replicate_self P (Nat.log (Ideal.absNorm P) B)

/-- Every selected prime ideal occurs in the packet factorization with the
largest exponent whose norm power is at most the packet frontier. -/
theorem count_normalizedFactors_idealLcmPacket
    (B : Nat) {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (primeIdealsUpToNorm K B) P) :
    Multiset.count P (normalizedFactors (idealLcmPacket K B)) =
      Nat.log (Ideal.absNorm P) B := by
  rw [normalizedFactors_idealLcmPacket, count_idealLcmPacketFactors K B hP]

end


end RobinBV.NumberField
