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

theorem absNorm_le_of_mem_primeIdealsUpToNorm
    {B : Nat} {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (primeIdealsUpToNorm K B) P) :
    Ideal.absNorm P <= B := by
  classical
  have hIdeal := (Finset.mem_filter.mp hP).1
  simpa only [idealsUpToNorm, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq] using hIdeal

theorem one_lt_absNorm_of_mem_primeIdealsUpToNorm
    {B : Nat} {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (primeIdealsUpToNorm K B) P) :
    1 < Ideal.absNorm P := by
  have hPrime := mem_primeIdealsUpToNorm_prime K hP
  have hNormZero : Not (Ideal.absNorm P = 0) :=
    Ideal.absNorm_eq_zero_iff.not.mpr hPrime.ne_zero
  have hNormOne : Not (Ideal.absNorm P = 1) :=
    Ideal.absNorm_eq_one_iff.not.mpr
      (Ideal.isPrime_of_prime hPrime).ne_top
  omega

private theorem mem_idealLcmPacketFactors_iff
    (B : Nat) {P : Ideal (NumberField.RingOfIntegers K)} :
    Membership.mem (idealLcmPacketFactors K B) P <->
      Membership.mem (primeIdealsUpToNorm K B) P := by
  constructor
  next =>
    intro hP
    rw [idealLcmPacketFactors, Multiset.mem_bind] at hP
    choose Q hQ hReplicate using hP
    rw [Multiset.mem_replicate] at hReplicate
    have hQFinset : Membership.mem (primeIdealsUpToNorm K B) Q := by
      simpa using hQ
    exact hReplicate.2.symm.subst hQFinset
  next =>
    intro hP
    rw [idealLcmPacketFactors, Multiset.mem_bind]
    apply Exists.intro P
    apply And.intro
    next => simpa using hP
    next =>
      rw [Multiset.mem_replicate]
      apply And.intro
      next =>
        exact Nat.ne_of_gt (Nat.log_pos
          (one_lt_absNorm_of_mem_primeIdealsUpToNorm K hP)
          (absNorm_le_of_mem_primeIdealsUpToNorm K hP))
      next => rfl

/-- The packet support is exactly the set of every prime ideal whose absolute
norm is at most the packet frontier. -/
theorem support_normalizedFactors_idealLcmPacket (B : Nat) :
    (normalizedFactors (idealLcmPacket K B)).toFinset =
      primeIdealsUpToNorm K B := by
  rw [normalizedFactors_idealLcmPacket]
  ext P
  rw [Multiset.mem_toFinset, mem_idealLcmPacketFactors_iff]

/-- The logarithmic height of the ideal lcm packet is exactly the complete
prime-ideal Chebyshev sum at the same frontier. -/
theorem log_absNorm_idealLcmPacket (B : Nat) :
    Real.log (Ideal.absNorm (idealLcmPacket K B) : Real) =
      idealChebyshevPsi K B := by
  classical
  rw [absNorm_idealLcmPacket]
  have hCast :
      (((primeIdealsUpToNorm K B).prod fun P =>
          Ideal.absNorm P ^ Nat.log (Ideal.absNorm P) B : Nat) : Real) =
        (primeIdealsUpToNorm K B).prod fun P =>
          (Ideal.absNorm P : Real) ^ Nat.log (Ideal.absNorm P) B := by
    simp
  rw [hCast]
  have hFactors : forall P,
      Membership.mem (primeIdealsUpToNorm K B) P ->
        Not (((Ideal.absNorm P : Real) ^
          Nat.log (Ideal.absNorm P) B) = 0) := by
    intro P hP
    have hPrime := mem_primeIdealsUpToNorm_prime K hP
    have hNormNat : Not (Ideal.absNorm P = 0) :=
      Ideal.absNorm_eq_zero_iff.not.mpr hPrime.ne_zero
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hNormNat)
  rw [Real.log_prod hFactors]
  unfold idealChebyshevPsi
  apply Finset.sum_congr rfl
  intro P _hP
  rw [Real.log_pow]

end


end RobinBV.NumberField
