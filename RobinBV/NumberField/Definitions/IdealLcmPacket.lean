import RobinBV.NumberField.Definitions.RobinCriterion

/-!
# Complete prime-ideal lcm packets

The ideal packet at frontier `B` contains every prime ideal of absolute norm
at most `B`, each with the largest exponent whose norm power is at most the
frontier. Equal-norm prime ideals remain distinct factors.
-/

namespace RobinBV.NumberField

open UniqueFactorizationMonoid

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The finite set of prime ideals with absolute norm at most `B`. -/
def primeIdealsUpToNorm (B : Nat) :
    Finset (Ideal (NumberField.RingOfIntegers K)) := by
  classical
  exact (idealsUpToNorm K B).filter Prime

/-- The ideal analogue of `Nat.lcmUpto`: each prime ideal receives the largest
exponent whose norm power is at most the frontier. -/
def idealLcmPacket (B : Nat) :
    Ideal (NumberField.RingOfIntegers K) :=
  (primeIdealsUpToNorm K B).prod fun P =>
    P ^ Nat.log (Ideal.absNorm P) B

/-- The prime-ideal Chebyshev function, with every prime ideal counted
separately and every prime-power layer up to the frontier included. -/
def idealChebyshevPsi (B : Nat) : Real :=
  (primeIdealsUpToNorm K B).sum fun P =>
    (Nat.log (Ideal.absNorm P) B : Real) *
      Real.log (Ideal.absNorm P : Real)

theorem mem_primeIdealsUpToNorm_prime
    {B : Nat} {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (primeIdealsUpToNorm K B) P) : Prime P := by
  classical
  exact (Finset.mem_filter.mp hP).2

theorem idealLcmPacket_ne_zero (B : Nat) :
    Not (idealLcmPacket K B = 0) := by
  classical
  unfold idealLcmPacket
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact pow_ne_zero _ (mem_primeIdealsUpToNorm_prime K hP).ne_zero

/-- The packet norm is the complete product of its prime-ideal norm powers. -/
theorem absNorm_idealLcmPacket (B : Nat) :
    Ideal.absNorm (idealLcmPacket K B) =
      (primeIdealsUpToNorm K B).prod fun P =>
        Ideal.absNorm P ^ Nat.log (Ideal.absNorm P) B := by
  unfold idealLcmPacket
  simp

end


end RobinBV.NumberField
