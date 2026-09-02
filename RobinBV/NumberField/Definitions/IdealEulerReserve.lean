import RobinBV.NumberField.Definitions.IdealLcmPacket

/-!
# Finite Euler data for ideal lcm packets

This module defines the nonzero packet used by ideal abundancy, its finite
prime-ideal Mertens product, and the loss contributed by the top exponent of
each local geometric series.
-/

namespace RobinBV.NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The ideal lcm packet regarded as a nonzero divisor. -/
def idealLcmPacketNonZero (B : Nat) :
    nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)) := by
  apply Subtype.mk (idealLcmPacket K B)
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact idealLcmPacket_ne_zero K B

/-- The finite Mertens product over every prime ideal of norm at most `B`. -/
def idealMertensProduct (B : Nat) : Real :=
  (primeIdealsUpToNorm K B).prod fun P =>
    1 - Inv.inv (Ideal.absNorm P : Real)

/-- The exact logarithmic loss from truncating each local Euler factor at the
largest prime-ideal power admitted by the packet frontier. -/
def idealLcmTowerReserve (B : Nat) : Real :=
  (primeIdealsUpToNorm K B).sum fun P =>
    -Real.log (1 - (Inv.inv (Ideal.absNorm P : Real)) ^
      (Nat.log (Ideal.absNorm P) B + 1))

end

end RobinBV.NumberField
