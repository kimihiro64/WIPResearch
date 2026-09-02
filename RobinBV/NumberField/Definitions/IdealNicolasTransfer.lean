import RobinBV.NumberField.Definitions.IdealEulerReserve

/-!
# Finite Nicolas data for ideal lcm packets

These definitions isolate the prime-ideal theta height, the finite Nicolas
function, and the exact logarithmic losses used to transfer a Nicolas
oscillation to the ideal Robin margin.
-/

namespace RobinBV.NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The prime-ideal Chebyshev theta function at a natural frontier. -/
def idealChebyshevTheta (B : Nat) : Real :=
  (primeIdealsUpToNorm K B).sum fun P =>
    Real.log (Ideal.absNorm P : Real)

/-- The finite number-field Nicolas function at a natural frontier. -/
def idealNicolasFunction (kappa : Real) (B : Nat) : Real :=
  Real.exp Real.eulerMascheroniConstant * kappa *
    Real.log (idealChebyshevTheta K B) * idealMertensProduct K B

/-- The logarithmic finite Nicolas oscillation. -/
def idealNicolasLogMertensOscillation (kappa : Real) (B : Nat) : Real :=
  Real.log (idealNicolasFunction K kappa B)

/-- The loss from using theta rather than the full prime-power height psi. -/
def idealLcmHeightLoss (B : Nat) : Real :=
  Real.log (Real.log (idealChebyshevPsi K B)) -
    Real.log (Real.log (idealChebyshevTheta K B))

/-- The normalized logarithmic ideal Robin margin of the complete packet. -/
def idealLcmPacketRobinLogMargin (kappa : Real) (B : Nat) : Real :=
  Real.log (idealAbundancy K (idealLcmPacketNonZero K B)) -
    Real.eulerMascheroniConstant - Real.log kappa -
      Real.log (Real.log (Real.log
        (Ideal.absNorm (idealLcmPacket K B) : Real)))

end

end RobinBV.NumberField
