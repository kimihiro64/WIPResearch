import RobinBV.NumberField.Proof.IdealNicolasTransfer
import RobinBV.NumberField.Proof.CriticalCorrectionBridge
import RobinBV.NumberField.Proof.QuadraticIdealHeightLossBounds

/-!
# Asymptotically exact quadratic ideal Nicolas transfer

The elementary height and tower losses are both negligible below the critical
half exponent once a half-strength linear lower bound for quadratic ideal theta
is available. Combined with the exact finite transfer identity, this makes the
ideal Robin log margin asymptotic to the negative ideal Nicolas oscillation.
-/

namespace RobinBV.NumberField

open Asymptotics
open Filter

noncomputable section

/-- Under a half-strength prime-ideal theorem, the complete quadratic packet
loss is negligible below the critical half exponent. -/
theorem quadraticIdealLcmTotalLoss_isLittleO_rpow_of_theta_linear
    (D : NumberField.OddFundamentalDiscriminant) {b : Real}
    (hb : b < (1 : Real) / 2)
    (hThetaLinear : Filter.Eventually
      (fun B : Nat =>
        (B : Real) / 2 <= idealChebyshevTheta D.QuadraticField B)
      atTop) :
    (fun B : Nat =>
      idealLcmHeightLoss D.QuadraticField B +
        idealLcmTowerReserve D.QuadraticField B) =o[
      (atTop : Filter Nat)]
      (fun B : Nat => (B : Real) ^ (-b)) := by
  exact
    (quadraticIdealLcmHeightLoss_isLittleO_rpow_of_theta_linear
      D hb hThetaLinear).add
        (quadraticIdealLcmTowerReserve_isLittleO_rpow D hb)

/-- Under a half-strength prime-ideal theorem, the exact quadratic ideal Robin
log margin differs from the negative ideal Nicolas oscillation by a term
negligible below the critical half exponent. -/
theorem quadraticIdealNicolasRobinDiscrepancy_isLittleO_rpow
    (D : NumberField.OddFundamentalDiscriminant) {kappa b : Real}
    (hKappa : 0 < kappa)
    (hb : b < (1 : Real) / 2)
    (hThetaLinear : Filter.Eventually
      (fun B : Nat =>
        (B : Real) / 2 <= idealChebyshevTheta D.QuadraticField B)
      atTop) :
    (fun B : Nat =>
      idealLcmPacketRobinLogMargin D.QuadraticField kappa B +
        idealNicolasLogMertensOscillation D.QuadraticField kappa B) =o[
      (atTop : Filter Nat)]
      (fun B : Nat => (B : Real) ^ (-b)) := by
  have hTotal :=
    quadraticIdealLcmTotalLoss_isLittleO_rpow_of_theta_linear
      D hb hThetaLinear
  have hNeg := hTotal.neg_left
  apply hNeg.congr'
  next =>
    filter_upwards [hThetaLinear, eventually_ge_atTop 4] with B hTheta hB
    have hThetaOne :
        1 < idealChebyshevTheta D.QuadraticField B := by
      have hCast : (4 : Real) <= B := by exact_mod_cast hB
      linarith
    have hIdentity :=
      idealLcmPacketRobinLogMargin_eq_neg_nicolasLog_sub_height_sub_tower
        D.QuadraticField hKappa B hThetaOne
    rw [hIdentity]
    ring
  next =>
    exact Filter.Eventually.of_forall (fun _B => rfl)

/-- A negative Nicolas excursion at any scale below the critical half exponent
forces a positive ideal Robin packet margin at arbitrarily large frontiers. -/
theorem frequently_pos_quadraticIdealRobinMargin_of_frequently_neg_nicolas
    (D : NumberField.OddFundamentalDiscriminant) {kappa b c : Real}
    (hKappa : 0 < kappa)
    (hb : b < (1 : Real) / 2)
    (hc : 0 < c)
    (hThetaLinear : Filter.Eventually
      (fun B : Nat =>
        (B : Real) / 2 <= idealChebyshevTheta D.QuadraticField B)
      atTop)
    (hNegativeOscillation : Filter.Frequently
      (fun B : Nat =>
        idealNicolasLogMertensOscillation D.QuadraticField kappa B <=
          -c * (B : Real) ^ (-b))
      atTop) :
    Filter.Frequently
      (fun B : Nat =>
        0 < idealLcmPacketRobinLogMargin D.QuadraticField kappa B)
      atTop := by
  have hError :=
    quadraticIdealNicolasRobinDiscrepancy_isLittleO_rpow
      D hKappa hb hThetaLinear
  have hcHalf : 0 < c / 2 := by linarith
  have hSmall := hError.bound hcHalf
  have hScalePositive : Filter.Eventually
      (fun B : Nat => 0 < (B : Real) ^ (-b)) atTop := by
    filter_upwards [eventually_ge_atTop 1] with B hB
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < B by omega)) _
  have hJoint :=
    hNegativeOscillation.and_eventually (hSmall.and hScalePositive)
  apply hJoint.mono
  intro B hData
  have hOscillation := hData.1
  have hBound := hData.2.1
  have hScalePos := hData.2.2
  have hAbs :
      abs (idealLcmPacketRobinLogMargin D.QuadraticField kappa B +
        idealNicolasLogMertensOscillation D.QuadraticField kappa B) <=
        (c / 2) * (B : Real) ^ (-b) := by
    simpa [Real.norm_eq_abs, Real.norm_of_nonneg hScalePos.le] using hBound
  have hLower := (abs_le.mp hAbs).1
  nlinarith

/-- Consequently, an eventual nonpositive quadratic ideal Robin packet margin
rules out every frequent negative Nicolas excursion below the critical half
exponent. -/
theorem not_frequently_neg_quadraticIdealNicolas_of_eventually_nonpos_robin
    (D : NumberField.OddFundamentalDiscriminant) {kappa b c : Real}
    (hKappa : 0 < kappa)
    (hb : b < (1 : Real) / 2)
    (hc : 0 < c)
    (hThetaLinear : Filter.Eventually
      (fun B : Nat =>
        (B : Real) / 2 <= idealChebyshevTheta D.QuadraticField B)
      atTop)
    (hRobinNonpos : Filter.Eventually
      (fun B : Nat =>
        idealLcmPacketRobinLogMargin D.QuadraticField kappa B <= 0)
      atTop) :
    Not (Filter.Frequently
      (fun B : Nat =>
        idealNicolasLogMertensOscillation D.QuadraticField kappa B <=
          -c * (B : Real) ^ (-b))
      atTop) := by
  intro hNegativeOscillation
  have hRobinPositive :=
    frequently_pos_quadraticIdealRobinMargin_of_frequently_neg_nicolas
      D hKappa hb hc hThetaLinear hNegativeOscillation
  apply hRobinPositive
  filter_upwards [hRobinNonpos] with B hB
  exact not_lt_of_ge hB

/-- A positive ideal Robin log margin is a literal strict violation of the
normalized ideal Robin inequality for the complete lcm packet. -/
theorem idealLcmPacket_robin_violation_of_pos_logMargin
    (K : Type*) [Field K] [NumberField K]
    {kappa : Real} (hKappa : 0 < kappa) (B : Nat)
    (hHeight : 1 < Real.log
      (Ideal.absNorm (idealLcmPacket K B) : Real))
    (hMargin : 0 < idealLcmPacketRobinLogMargin K kappa B) :
    Real.exp Real.eulerMascheroniConstant * kappa *
        Ideal.absNorm (idealLcmPacket K B) *
        Real.log (Real.log
          (Ideal.absNorm (idealLcmPacket K B) : Real)) <
      (idealDivisorSum K (idealLcmPacketNonZero K B) : Real) := by
  have hNormNat : 0 < Ideal.absNorm (idealLcmPacket K B) :=
    Ideal.absNorm_pos_of_nonZeroDivisors (idealLcmPacketNonZero K B)
  have hNorm :
      (0 : Real) < Ideal.absNorm (idealLcmPacket K B) := by
    exact_mod_cast hNormNat
  have hLogHeight : 0 < Real.log (Real.log
      (Ideal.absNorm (idealLcmPacket K B) : Real)) :=
    Real.log_pos hHeight
  have hAbundancy := idealAbundancy_pos (idealLcmPacketNonZero K B)
  have hLog :
      Real.eulerMascheroniConstant + Real.log kappa +
          Real.log (Real.log
            (Real.log (Ideal.absNorm (idealLcmPacket K B) : Real))) <
        Real.log (idealAbundancy K (idealLcmPacketNonZero K B)) := by
    unfold idealLcmPacketRobinLogMargin at hMargin
    linarith
  have hExp := Real.exp_lt_exp.mpr hLog
  rw [Real.exp_add, Real.exp_add, Real.exp_log hKappa,
    Real.exp_log hLogHeight, Real.exp_log hAbundancy] at hExp
  have hMultiplied := mul_lt_mul_of_pos_right hExp hNorm
  calc
    Real.exp Real.eulerMascheroniConstant * kappa *
        Ideal.absNorm (idealLcmPacket K B) *
        Real.log (Real.log
          (Ideal.absNorm (idealLcmPacket K B) : Real)) =
      (Real.exp Real.eulerMascheroniConstant * kappa *
        Real.log (Real.log
          (Ideal.absNorm (idealLcmPacket K B) : Real))) *
        Ideal.absNorm (idealLcmPacket K B) := by ring
    _ < idealAbundancy K (idealLcmPacketNonZero K B) *
        Ideal.absNorm (idealLcmPacket K B) := hMultiplied
    _ = (idealDivisorSum K (idealLcmPacketNonZero K B) : Real) := by
      unfold idealAbundancy
      change
        (idealDivisorSum K (idealLcmPacketNonZero K B) : Real) /
            (Ideal.absNorm (idealLcmPacket K B) : Real) *
            Ideal.absNorm (idealLcmPacket K B) =
          (idealDivisorSum K (idealLcmPacketNonZero K B) : Real)
      field_simp [hNorm.ne']

/-- Frequent off-critical negative Nicolas excursions therefore produce
arbitrarily large literal violations on quadratic ideal lcm packets. -/
theorem frequently_quadraticIdealLcmPacket_robin_violation_of_frequently_neg_nicolas
    (D : NumberField.OddFundamentalDiscriminant) {kappa b c : Real}
    (hKappa : 0 < kappa)
    (hb : b < (1 : Real) / 2)
    (hc : 0 < c)
    (hThetaLinear : Filter.Eventually
      (fun B : Nat =>
        (B : Real) / 2 <= idealChebyshevTheta D.QuadraticField B)
      atTop)
    (hNegativeOscillation : Filter.Frequently
      (fun B : Nat =>
        idealNicolasLogMertensOscillation D.QuadraticField kappa B <=
          -c * (B : Real) ^ (-b))
      atTop) :
    Filter.Frequently
      (fun B : Nat =>
        Real.exp Real.eulerMascheroniConstant * kappa *
            Ideal.absNorm (idealLcmPacket D.QuadraticField B) *
            Real.log (Real.log (Ideal.absNorm
              (idealLcmPacket D.QuadraticField B) : Real)) <
          (idealDivisorSum D.QuadraticField
            (idealLcmPacketNonZero D.QuadraticField B) : Real))
      atTop := by
  have hPositiveMargin :=
    frequently_pos_quadraticIdealRobinMargin_of_frequently_neg_nicolas
      D hKappa hb hc hThetaLinear hNegativeOscillation
  have hHeight : Filter.Eventually
      (fun B : Nat => 1 < Real.log (Ideal.absNorm
        (idealLcmPacket D.QuadraticField B) : Real)) atTop := by
    filter_upwards [hThetaLinear, eventually_ge_atTop 4] with B hTheta hB
    rw [log_absNorm_idealLcmPacket]
    have hThetaPsi := idealChebyshevTheta_le_psi D.QuadraticField B
    have hCast : (4 : Real) <= B := by exact_mod_cast hB
    linarith
  have hJoint := hPositiveMargin.and_eventually hHeight
  apply hJoint.mono
  intro B hData
  exact idealLcmPacket_robin_violation_of_pos_logMargin
    D.QuadraticField hKappa B hData.2 hData.1

end

end RobinBV.NumberField
