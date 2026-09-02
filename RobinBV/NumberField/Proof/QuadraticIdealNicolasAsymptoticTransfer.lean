import RobinBV.NumberField.Proof.IdealNicolasTransfer
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

end

end RobinBV.NumberField
