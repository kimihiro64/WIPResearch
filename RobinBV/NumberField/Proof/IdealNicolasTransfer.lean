import RobinBV.NumberField.Definitions.IdealNicolasTransfer
import RobinBV.NumberField.Proof.IdealEulerReserve

/-!
# Exact Nicolas-to-ideal-Robin transfer

At every nondegenerate natural frontier, the packet Robin margin is exactly
the negative finite Nicolas oscillation minus the complete height and tower
losses.  No analytic estimate is used here.
-/

namespace RobinBV.NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Every finite prime-ideal Mertens product is positive. -/
theorem idealMertensProduct_pos (B : Nat) :
    0 < idealMertensProduct K B := by
  unfold idealMertensProduct
  apply Finset.prod_pos
  intro P hP
  have hq := one_lt_absNorm_of_mem_primeIdealsUpToNorm K hP
  have hqReal : (1 : Real) < Ideal.absNorm P := by exact_mod_cast hq
  have hInvLt : Inv.inv (Ideal.absNorm P : Real) < 1 := by
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (a := (1 : Real))
        (b := (Ideal.absNorm P : Real)) zero_lt_one hqReal)
  exact sub_pos.mpr hInvLt

/-- On the positive domain, the Nicolas logarithm expands into the
Euler--Mascheroni constant, residue, theta height, and Mertens product. -/
theorem idealNicolasLogMertensOscillation_eq_expanded
    {kappa : Real} (hkappa : 0 < kappa) (B : Nat)
    (hTheta : 1 < idealChebyshevTheta K B) :
    idealNicolasLogMertensOscillation K kappa B =
      Real.eulerMascheroniConstant + Real.log kappa +
        Real.log (Real.log (idealChebyshevTheta K B)) +
          Real.log (idealMertensProduct K B) := by
  have hLogThetaPos : 0 < Real.log (idealChebyshevTheta K B) :=
    Real.log_pos hTheta
  have hProductPos := idealMertensProduct_pos K B
  unfold idealNicolasLogMertensOscillation idealNicolasFunction
  rw [Real.log_mul
    (mul_ne_zero
      (mul_ne_zero (Real.exp_ne_zero _) hkappa.ne') hLogThetaPos.ne')
    hProductPos.ne']
  rw [Real.log_mul
    (mul_ne_zero (Real.exp_ne_zero _) hkappa.ne') hLogThetaPos.ne']
  rw [Real.log_mul (Real.exp_ne_zero _) hkappa.ne']
  rw [Real.log_exp]

/-- Exact signed Nicolas-to-Robin identity for the complete ideal lcm packet.
The two losses retain their signs and contain every prime-ideal layer. -/
theorem idealLcmPacketRobinLogMargin_eq_neg_nicolasLog_sub_height_sub_tower
    {kappa : Real} (hkappa : 0 < kappa) (B : Nat)
    (hTheta : 1 < idealChebyshevTheta K B) :
    idealLcmPacketRobinLogMargin K kappa B =
      -idealNicolasLogMertensOscillation K kappa B -
        idealLcmHeightLoss K B - idealLcmTowerReserve K B := by
  have hLogAbundancy :=
    log_idealAbundancy_idealLcmPacket_eq_mertens_sub_reserve K B
  have hNicolas :=
    idealNicolasLogMertensOscillation_eq_expanded K hkappa B hTheta
  unfold idealLcmPacketRobinLogMargin idealLcmHeightLoss
  rw [hLogAbundancy, hNicolas]
  rw [log_absNorm_idealLcmPacket]
  ring

end

end RobinBV.NumberField
