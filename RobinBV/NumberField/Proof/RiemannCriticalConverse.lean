import Robin1984.NicolasLandau.NicolasLandauRightmostRay
import RobinBV.NumberField.Proof.RiemannCriticalBound

/-!
# The principal critical-tail bound implies RH

A finite critical-scale bound contradicts Robin1984's proved negative
Omega excursion under failure of RH. The source is the actual centered
Chebyshev tail, not a new oscillation assumption.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set Filter Asymptotics

noncomputable section

/-- Any eventual critical-scale bound with a fixed nonnegative coefficient
forces RH, independently of the coefficient's particular value. -/
theorem riemannHypothesis_of_eventual_critical_bound
    {C : Real} (hC : 0 <= C)
    (hBound : Filter.Eventually (fun x : Real =>
      abs (Robin1984.nicolasJ x) <= C / (Real.sqrt x * Real.log x)) atTop) :
    RiemannHypothesis := by
  have hBigO : IsBigO atTop Robin1984.nicolasJ
      (fun x : Real => x ^ (-(1 / 2 : Real))) := by
    apply IsBigO.of_bound C
    filter_upwards [hBound, Filter.eventually_ge_atTop (Real.exp 1)] with x hBound hx
    have hxPos : 0 < x := (Real.exp_pos 1).trans_le hx
    have hLogOne : 1 <= Real.log x := by
      have hLog := Real.log_le_log (Real.exp_pos 1) hx
      simpa only [Real.log_exp] using hLog
    have hInvLog : Inv.inv (Real.log x) <= 1 := by
      simpa only [one_div, inv_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hLogOne
    have hPowerNonneg : 0 <= x ^ (-(1 / 2 : Real)) := Real.rpow_nonneg hxPos.le _
    calc
      norm (Robin1984.nicolasJ x) = abs (Robin1984.nicolasJ x) := Real.norm_eq_abs _
      _ <= C / (Real.sqrt x * Real.log x) := hBound
      _ = C * (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) := by
        rw [quadraticCriticalKernelBase_eq hxPos.le]
        ring
      _ <= C * x ^ (-(1 / 2 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hInvLog hPowerNonneg
      _ = C * norm (x ^ (-(1 / 2 : Real))) := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxPos _)]
  by_contra hNotRH
  choose b hbPos hbHalf hOmega using
    Robin1984.exists_nicolasJ_omegaMinus_of_not_riemannHypothesis hNotRH
  have hLittle : IsLittleO atTop Robin1984.nicolasJ (fun x : Real => x ^ (-b)) :=
    hBigO.trans_isLittleO (Robin1984.rpow_neg_oneHalf_isLittleO_rpow_neg hbHalf)
  have hScalePos : Filter.Eventually (fun x : Real => 0 < x ^ (-b)) atTop := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    exact Real.rpow_pos_of_pos hx _
  exact (not_atTopOmegaMinus_of_isLittleO hScalePos hLittle) hOmega

/-- The canonical mass-normalized principal critical inequality forces RH. -/
theorem riemannHypothesis_of_riemannCriticalBound
    (hBound : RiemannCriticalBound) : RiemannHypothesis := by
  have hC : 0 <= riemannXiZeroMass + 1 := by linarith [riemannXiZeroMass_nonneg]
  exact riemannHypothesis_of_eventual_critical_bound hC
    (hBound 1 (by norm_num : (0 : Real) < 1))

end

end RobinBV.NumberField
