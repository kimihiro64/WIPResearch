import RobinBV.NumberField.Proof.QuadraticDedekindERHLogDefect

/-!
# The principal zeta critical integral bound

The actual centered Chebyshev tail is normalized by its complete
multiplicity-weighted xi zero mass. Robin1984 supplies the zero-kernel
estimate and the exact rational endpoint formula; the archimedean and
trivial-zero correction is retained before passing to the critical scale.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set Filter

noncomputable section

theorem riemannXiZeroMass_nonneg : 0 <= riemannXiZeroMass := by
  unfold riemannXiZeroMass
  exact tsum_nonneg (fun _ => sq_nonneg _)

/-- The compatible rational endpoint integral is exactly Nicolas's actual
psi-minus-x tail, including its original kernel. -/
theorem riemannWeightedErrorIntegral_eq_nicolasJ
    {x : Real} (hx : 1 <= x) :
    quadraticRationalWeightedErrorIntegral 1 x = Robin1984.nicolasJ x := by
  unfold quadraticRationalWeightedErrorIntegral Robin1984.nicolasJ Robin1984.nicolasPsiError
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [quadraticRationalRealWeight_one_eq_nicolasTailKernel (hx.trans_lt ht)]

/-- Finite-cutoff RH bound for the actual rational tail, with the complete
nontrivial-zero mass and the full exact trivial-zero correction. -/
theorem abs_nicolasJ_le_zeroMass_scale_add_correction
    (hRH : RiemannHypothesis) {x : Real} (hx : 2 <= x) :
    abs (Robin1984.nicolasJ x) <=
      riemannXiZeroMass * quadraticRobinZeroKernelScale 1 x +
        Robin1984.robinTrivialZeroCorrection 1 x := by
  have hxOne : 1 < x := by linarith
  have hFormula := quadraticRationalWeightedErrorIntegral_one_eq_zero_sum_correction hRH hx
  rw [riemannWeightedErrorIntegral_eq_nicolasJ (by linarith : 1 <= x)] at hFormula
  have hZero := Robin1984.norm_tsum_robinZeroKernel_div_rho_le
    hRH (by norm_num : 1 <= (1 : Nat)) hxOne
  rw [<- riemannXiZeroMass_eq_of_riemannHypothesis hRH] at hZero
  have hCorrection := Robin1984.robinTrivialZeroCorrection_bounds
    (by norm_num : 1 <= (1 : Nat)) hx
  calc
    abs (Robin1984.nicolasJ x) = norm (Robin1984.nicolasJ x : Complex) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = norm (-tsum (fun p : RiemannXiDivisorZeroIndex =>
        Robin1984.robinZeroKernel 1 (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p) - (Robin1984.robinTrivialZeroCorrection 1 x : Complex)) := by
      rw [hFormula]
    _ <= norm (-tsum (fun p : RiemannXiDivisorZeroIndex =>
        Robin1984.robinZeroKernel 1 (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p)) + norm (Robin1984.robinTrivialZeroCorrection 1 x : Complex) :=
      norm_sub_le _ _
    _ = norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
        Robin1984.robinZeroKernel 1 (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p)) + Robin1984.robinTrivialZeroCorrection 1 x := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCorrection.1]
    _ <= _ := add_le_add hZero le_rfl

/-- Critical centered-tail inequality for the principal zeta factor.
The coefficient is the actual multiplicity-weighted xi zero mass. -/
def RiemannCriticalBound : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    Filter.Eventually (fun x : Real =>
      abs (Robin1984.nicolasJ x) <=
        (riemannXiZeroMass + epsilon) / (Real.sqrt x * Real.log x)) atTop

/-- RH implies the principal critical integral inequality, with no loss in
the leading zero-mass coefficient. -/
theorem riemannCriticalBound_of_riemannHypothesis
    (hRH : RiemannHypothesis) : RiemannCriticalBound := by
  intro epsilon hEpsilon
  let M : Real := riemannXiZeroMass
  have hM : 0 <= M := riemannXiZeroMass_nonneg
  let delta : Real := epsilon / (2 * (M + 1))
  have hDelta : 0 < delta := by dsimp only [delta]; positivity
  have hHalf : 0 < epsilon / 2 := by linarith
  have hMDelta : M * delta <= epsilon / 2 := by
    calc
      _ <= (M + 1) * delta := mul_le_mul_of_nonneg_right (by linarith) hDelta.le
      _ = _ := by dsimp only [delta]; field_simp
  have hScale := eventually_quadraticRobinZeroKernelScale_one_le hDelta
  have hCorrection := eventually_robinTrivialZeroCorrection_one_le hHalf
  filter_upwards [hScale, hCorrection, Filter.eventually_ge_atTop (3 : Real)] with x hScale hCorr hx
  have hxPos : 0 < x := by linarith
  have hBaseNonneg : 0 <= x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) := by
    have hLog : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  have hMain : M * quadraticRobinZeroKernelScale 1 x <=
      (M + epsilon / 2) / (Real.sqrt x * Real.log x) := by
    calc
      _ <= M * ((1 + delta) * (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x))) :=
        mul_le_mul_of_nonneg_left hScale hM
      _ = (M * (1 + delta)) * (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) := by ring
      _ <= (M + epsilon / 2) * (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hMDelta]) hBaseNonneg
      _ = _ := by rw [quadraticCriticalKernelBase_eq hxPos.le]; ring
  calc
    _ <= M * quadraticRobinZeroKernelScale 1 x + Robin1984.robinTrivialZeroCorrection 1 x :=
      abs_nicolasJ_le_zeroMass_scale_add_correction hRH (by linarith)
    _ <= (M + epsilon / 2) / (Real.sqrt x * Real.log x) +
        (epsilon / 2) / (Real.sqrt x * Real.log x) := add_le_add hMain hCorr
    _ = _ := by dsimp only [M]; ring

end

end RobinBV.NumberField
