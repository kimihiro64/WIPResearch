import Robin1984.Equivalence.RobinLemmaTwo
import RobinBV.NumberField.Helpers.ZeroKernelShiftedMass

/-!
# Actual shifted xi zero masses and complete kernel errors

The full multiplicity-counted shifted mass is evaluated by the actual xi
logarithmic derivative, with Robin's exact unshifted constant retained.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex

noncomputable section

/-- Complete shifted inverse-square mass of the actual xi divisor. -/
def riemannShiftedZeroMass (a : Real) : Real :=
  tsum (fun p : RiemannXiDivisorZeroIndex =>
    (Inv.inv (norm ((a : Complex)-riemannXiDivisorZeroValue p)))^2)

/-- Actual xi logarithmic-derivative difference equals the full two-pole sum. -/
theorem riemann_twoPoleSum_eq_logDeriv_sub
    (hRH : RiemannHypothesis) {a : Real} (ha : 1 <= a) :
    tsum (fun p : RiemannXiDivisorZeroIndex =>
      (a : Complex)/(riemannXiDivisorZeroValue p*((a : Complex)-riemannXiDivisorZeroValue p))) =
      logDeriv riemannXi (a : Complex) - logDeriv riemannXi 0 := by
  choose P hP using riemannXi_hadamard_factorization_no_monomial
  have hAway (p : RiemannXiDivisorZeroIndex) :
      Not ((a : Complex) = riemannXiDivisorZeroValue p) := by
    intro h
    have hr := congrArg Complex.re h
    have hp := Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
    simp only [Complex.ofReal_re] at hr
    linarith
  have hFormula := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
    (P := P) hP.2 hAway
  rw [Robin1984.riemannXi_hadamardPolynomialDerivative_eval_eq_logDeriv_zero
    hP.1 hP.2] at hFormula
  have hTerms : tsum (fun p : RiemannXiDivisorZeroIndex =>
      1/((a : Complex)-riemannXiDivisorZeroValue p)+1/riemannXiDivisorZeroValue p) =
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          (a : Complex)/(riemannXiDivisorZeroValue p*((a : Complex)-riemannXiDivisorZeroValue p))) := by
    apply tsum_congr
    intro p
    have hRho := riemannXiDivisorZeroValue_ne_zero p
    have hSub := sub_ne_zero.mpr (hAway p)
    field_simp [hRho, hSub]
    ring
  rw [hTerms] at hFormula
  rw [hFormula]
  ring

/-- Exact actual shifted xi mass with the evaluated Robin constant. -/
theorem riemann_shiftedZeroMass_logDeriv
    (hRH : RiemannHypothesis) {a : Real} (ha : 1 <= a) :
    riemannShiftedZeroMass a =
      ((logDeriv riemannXi (a : Complex)-logDeriv riemannXi 0).re -
        (Real.eulerMascheroniConstant+2-Real.log (4*Real.pi))/2)/(a-1/2) := by
  have hReal := Complex.re_tsum_real_div_mul_sub_of_re_eq_half
    riemannXiDivisorZeroValue
    (Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH)
    Robin1984.summable_robinXiZeroWeight ha
  rw [riemann_twoPoleSum_eq_logDeriv_sub hRH ha,
    Robin1984.robinXiZeroConstant_eq_of_riemannHypothesis hRH] at hReal
  change (logDeriv riemannXi (a : Complex)-logDeriv riemannXi 0).re =
    (a-1/2)*riemannShiftedZeroMass a +
      (1/2)*(Real.eulerMascheroniConstant+2-Real.log (4*Real.pi)) at hReal
  apply (eq_div_iff (by linarith : Not (a-1/2=0))).mpr
  nlinarith [hReal]

/-- The exact endpoint constant cancels, leaving a single actual xi logarithmic derivative. -/
theorem riemann_shiftedZeroMass_eq_re_logDeriv
    (hRH : RiemannHypothesis) {a : Real} (ha : 1 <= a) :
    riemannShiftedZeroMass a = (logDeriv riemannXi (a : Complex)).re / (a-1/2) := by
  have hEndpoint : (Real.eulerMascheroniConstant+2-Real.log (4*Real.pi))/2 =
      -(logDeriv riemannXi 0).re := by
    have h := congrArg Complex.re neg_two_mul_logDeriv_riemannXi_zero_eq
    norm_num at h
    linarith
  rw [riemann_shiftedZeroMass_logDeriv hRH ha, Complex.sub_re, hEndpoint]
  ring

/-- Actual shifted xi mass is no larger than Robin's exact constant. -/
theorem riemann_shiftedZeroMass_le (hRH : RiemannHypothesis)
    {a : Real} (ha : 1 <= a) :
    riemannShiftedZeroMass a <= Real.eulerMascheroniConstant+2-Real.log (4*Real.pi) := by
  have h := Complex.tsum_inv_norm_real_sub_sq_le_of_re_eq_half
    riemannXiDivisorZeroValue
    (Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH)
    Robin1984.summable_robinXiZeroWeight ha
  rw [Robin1984.robinXiZeroConstant_eq_of_riemannHypothesis hRH] at h
  exact h

/-- Complete xi kernel error with the actual shifted, rather than crude, mass. -/
theorem norm_riemannZeroKernel_shifted_error_scaled_le
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    norm (((x ^ ((n : Real)-1/2)*Real.log x : Real) : Complex)*
      (tsum (fun p : RiemannXiDivisorZeroIndex =>
        Robin1984.robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) -
      tsum (fun p : RiemannXiDivisorZeroIndex => zeroKernelLeadingTerm n (riemannXiDivisorZeroValue p) x))) <=
      riemannShiftedZeroMass n *
        (Inv.inv (Real.log x)+(2/((n : Real)-1/2))*Inv.inv (Real.log x)^2) := by
  simpa only [riemannShiftedZeroMass, Complex.ofReal_natCast] using
    norm_zeroKernel_sum_leading_error_scaled_shifted_le riemannXiDivisorZeroValue
      (Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH)
      Robin1984.summable_robinXiZeroWeight hn hx

/-- Refined actual Robin arithmetic bound, including the full explicit
trivial-zero correction. The leading constant uses both spectral masses. -/
theorem riemannWeightedIntegral_refined_bound
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    norm (((x ^ ((n : Real)-1/2)*Real.log x : Real) : Complex)*
      (Robin1984.robinPsiWeightedErrorIntegral n x : Complex)) <=
      (n : Real)*Real.sqrt ((Real.eulerMascheroniConstant+2-Real.log (4*Real.pi))*
        riemannShiftedZeroMass n) +
      riemannShiftedZeroMass n *
        (Inv.inv (Real.log x)+(2/((n : Real)-1/2))*Inv.inv (Real.log x)^2) +
      Real.log (2*Real.pi)*x ^ (-(1/2 : Real)) := by
  have hxPos : 0 < x := by linarith
  have hxOne : 1 < x := by linarith
  have hLog : Not (Real.log x = 0) := (Real.log_pos hxOne).ne'
  let F : Complex := ((x ^ ((n : Real)-1/2)*Real.log x : Real) : Complex)
  let J : Complex := (Robin1984.robinPsiWeightedErrorIntegral n x : Complex)
  let K := tsum (fun p : RiemannXiDivisorZeroIndex =>
    Robin1984.robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p)
  have hScale : 0 <= x ^ ((n : Real)-1/2)*Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_pos hxOne).le
  have hPowers : x ^ ((n : Real)-1/2)*x ^ (-(n : Real))=x ^ (-(1/2 : Real)) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  have hScaled : norm (F*(J+K)) <= Real.log (2*Real.pi)*x ^ (-(1/2 : Real)) := by
    have hIdentity := Robin1984.robinPsiWeightedErrorIntegral_eq_zero_sum_correction_all hRH hn hx
    have hTrivial := Robin1984.robinTrivialZeroCorrection_bounds hn hx
    dsimp only [F, J, K]
    rw [hIdentity]
    have hCancel (a b : Complex) : -a-b+a = -b := by ring
    rw [hCancel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hTrivial.1]
    apply (mul_le_mul_of_nonneg_left hTrivial.2 hScale).trans_eq
    calc
      _ = Real.log (2*Real.pi)*(x ^ ((n : Real)-1/2)*x ^ (-(n : Real))) := by field_simp [hLog]
      _ = _ := by rw [hPowers]
  have hKernel : norm (F*K) <=
      (n : Real)*Real.sqrt ((Real.eulerMascheroniConstant+2-Real.log (4*Real.pi))*
        riemannShiftedZeroMass n) +
      riemannShiftedZeroMass n *
        (Inv.inv (Real.log x)+(2/((n : Real)-1/2))*Inv.inv (Real.log x)^2) := by
    have h := norm_zeroKernel_sum_scaled_le_sqrt_add_shifted riemannXiDivisorZeroValue
      (Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH)
      Robin1984.summable_robinXiZeroWeight hn hxOne
    rw [Robin1984.robinXiZeroConstant_eq_of_riemannHypothesis hRH] at h
    simpa only [F, K, riemannShiftedZeroMass, Complex.ofReal_natCast] using h
  have hSplit : F*J=F*(J+K)-F*K := by ring
  change norm (F*J) <= _
  rw [hSplit]
  exact (norm_sub_le _ _).trans ((add_le_add hScaled hKernel).trans_eq (by ring))

end

end RobinBV.NumberField
