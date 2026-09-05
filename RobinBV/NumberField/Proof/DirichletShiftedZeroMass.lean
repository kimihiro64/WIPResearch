import RobinBV.NumberField.Helpers.ZeroKernelShiftedMass
import RobinBV.NumberField.Proof.DirichletZeroLeadingExpansion

/-!
# Actual shifted Dirichlet zero masses

Under ERH the complete shifted mass is evaluated by logarithmic derivatives
of the actual symmetric completion. Both parities, central zeros and all
analytic multiplicities remain in the canonical divisor index.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex BombieriVinogradov.SiegelWalfisz

noncomputable section

variable {N : Nat} [NeZero N]

/-- Complete shifted mass of the actual completed-L divisor. -/
def dirichletShiftedZeroMass (chi : DirichletCharacter Complex N) (a : Real) : Real :=
  tsum (fun p : QuadraticLZeroIndex chi =>
    (Inv.inv (norm ((a : Complex) - quadraticLZeroValue p)))^2)

/-- The actual full two-pole sum is a difference of logarithmic derivatives. -/
theorem primitiveDirichlet_twoPoleSum_eq_logDeriv_sub
    {chi : DirichletCharacter Complex N} (hChi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi) (hERH : DirichletERH chi)
    {a : Real} (ha : 1 <= a) :
    tsum (fun p : QuadraticLZeroIndex chi =>
      (a : Complex)/(quadraticLZeroValue p*((a : Complex)-quadraticLZeroValue p))) =
      logDeriv (symmetricCompletedLFunction chi) (a : Complex) -
        logDeriv (symmetricCompletedLFunction chi) 0 := by
  have hAway (p : QuadraticLZeroIndex chi) :
      Not ((a : Complex) = quadraticLZeroValue p) := by
    intro h
    have hr := congrArg Complex.re h
    have hp := quadraticLZeroValue_re_eq_half_of_dirichletERH hChi hPrimitive hERH p
    simp only [Complex.ofReal_re] at hr
    linarith
  have hFormula := logDeriv_symmetricCompletedLFunction_eq_hadamardConstant_add_tsum
    hChi hPrimitive (primitiveCharacter_endpoint_isHadamardConstant hChi hPrimitive) hAway
  have hTerms : tsum (fun p : QuadraticLZeroIndex chi =>
      1/((a : Complex)-quadraticLZeroValue p)+1/quadraticLZeroValue p) =
        tsum (fun p : QuadraticLZeroIndex chi =>
          (a : Complex)/(quadraticLZeroValue p*((a : Complex)-quadraticLZeroValue p))) := by
    apply tsum_congr
    intro p
    have hRho : Not (quadraticLZeroValue p = 0) := p.property
    have hSub : Not ((a : Complex)-quadraticLZeroValue p = 0) := sub_ne_zero.mpr (hAway p)
    field_simp [hRho, hSub]
    ring
  change logDeriv (symmetricCompletedLFunction chi) (a : Complex) =
    logDeriv (symmetricCompletedLFunction chi) 0 +
      tsum (fun p : QuadraticLZeroIndex chi =>
        1/((a : Complex)-quadraticLZeroValue p)+1/quadraticLZeroValue p) at hFormula
  rw [hTerms] at hFormula
  rw [hFormula]
  ring

/-- Exact shifted spectral mass in terms of the actual completed-L function. -/
theorem primitiveDirichlet_shiftedZeroMass_logDeriv
    {chi : DirichletCharacter Complex N} (hChi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi) (hERH : DirichletERH chi)
    {a : Real} (ha : 1 <= a) :
    dirichletShiftedZeroMass chi a =
      ((logDeriv (symmetricCompletedLFunction chi) (a : Complex) -
        logDeriv (symmetricCompletedLFunction chi) 0).re - quadraticLZeroMass chi / 2) /
          (a - 1/2) := by
  have hReal := Complex.re_tsum_real_div_mul_sub_of_re_eq_half
    (fun p : QuadraticLZeroIndex chi => quadraticLZeroValue p)
    (quadraticLZeroValue_re_eq_half_of_dirichletERH hChi hPrimitive hERH)
    (summable_quadraticLZeroWeight hChi hPrimitive) ha
  rw [primitiveDirichlet_twoPoleSum_eq_logDeriv_sub hChi hPrimitive hERH ha] at hReal
  change (logDeriv (symmetricCompletedLFunction chi) (a : Complex) -
      logDeriv (symmetricCompletedLFunction chi) 0).re =
    (a-1/2)*dirichletShiftedZeroMass chi a + (1/2)*quadraticLZeroMass chi at hReal
  apply (eq_div_iff (by linarith : Not (a-1/2=0))).mpr
  nlinarith [hReal]

/-- The shifted mass genuinely improves the previous unshifted majorant. -/
theorem primitiveDirichlet_shiftedZeroMass_le
    {chi : DirichletCharacter Complex N} (hChi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi) (hERH : DirichletERH chi)
    {a : Real} (ha : 1 <= a) :
    dirichletShiftedZeroMass chi a <= quadraticLZeroMass chi := by
  exact Complex.tsum_inv_norm_real_sub_sq_le_of_re_eq_half
    (fun p : QuadraticLZeroIndex chi => quadraticLZeroValue p)
    (quadraticLZeroValue_re_eq_half_of_dirichletERH hChi hPrimitive hERH)
    (summable_quadraticLZeroWeight hChi hPrimitive) ha

/-- The completed-function normalization cancels the endpoint constant:
the shifted mass is the real logarithmic derivative divided by its shift. -/
theorem primitiveDirichlet_shiftedZeroMass_eq_re_logDeriv
    {chi : DirichletCharacter Complex N} (hChi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi) (hERH : DirichletERH chi)
    {a : Real} (ha : 1 <= a) :
    dirichletShiftedZeroMass chi a =
      (logDeriv (symmetricCompletedLFunction chi) (a : Complex)).re / (a-1/2) := by
  rw [primitiveDirichlet_shiftedZeroMass_logDeriv hChi hPrimitive hERH ha,
    Complex.sub_re, quadraticLZeroMass_eq_neg_two_mul_re_logDeriv_zero hChi hPrimitive hERH]
  ring

/-- Complete actual Dirichlet zero-kernel leading error with shifted mass. -/
theorem norm_primitiveDirichletZeroKernel_shifted_error_scaled_le
    {chi : DirichletCharacter Complex N} (hChi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi) (hERH : DirichletERH chi)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    norm (((x ^ ((n : Real)-1/2)*Real.log x : Real) : Complex)*
      (tsum (fun p : QuadraticLZeroIndex chi =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x / quadraticLZeroValue p) -
      tsum (fun p : QuadraticLZeroIndex chi => zeroKernelLeadingTerm n (quadraticLZeroValue p) x))) <=
      dirichletShiftedZeroMass chi n *
        (Inv.inv (Real.log x)+(2/((n : Real)-1/2))*Inv.inv (Real.log x)^2) := by
  simpa only [dirichletShiftedZeroMass, Complex.ofReal_natCast] using
    norm_zeroKernel_sum_leading_error_scaled_shifted_le
      (fun p : QuadraticLZeroIndex chi => quadraticLZeroValue p)
      (quadraticLZeroValue_re_eq_half_of_dirichletERH hChi hPrimitive hERH)
      (summable_quadraticLZeroWeight hChi hPrimitive) hn hx

/-- Refined actual arithmetic ERH bound. The complete parity and endpoint
correction has a derived lower-order coefficient, not an added assumption. -/
theorem exists_primitiveDirichletWeightedIntegral_refined_bound
    {chi : DirichletCharacter Complex N} (hChi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi) (hERH : DirichletERH chi)
    {n : Nat} (hn : 2 <= n) :
    exists A : Real, And (0 <= A) (forall x : Real, 3 <= x ->
      norm (((x ^ ((n : Real)-1/2)*Real.log x : Real) : Complex)*
        dirichletCharacterWeightedIntegral chi n x) <=
      (n : Real)*Real.sqrt (quadraticLZeroMass chi * dirichletShiftedZeroMass chi n) +
      dirichletShiftedZeroMass chi n *
        (Inv.inv (Real.log x)+(2/((n : Real)-1/2))*Inv.inv (Real.log x)^2) +
      A*(x ^ (-(1/2 : Real))*Real.log x)) := by
  choose A hA hBound using
    exists_primitiveDirichletWeightedIntegral_add_zeroKernel_bound hChi hPrimitive hERH hn
  refine Exists.intro A (And.intro hA ?_)
  intro x hx
  have hxPos : 0 < x := by linarith
  have hxOne : 1 < x := by linarith
  let F : Complex := ((x ^ ((n : Real)-1/2)*Real.log x : Real) : Complex)
  let J := dirichletCharacterWeightedIntegral chi n x
  let K := tsum (fun p : QuadraticLZeroIndex chi =>
    Robin1984.robinZeroKernel n (quadraticLZeroValue p) x / quadraticLZeroValue p)
  have hScale : 0 <= x ^ ((n : Real)-1/2)*Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_pos hxOne).le
  have hPowers : x ^ ((n : Real)-1/2)*x ^ (-(n : Real))=x ^ (-(1/2 : Real)) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  have hScaled : norm (F*(J+K)) <= A*(x ^ (-(1/2 : Real))*Real.log x) := by
    dsimp only [F, J, K]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale]
    apply (mul_le_mul_of_nonneg_left (hBound x hx) hScale).trans_eq
    calc
      _ = A*(x ^ ((n : Real)-1/2)*x ^ (-(n : Real)))*Real.log x := by ring
      _ = _ := by rw [hPowers]; ring
  have hKernel : norm (F*K) <=
      (n : Real)*Real.sqrt (quadraticLZeroMass chi * dirichletShiftedZeroMass chi n) +
      dirichletShiftedZeroMass chi n *
        (Inv.inv (Real.log x)+(2/((n : Real)-1/2))*Inv.inv (Real.log x)^2) := by
    simpa only [F, K, quadraticLZeroMass, dirichletShiftedZeroMass, Complex.ofReal_natCast] using
      norm_zeroKernel_sum_scaled_le_sqrt_add_shifted
        (fun p : QuadraticLZeroIndex chi => quadraticLZeroValue p)
        (quadraticLZeroValue_re_eq_half_of_dirichletERH hChi hPrimitive hERH)
        (summable_quadraticLZeroWeight hChi hPrimitive) (by omega : 1 <= n) hxOne
  have hSplit : F*J=F*(J+K)-F*K := by ring
  change norm (F*J) <= _
  rw [hSplit]
  exact (norm_sub_le _ _).trans ((add_le_add hScaled hKernel).trans_eq (by ring))

end

end RobinBV.NumberField
