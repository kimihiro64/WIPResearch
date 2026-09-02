import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardConstantRealPart
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedProductLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivative
import RobinBV.NumberField.Proof.QuadraticLZeroMass

/-!
# Endpoint evaluation of the primitive quadratic L zero mass

Under Dirichlet ERH, the inverse-square zero mass is evaluated through the
logarithmic derivative of the symmetric completion at zero.  For a self-dual
character, the functional equation moves the evaluation to one, where the
modulus, ordinary L-function, and gamma-factor contributions separate.  The
final even and odd formulas expose the exact quadratic-field signature terms.
-/

namespace RobinBV.NumberField

open DirichletCharacter
open BombieriVinogradov.SiegelWalfisz
open scoped BigOperators

noncomputable section

variable {N : Nat} [NeZero N]

theorem quadraticLZeroWeight_eq_two_mul_inv_re
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) (p : QuadraticLZeroIndex chi) :
    (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat) =
      2 * (1 / quadraticLZeroValue p).re := by
  let rho : Complex := quadraticLZeroValue p
  have hRhoZero : Not (rho = 0) := p.property
  have hNormZero : Not (norm rho = 0) :=
    norm_ne_zero_iff.mpr hRhoZero
  have hRe : rho.re = (1 / 2 : Real) :=
    quadraticLZeroValue_re_eq_half_of_dirichletERH
      hchi hPrimitive hERH p
  change (Inv.inv (norm rho)) ^ (2 : Nat) = 2 * (1 / rho).re
  rw [one_div, Complex.inv_re, hRe, Complex.normSq_eq_norm_sq]
  field_simp [hNormZero]

theorem quadraticLZeroMass_eq_two_mul_tsum_inv_re
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) :
    quadraticLZeroMass chi =
      2 * tsum (fun p : QuadraticLZeroIndex chi =>
        (1 / quadraticLZeroValue p).re) := by
  have hInvSummable :
      Summable (fun p : QuadraticLZeroIndex chi =>
        (1 / quadraticLZeroValue p).re) := by
    exact_decl_by_ascii_name "BombieriVinogradov.SiegelWalfisz.summable_symmetricCompletedLFunction_divisorZeroIndex\u2080_inv_re" for N chi hchi hPrimitive
  rw [quadraticLZeroMass]
  calc
    tsum (fun p : QuadraticLZeroIndex chi =>
        (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat)) =
        tsum (fun p : QuadraticLZeroIndex chi =>
          2 * (1 / quadraticLZeroValue p).re) := by
      apply tsum_congr
      intro p
      exact quadraticLZeroWeight_eq_two_mul_inv_re
        hchi hPrimitive hERH p
    _ = 2 * tsum (fun p : QuadraticLZeroIndex chi =>
        (1 / quadraticLZeroValue p).re) :=
      hInvSummable.tsum_mul_left 2

/-- The positive ERH zero mass is the negative doubled real logarithmic
derivative of the symmetric completion at zero. -/
theorem quadraticLZeroMass_eq_neg_two_mul_re_logDeriv_zero
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) :
    quadraticLZeroMass chi =
      -2 * (logDeriv (symmetricCompletedLFunction chi) 0).re := by
  choose B hB _hBUnique using
    existsUnique_symmetricCompletedLFunction_hadamardConstant
      hchi hPrimitive
  choose Binv hBinv _hBinvUnique using
    existsUnique_symmetricCompletedLFunction_hadamardConstant
      (chi := Inv.inv chi)
      (BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi)
      (BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive)
  have hBReRaw :=
    symmetricCompletedLFunction_hadamardConstant_re_eq_neg_tsum
      hchi hPrimitive hB hBinv
  have hBRe : B.re =
      -tsum (fun p : QuadraticLZeroIndex chi =>
        (1 / quadraticLZeroValue p).re) := by
    simpa [quadraticLZeroValue] using hBReRaw
  have hMass := quadraticLZeroMass_eq_two_mul_tsum_inv_re
    hchi hPrimitive hERH
  have hLog :=
    logDeriv_symmetricCompletedLFunction_zero_eq_hadamardConstant
      hchi hPrimitive hB
  rw [hLog]
  linarith

/-- Product decomposition at the endpoint `s = 1`.  The dependency theorem
is stated for `re s > 1`; nonvanishing at the boundary allows the same local
logarithmic-derivative proof at one. -/
theorem logDeriv_symmetricCompletedLFunction_one_eq_three_factors
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1)) :
    logDeriv (symmetricCompletedLFunction chi) 1 =
      (Real.log N : Complex) / 2 +
        (logDeriv chi.LFunction 1 + logDeriv chi.gammaFactor 1) := by
  have hPositive : 0 < ((1 : Complex).re) := by norm_num
  have hHalfPlane :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hPositive
  have hEventually : Filter.EventuallyEq (nhds (1 : Complex))
      (symmetricCompletedLFunction chi)
      (fun z : Complex =>
        (N : Complex) ^ (z / 2) *
          (chi.LFunction z * chi.gammaFactor z)) := by
    filter_upwards [hHalfPlane] with z hz
    rw [symmetricCompletedLFunction,
      DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
        chi hz]
  have hCongruent :
      logDeriv (symmetricCompletedLFunction chi) 1 =
        logDeriv
          (fun z : Complex =>
            (N : Complex) ^ (z / 2) *
              (chi.LFunction z * chi.gammaFactor z)) 1 :=
    (logDeriv_congr_nhds hEventually).self_of_nhds
  have hN : Not ((N : Complex) = 0) := by
    exact_mod_cast NeZero.ne N
  have hNormalizationNe :
      Not ((N : Complex) ^ ((1 : Complex) / 2) = 0) := by
    simp [hN]
  have hNormalizationDifferentiable :
      DifferentiableAt Complex
        (fun z : Complex => (N : Complex) ^ (z / 2)) 1 :=
    ((differentiable_id.div_const (2 : Complex)).const_cpow
      (Or.inl hN)).differentiableAt
  have hLFunctionNe : Not (chi.LFunction 1 = 0) :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re
      chi (Or.inl hchi) (by norm_num)
  have hLFunctionDifferentiable :
      DifferentiableAt Complex chi.LFunction 1 :=
    DirichletCharacter.differentiableAt_LFunction chi 1 (Or.inr hchi)
  have hGammaNe : Not (chi.gammaFactor 1 = 0) :=
    DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hPositive
  have hGammaDifferentiable :
      DifferentiableAt Complex chi.gammaFactor 1 :=
    DirichletCharacter.differentiableAt_gammaFactor_of_re_pos chi hPositive
  have hProductNe : Not (chi.LFunction 1 * chi.gammaFactor 1 = 0) :=
    mul_ne_zero hLFunctionNe hGammaNe
  have hOuter :=
    logDeriv_mul 1 hNormalizationNe hProductNe
      hNormalizationDifferentiable
      (hLFunctionDifferentiable.mul hGammaDifferentiable)
  have hInner :=
    logDeriv_mul 1 hLFunctionNe hGammaNe
      hLFunctionDifferentiable hGammaDifferentiable
  calc
    logDeriv (symmetricCompletedLFunction chi) 1 =
        logDeriv
          (fun z : Complex =>
            (N : Complex) ^ (z / 2) *
              (chi.LFunction z * chi.gammaFactor z)) 1 := hCongruent
    _ = logDeriv (fun z : Complex => (N : Complex) ^ (z / 2)) 1 +
        logDeriv (fun z : Complex =>
          chi.LFunction z * chi.gammaFactor z) 1 := hOuter
    _ = (Real.log N : Complex) / 2 +
        (logDeriv chi.LFunction 1 + logDeriv chi.gammaFactor 1) := by
      rw [hInner, logDeriv_symmetricNormalization]

/-- For a self-dual primitive character, the zero mass separates into the
modulus, ordinary L-function, and gamma-factor endpoint contributions. -/
theorem quadraticLZeroMass_eq_log_modulus_add_logDeriv_one
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSelfDual : Inv.inv chi = chi) (hERH : DirichletERH chi) :
    quadraticLZeroMass chi =
      Real.log N + 2 * (logDeriv chi.LFunction 1).re +
        2 * (logDeriv chi.gammaFactor 1).re := by
  have hMass := quadraticLZeroMass_eq_neg_two_mul_re_logDeriv_zero
    hchi hPrimitive hERH
  have hReflection :=
    logDeriv_symmetricCompletedLFunction_one_sub hchi hPrimitive
      (0 : Complex)
  rw [hSelfDual] at hReflection
  have hThree :=
    logDeriv_symmetricCompletedLFunction_one_eq_three_factors hchi
  have hReflectionRe :
      (logDeriv (symmetricCompletedLFunction chi) 1).re =
        -(logDeriv (symmetricCompletedLFunction chi) 0).re := by
    simpa only [sub_zero, Complex.neg_re] using
      congrArg Complex.re hReflection
  have hThreeRe :
      (logDeriv (symmetricCompletedLFunction chi) 1).re =
        Real.log N / 2 + ((logDeriv chi.LFunction 1).re +
          (logDeriv chi.gammaFactor 1).re) := by
    simpa only [Complex.add_re, Complex.div_ofNat_re,
      Complex.ofReal_re] using congrArg Complex.re hThree
  linarith

/-- Even self-dual characters have the real-quadratic gamma contribution. -/
theorem quadraticLZeroMass_eq_even_explicit
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSelfDual : Inv.inv chi = chi)
    (hEven : DirichletCharacter.Even chi) (hERH : DirichletERH chi) :
    quadraticLZeroMass chi =
      Real.log N + 2 * (logDeriv chi.LFunction 1).re -
        Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  have hMass := quadraticLZeroMass_eq_log_modulus_add_logDeriv_one
    hchi hPrimitive hSelfDual hERH
  have hGamma := logDeriv_gammaFactor_of_even hEven
    (s := (1 : Complex)) (by norm_num)
  rw [Complex.digamma_one_half] at hGamma
  have hLogTwo : Complex.log (2 : Complex) =
      (Real.log 2 : Complex) := by
    exact (Complex.ofReal_log (x := (2 : Real)) (by norm_num)).symm
  rw [hLogTwo] at hGamma
  have hGammaRe :
      (logDeriv chi.gammaFactor 1).re =
        -Real.log Real.pi / 2 +
          (1 / 2 : Real) *
            (-2 * Real.log 2 - Real.eulerMascheroniConstant) := by
    simpa only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.mul_re, Complex.add_im,
      Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, zero_div,
      sub_zero] using congrArg Complex.re hGamma
  rw [Real.log_mul (by norm_num : Not ((4 : Real) = 0))
    (by positivity : Not (Real.pi = 0))]
  have hLogFour : Real.log (4 : Real) = 2 * Real.log 2 := by
    calc
      Real.log (4 : Real) = Real.log 2 + Real.log 2 := by
        rw [show (4 : Real) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]
      _ = 2 * Real.log 2 := by ring
  rw [hLogFour]
  linarith

/-- Odd self-dual characters have the imaginary-quadratic gamma contribution. -/
theorem quadraticLZeroMass_eq_odd_explicit
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hSelfDual : Inv.inv chi = chi)
    (hOdd : DirichletCharacter.Odd chi) (hERH : DirichletERH chi) :
    quadraticLZeroMass chi =
      Real.log N + 2 * (logDeriv chi.LFunction 1).re -
        Real.eulerMascheroniConstant - Real.log Real.pi := by
  have hMass := quadraticLZeroMass_eq_log_modulus_add_logDeriv_one
    hchi hPrimitive hSelfDual hERH
  have hGamma := logDeriv_gammaFactor_of_odd hOdd
    (s := (1 : Complex)) (by norm_num)
  have hGamma' :
      logDeriv chi.gammaFactor 1 =
        -(Real.log Real.pi : Complex) / 2 +
          (1 / 2 : Complex) * Complex.digamma 1 := by
    simpa using hGamma
  rw [Complex.digamma_one] at hGamma'
  have hGammaRe :
      (logDeriv chi.gammaFactor 1).re =
        -Real.log Real.pi / 2 +
          (1 / 2 : Real) * (-Real.eulerMascheroniConstant) := by
    simpa only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.mul_re, Complex.add_im,
      Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, zero_div,
      sub_zero] using congrArg Complex.re hGamma'
  linarith

end

end RobinBV.NumberField
