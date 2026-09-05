import RobinBV.NumberField.Proof.ImprimitiveCriticalCriterion
import RobinBV.NumberField.Proof.ImprimitivePrimePowerEndpoint

/-!
# Resonant leading term of the complete conductor correction

The resonance count is the number of excluded primes at which the inducing
primitive character equals one. The complete Chebyshev correction differs
from minus this count times log(t) by an explicitly bounded quantity.
This is the pointwise input for the actual inverse-cutoff endpoint term.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set

noncomputable section

/-- Number of resonant excluded primes, counted exactly once each. -/
def imprimitiveResonanceCount {N : Nat} (chi : DirichletCharacter Complex N) : Nat :=
  Finset.sum N.primeFactors (fun p => chi.primitiveCharacter.primePowerResonance p)

/-- Complete finite constant controlling the nonlogarithmic step error. -/
def imprimitiveStepErrorBound {N : Nat} (chi : DirichletCharacter Complex N) : Real :=
  Finset.sum N.primeFactors (fun p => chi.primitiveCharacter.primePowerStepErrorBound p)

theorem imprimitiveStepErrorBound_nonneg
    {N : Nat} (chi : DirichletCharacter Complex N) :
    0 <= imprimitiveStepErrorBound chi := by
  apply Finset.sum_nonneg
  intro p hp
  exact chi.primitiveCharacter.primePowerStepErrorBound_nonneg (Nat.mem_primeFactors.mp hp).1

/-- All excluded primes are retained in the uniform resonant step estimate.
No ERH hypothesis or global prime-distribution estimate is used. -/
theorem norm_imprimitiveChebyshevStep_add_resonance_log_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {t : Real} (ht : 1 <= t) :
    norm (characterChebyshevSum (Nat.floor t) chi -
      characterChebyshevSum (Nat.floor t) chi.primitiveCharacter +
        (imprimitiveResonanceCount chi : Complex) * (Real.log t : Complex)) <=
      imprimitiveStepErrorBound chi := by
  have hExpression : characterChebyshevSum (Nat.floor t) chi -
      characterChebyshevSum (Nat.floor t) chi.primitiveCharacter +
        (imprimitiveResonanceCount chi : Complex) * (Real.log t : Complex) =
      -Finset.sum N.primeFactors (fun p =>
        chi.primitiveCharacter.primePowerChebyshevStep p t -
          (chi.primitiveCharacter.primePowerResonance p : Complex) * (Real.log t : Complex)) := by
    rw [characterChebyshevSum_sub_primitive_eq_sum_primePowers chi (Nat.floor t)]
    simp only [imprimitiveResonanceCount, Nat.cast_sum, Finset.sum_mul,
      Finset.sum_sub_distrib, DirichletCharacter.primePowerChebyshevStep]
    ring
  rw [hExpression, norm_neg]
  calc
    _ <= Finset.sum N.primeFactors (fun p =>
        norm (chi.primitiveCharacter.primePowerChebyshevStep p t -
          (chi.primitiveCharacter.primePowerResonance p : Complex) * (Real.log t : Complex))) :=
      norm_sum_le _ _
    _ <= imprimitiveStepErrorBound chi := by
      apply Finset.sum_le_sum
      intro p hp
      exact chi.primitiveCharacter.norm_primePowerChebyshevStep_sub_resonance_log_le
        (Nat.mem_primeFactors.mp hp).1 ht

/-- Exact normalization of the logarithmic endpoint weight and a bound for
its full residual integral. The secondary integral is not discarded. -/
theorem log_mul_robinRealWeight_one_integral_data
    {x : Real} (hx : 3 <= x) :
    And
      (IntegrableOn (fun t : Real => Real.log t * Robin1984.robinRealWeight 1 t) (Ioi x))
      (And
        (integral (volume.restrict (Ioi x)) (fun t : Real =>
          Real.log t * Robin1984.robinRealWeight 1 t) =
          1 / x + integral (volume.restrict (Ioi x)) (fun t : Real => 1 / (t ^ 2 * Real.log t)))
        (And
          (0 <= integral (volume.restrict (Ioi x)) (fun t : Real => 1 / (t ^ 2 * Real.log t)))
          (integral (volume.restrict (Ioi x)) (fun t : Real => 1 / (t ^ 2 * Real.log t)) <=
            1 / (x * Real.log x)))) := by
  have hxPos : 0 < x := by linarith
  have hxOne : 1 < x := by linarith
  have hLogX : 0 < Real.log x := Real.log_pos hxOne
  let g : Real -> Real := fun t => 1 / (t ^ 2 * Real.log t)
  have hPow : IntegrableOn (fun t : Real => t ^ (-2 : Real)) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : Real) < -1) hxPos
  have hMajor : IntegrableOn (fun t : Real =>
      Inv.inv (Real.log x) * t ^ (-2 : Real)) (Ioi x) :=
    hPow.const_mul (Inv.inv (Real.log x))
  have hPoint (t : Real) (ht : x < t) :
      And (0 <= g t) (g t <= Inv.inv (Real.log x) * t ^ (-2 : Real)) := by
    have htPos : 0 < t := hxPos.trans ht
    have hLogT : 0 < Real.log t := Real.log_pos (hxOne.trans ht)
    have hInvLog : 1 / Real.log t <= 1 / Real.log x :=
      one_div_le_one_div_of_le hLogX (Real.log_le_log hxPos ht.le)
    have hPower : t ^ (-2 : Real) = Inv.inv (t ^ (2 : Nat)) := by
      rw [Real.rpow_neg htPos.le]
      norm_num
    refine And.intro (by dsimp only [g]; positivity) ?_
    rw [hPower]
    calc
      g t = (1 / Real.log t) * Inv.inv (t ^ (2 : Nat)) := by dsimp only [g]; ring
      _ <= (1 / Real.log x) * Inv.inv (t ^ (2 : Nat)) :=
        mul_le_mul_of_nonneg_right hInvLog (by positivity)
      _ = _ := by rw [one_div]
  have hGMeas : Measurable g := by dsimp only [g]; fun_prop
  have hG : IntegrableOn g (Ioi x) := by
    apply hMajor.mono' hGMeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hPoint t ht).1]
    exact (hPoint t ht).2
  have hFunction : EqOn (fun t : Real => t ^ (-2 : Real) + g t)
      (fun t : Real => Real.log t * Robin1984.robinRealWeight 1 t) (Ioi x) := by
    intro t ht
    have htPos : 0 < t := hxPos.trans ht
    have hLogT : 0 < Real.log t := Real.log_pos (hxOne.trans ht)
    dsimp only
    rw [quadraticDedekindRealWeight_one_eq_nicolasTailKernel (hxOne.trans ht)]
    unfold quadraticDedekindNicolasTailKernel
    dsimp only [g]
    rw [Real.rpow_neg htPos.le]
    norm_num
    field_simp [htPos.ne', hLogT.ne']
  have hFull : IntegrableOn (fun t : Real => Real.log t * Robin1984.robinRealWeight 1 t) (Ioi x) :=
    (hPow.add hG).congr_fun hFunction measurableSet_Ioi
  have hPowIntegral : integral (volume.restrict (Ioi x)) (fun t : Real => t ^ (-2 : Real)) = 1 / x := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : Real) < -1) hxPos]
    norm_num [Real.rpow_neg hxPos.le, one_div]
  have hIdentity : integral (volume.restrict (Ioi x)) (fun t : Real =>
      Real.log t * Robin1984.robinRealWeight 1 t) =
      1 / x + integral (volume.restrict (Ioi x)) g := by
    rw [<- setIntegral_congr_fun measurableSet_Ioi hFunction, integral_add hPow hG, hPowIntegral]
  have hNonneg : 0 <= integral (volume.restrict (Ioi x)) g := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hPoint t ht).1
  have hBound : integral (volume.restrict (Ioi x)) g <= 1 / (x * Real.log x) := by
    calc
      _ <= integral (volume.restrict (Ioi x)) (fun t : Real =>
          Inv.inv (Real.log x) * t ^ (-2 : Real)) := by
        apply integral_mono_ae hG hMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hPoint t ht).2
      _ = _ := by rw [integral_const_mul, hPowIntegral]; ring
  exact And.intro hFull (And.intro hIdentity (And.intro hNonneg hBound))

/-- Explicit resonant leading term for the directly integrable complete
conductor correction, including principal characters. The coefficient is the
exact count of resonant excluded primes. No ERH or nonprincipality is assumed. -/
theorem norm_integral_imprimitiveChebyshevStep_add_resonance_div_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Real} (hx : 3 <= x) :
    norm (integral (volume.restrict (Ioi x)) (fun t : Real =>
      (characterChebyshevSum (Nat.floor t) chi -
        characterChebyshevSum (Nat.floor t) chi.primitiveCharacter) *
          (Robin1984.robinRealWeight 1 t : Complex)) +
        (imprimitiveResonanceCount chi : Complex) / (x : Complex)) <=
      (imprimitiveStepErrorBound chi + (imprimitiveResonanceCount chi : Real)) /
        (x * Real.log x) := by
  have hxPos : 0 < x := by linarith
  have hxOne : 1 < x := by linarith
  have hLogX : 0 < Real.log x := Real.log_pos hxOne
  let r : Nat := imprimitiveResonanceCount chi
  let C : Real := imprimitiveStepErrorBound chi
  let D : Complex := integral (volume.restrict (Ioi x)) (fun t : Real =>
    (characterChebyshevSum (Nat.floor t) chi -
      characterChebyshevSum (Nat.floor t) chi.primitiveCharacter) *
        (Robin1984.robinRealWeight 1 t : Complex))
  let L : Real := integral (volume.restrict (Ioi x)) (fun t : Real =>
    Real.log t * Robin1984.robinRealWeight 1 t)
  let E : Real -> Complex := fun t =>
    (characterChebyshevSum (Nat.floor t) chi -
      characterChebyshevSum (Nat.floor t) chi.primitiveCharacter +
        (r : Complex) * (Real.log t : Complex)) * (Robin1984.robinRealWeight 1 t : Complex)
  have hC : 0 <= C := imprimitiveStepErrorBound_nonneg chi
  have hLogData := log_mul_robinRealWeight_one_integral_data hx
  have hWeight := Robin1984.integrableOn_robinRealWeight
    (by norm_num : 1 <= (1 : Nat)) hxOne
  have hDifference := integrableOn_imprimitiveChebyshevStep_mul_weight chi hx
  have hLogComplex : IntegrableOn (fun t : Real =>
      (r : Complex) * ((Real.log t * Robin1984.robinRealWeight 1 t : Real) : Complex)) (Ioi x) :=
    hLogData.1.ofReal.const_mul (r : Complex)
  have hIntegral : integral (volume.restrict (Ioi x)) E =
      D + (r : Complex) * (L : Complex) := by
    calc
      _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
          (characterChebyshevSum (Nat.floor t) chi -
            characterChebyshevSum (Nat.floor t) chi.primitiveCharacter) *
              (Robin1984.robinRealWeight 1 t : Complex) +
          (r : Complex) * ((Real.log t * Robin1984.robinRealWeight 1 t : Real) : Complex)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        push_cast
        ring
      _ = _ := by
        rw [integral_add hDifference hLogComplex, integral_const_mul, integral_complex_ofReal]
  have hNorm : norm (integral (volume.restrict (Ioi x)) E) <= C / (x * Real.log x) := by
    have hMajor := hWeight.const_mul C
    have hBound := norm_integral_le_of_norm_le hMajor
      (show Filter.Eventually (fun t : Real => norm (E t) <= C * Robin1984.robinRealWeight 1 t)
        (ae (volume.restrict (Ioi x))) from by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have hWeightNonneg := Robin1984.robinRealWeight_nonneg (n := 1) (hxOne.trans ht)
          dsimp only [E]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeightNonneg]
          exact mul_le_mul_of_nonneg_right
            (norm_imprimitiveChebyshevStep_add_resonance_log_le chi (hxOne.trans ht).le) hWeightNonneg)
    refine hBound.trans_eq ?_
    rw [integral_const_mul, Robin1984.integral_robinRealWeight
      (by norm_num : 1 <= (1 : Nat)) hxOne]
    norm_num [Real.rpow_neg_one]
    ring
  have hGapNonneg : 0 <= L - 1 / x := by
    dsimp only [L]
    rw [hLogData.2.1]
    linarith [hLogData.2.2.1]
  have hGapLe : L - 1 / x <= 1 / (x * Real.log x) := by
    dsimp only [L]
    rw [hLogData.2.1]
    linarith [hLogData.2.2.2]
  have hResidual : norm ((((r : Real) * (L - 1 / x) : Real) : Complex)) <=
      (r : Real) / (x * Real.log x) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg r) hGapNonneg)]
    calc
      _ <= (r : Real) * (1 / (x * Real.log x)) :=
        mul_le_mul_of_nonneg_left hGapLe (Nat.cast_nonneg r)
      _ = _ := by ring
  have hIdentity : D + (r : Complex) / (x : Complex) =
      integral (volume.restrict (Ioi x)) E - (((r : Real) * (L - 1 / x) : Real) : Complex) := by
    rw [hIntegral]
    push_cast
    ring
  change norm (D + (r : Complex) / (x : Complex)) <= _
  rw [hIdentity]
  calc
    _ <= norm (integral (volume.restrict (Ioi x)) E) +
        norm ((((r : Real) * (L - 1 / x) : Real) : Complex)) := norm_sub_le _ _
    _ <= C / (x * Real.log x) + (r : Real) / (x * Real.log x) := add_le_add hNorm hResidual
    _ = _ := by dsimp only [C, r]; ring

/-- Explicit resonant leading term for the actual complete nonprincipal
conductor correction, obtained from the all-character integral estimate. -/
theorem norm_dirichletWeightedIntegral_sub_primitive_add_resonance_div_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Not (chi = 1)) {x : Real} (hx : 3 <= x) :
    norm (dirichletCharacterWeightedIntegral chi 1 x -
      dirichletCharacterWeightedIntegral chi.primitiveCharacter 1 x +
        (imprimitiveResonanceCount chi : Complex) / (x : Complex)) <=
      (imprimitiveStepErrorBound chi + (imprimitiveResonanceCount chi : Real)) /
        (x * Real.log x) := by
  rw [dirichletWeightedIntegral_sub_primitive_eq chi hchi hx]
  exact norm_integral_imprimitiveChebyshevStep_add_resonance_div_le chi hx

/-- The paired conductor correction has leading term -2r/x, with the full
explicit single-character remainder doubled by exact complex conjugation. -/
theorem norm_pairedWeightedIntegral_sub_primitive_add_resonance_div_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Not (chi = 1)) {x : Real} (hx : 3 <= x) :
    norm (pairedDirichletWeightedIntegral chi 1 x -
      pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x +
        2 * (imprimitiveResonanceCount chi : Complex) / (x : Complex)) <=
      2 * (imprimitiveStepErrorBound chi + (imprimitiveResonanceCount chi : Real)) /
        (x * Real.log x) := by
  let A : Complex := dirichletCharacterWeightedIntegral chi 1 x -
    dirichletCharacterWeightedIntegral chi.primitiveCharacter 1 x +
      (imprimitiveResonanceCount chi : Complex) / (x : Complex)
  have hSingle := norm_dirichletWeightedIntegral_sub_primitive_add_resonance_div_le chi hchi hx
  have hPair : pairedDirichletWeightedIntegral chi 1 x -
      pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x +
        2 * (imprimitiveResonanceCount chi : Complex) / (x : Complex) =
        A + (starRingEnd Complex) A := by
    simp [A, pairedDirichletWeightedIntegral, dirichletCharacterWeightedIntegral_inv_eq_conj]
    ring
  rw [hPair]
  calc
    _ <= norm A + norm ((starRingEnd Complex) A) := norm_add_le _ _
    _ = 2 * norm A := by rw [Complex.norm_conj]; ring
    _ <= 2 * ((imprimitiveStepErrorBound chi + (imprimitiveResonanceCount chi : Real)) /
        (x * Real.log x)) := mul_le_mul_of_nonneg_left hSingle (by norm_num)
    _ = _ := by ring

end

end RobinBV.NumberField
