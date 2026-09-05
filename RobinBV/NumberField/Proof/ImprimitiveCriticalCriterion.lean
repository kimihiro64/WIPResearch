import RobinBV.NumberField.Proof.ImprimitiveDirichletERH
import RobinBV.NumberField.Proof.ImprimitiveEndpointCorrection
import RobinBV.NumberField.Proof.PairedDirichletMellinConverse

/-!
# The critical integral criterion at arbitrary nonprincipal character level

The actual ambient-level paired integral is retained. Its canonical
coefficient is the zero mass of the inducing primitive character. The
complete finite Euler correction is unconditionally negligible at the
critical scale, so the primitive equivalence transports in both directions.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set Filter

noncomputable section

/-- Complex conjugation changes the full weighted arithmetic integral to its
dual character, without primitivity or an ERH hypothesis. -/
theorem dirichletCharacterWeightedIntegral_inv_eq_conj
    {N : Nat} (chi : DirichletCharacter Complex N) (n : Nat) (x : Real) :
    dirichletCharacterWeightedIntegral (Inv.inv chi) n x =
      (starRingEnd Complex) (dirichletCharacterWeightedIntegral chi n x) := by
  have hStep (k : Nat) : characterChebyshevSum k (Inv.inv chi) =
      (starRingEnd Complex) (characterChebyshevSum k chi) := by
    unfold characterChebyshevSum BombieriVinogradov.VaughanMeanValue.psiCharacterSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [map_mul, Complex.conj_ofReal,
      BombieriVinogradov.DirichletCharacter.conj_apply_eq_inv_apply]
  unfold dirichletCharacterWeightedIntegral
  rw [<- integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hStep, map_mul, Complex.conj_ofReal]

/-- The full paired conductor correction has an explicit inverse-cutoff
bound. No equality between differently typed primitive inverse characters
is silently assumed. -/
theorem norm_pairedWeightedIntegral_sub_primitive_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Not (chi = 1)) {x : Real} (hx : 3 <= x) :
    norm (pairedDirichletWeightedIntegral chi 1 x -
      pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x) <=
        (2 * (Real.log N / Real.log 2) * (1 + 1 / Real.log x)) / x := by
  have hSingle := norm_dirichletWeightedIntegral_sub_primitive_le chi hchi hx
  have hPair : pairedDirichletWeightedIntegral chi 1 x -
      pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x =
      (dirichletCharacterWeightedIntegral chi 1 x -
        dirichletCharacterWeightedIntegral chi.primitiveCharacter 1 x) +
      (starRingEnd Complex) (dirichletCharacterWeightedIntegral chi 1 x -
        dirichletCharacterWeightedIntegral chi.primitiveCharacter 1 x) := by
    simp only [pairedDirichletWeightedIntegral,
      dirichletCharacterWeightedIntegral_inv_eq_conj, map_sub]
    ring
  rw [hPair]
  calc
    _ <= norm (dirichletCharacterWeightedIntegral chi 1 x -
        dirichletCharacterWeightedIntegral chi.primitiveCharacter 1 x) +
      norm ((starRingEnd Complex) (dirichletCharacterWeightedIntegral chi 1 x -
        dirichletCharacterWeightedIntegral chi.primitiveCharacter 1 x)) := norm_add_le _ _
    _ = 2 * norm (dirichletCharacterWeightedIntegral chi 1 x -
        dirichletCharacterWeightedIntegral chi.primitiveCharacter 1 x) := by
      rw [Complex.norm_conj]
      ring
    _ <= 2 * ((Real.log N / Real.log 2 * (1 + 1 / Real.log x)) / x) :=
      mul_le_mul_of_nonneg_left hSingle (by norm_num)
    _ = _ := by ring

/-- The complete paired change of level is smaller than every positive
multiple of the critical scale, unconditionally. -/
theorem eventually_pairedWeightedIntegral_sub_primitive_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Not (chi = 1))
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      norm (pairedDirichletWeightedIntegral chi 1 x -
        pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x) <=
          epsilon / (Real.sqrt x * Real.log x)) atTop := by
  let A : Real := 2 * (Real.log N / Real.log 2) * (1 + 1 / Real.log 3)
  have hLogN : 0 <= Real.log N :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)))
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hLogThree : 0 < Real.log (3 : Real) := Real.log_pos (by norm_num)
  have hA : 0 <= A := by dsimp only [A]; positivity
  let eta : Real := epsilon / (A + 1)
  have hEta : 0 < eta := by dsimp only [eta]; positivity
  have hAEta : A * eta <= epsilon := by
    calc
      _ <= (A + 1) * eta := mul_le_mul_of_nonneg_right (by linarith) hEta.le
      _ = epsilon := by dsimp only [eta]; field_simp
  have hSmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).bound hEta
  filter_upwards [hSmall, Filter.eventually_ge_atTop (3 : Real)] with x hSmall hx
  have hxPos : 0 < x := by linarith
  have hLogX : 0 < Real.log x := Real.log_pos (by linarith)
  have hSqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxPos
  have hDenPos : 0 < Real.sqrt x * Real.log x := mul_pos hSqrtPos hLogX
  have hInvLog : 1 / Real.log x <= 1 / Real.log 3 :=
    one_div_le_one_div_of_le hLogThree (Real.log_le_log (by norm_num) hx)
  have hCoeff : 2 * (Real.log N / Real.log 2) * (1 + 1 / Real.log x) <= A := by
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hCorrection : norm (pairedDirichletWeightedIntegral chi 1 x -
      pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x) <= A / x :=
    (norm_pairedWeightedIntegral_sub_primitive_le chi hchi hx).trans
      (div_le_div_of_nonneg_right hCoeff hxPos.le)
  have hLog : Real.log x <= eta * Real.sqrt x := by
    have hRpow : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hxPos _
    simpa only [Real.norm_eq_abs, abs_of_pos hLogX, abs_of_pos hRpow,
      Real.sqrt_eq_rpow] using hSmall
  have hScaled : A * Real.log x <= epsilon * Real.sqrt x := by
    calc
      _ <= A * (eta * Real.sqrt x) := mul_le_mul_of_nonneg_left hLog hA
      _ = (A * eta) * Real.sqrt x := by ring
      _ <= _ := mul_le_mul_of_nonneg_right hAEta (Real.sqrt_nonneg x)
  have hKey : (A / x) * (Real.sqrt x * Real.log x) <= epsilon := by
    calc
      _ = (A * Real.log x) * (Real.sqrt x / x) := by ring
      _ <= (epsilon * Real.sqrt x) * (Real.sqrt x / x) :=
        mul_le_mul_of_nonneg_right hScaled (by positivity)
      _ = epsilon := by
        calc
          _ = epsilon * (Real.sqrt x * Real.sqrt x) / x := by ring
          _ = epsilon * x / x := by rw [Real.mul_self_sqrt hxPos.le]
          _ = epsilon := by field_simp [hxPos.ne']
  have hCritical : A / x <= epsilon / (Real.sqrt x * Real.log x) := by
    calc
      _ = ((A / x) * (Real.sqrt x * Real.log x)) / (Real.sqrt x * Real.log x) := by
        field_simp [hDenPos.ne']
      _ <= _ := div_le_div_of_nonneg_right hKey hDenPos.le
  exact hCorrection.trans hCritical

/-- The ambient paired integral, normalized by the actual zero mass of its
inducing primitive character. Finite level factors are not counted as
critical-strip zeros. -/
def ImprimitivePairedDirichletCriticalBound
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    Filter.Eventually (fun x : Real =>
      norm (pairedDirichletWeightedIntegral chi 1 x) <=
        (pairedDirichletZeroMass chi.primitiveCharacter + epsilon) /
          (Real.sqrt x * Real.log x)) atTop

/-- The actual ambient and primitive integral criteria are equivalent.
Every epsilon is split between the primitive estimate and the full
unconditional finite-level correction. -/
theorem imprimitivePairedCriticalBound_iff_primitive
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Not (chi = 1)) :
    ImprimitivePairedDirichletCriticalBound chi <->
      PairedDirichletCriticalBound chi.primitiveCharacter := by
  constructor
  next =>
    intro hBound epsilon hEpsilon
    have hHalf : 0 < epsilon / 2 := by linarith
    have hCorrection := eventually_pairedWeightedIntegral_sub_primitive_le chi hchi hHalf
    filter_upwards [hBound (epsilon / 2) hHalf, hCorrection] with x hMain hError
    have hTriangle : norm (pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x) <=
        norm (pairedDirichletWeightedIntegral chi 1 x) +
          norm (pairedDirichletWeightedIntegral chi 1 x -
            pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x) := by
      calc
        _ = norm (pairedDirichletWeightedIntegral chi 1 x -
            (pairedDirichletWeightedIntegral chi 1 x -
              pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x)) := by
          congr 1
          ring
        _ <= _ := norm_sub_le _ _
    calc
      _ <= norm (pairedDirichletWeightedIntegral chi 1 x) +
          norm (pairedDirichletWeightedIntegral chi 1 x -
            pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x) := hTriangle
      _ <= (pairedDirichletZeroMass chi.primitiveCharacter + epsilon / 2) /
          (Real.sqrt x * Real.log x) + (epsilon / 2) / (Real.sqrt x * Real.log x) :=
            add_le_add hMain hError
      _ = _ := by ring
  next =>
    intro hBound epsilon hEpsilon
    have hHalf : 0 < epsilon / 2 := by linarith
    have hCorrection := eventually_pairedWeightedIntegral_sub_primitive_le chi hchi hHalf
    filter_upwards [hBound (epsilon / 2) hHalf, hCorrection] with x hMain hError
    have hTriangle : norm (pairedDirichletWeightedIntegral chi 1 x) <=
        norm (pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x) +
          norm (pairedDirichletWeightedIntegral chi 1 x -
            pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x) := by
      calc
        _ = norm (pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x +
            (pairedDirichletWeightedIntegral chi 1 x -
              pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x)) := by
          congr 1
          ring
        _ <= _ := norm_add_le _ _
    calc
      _ <= norm (pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x) +
          norm (pairedDirichletWeightedIntegral chi 1 x -
            pairedDirichletWeightedIntegral chi.primitiveCharacter 1 x) := hTriangle
      _ <= (pairedDirichletZeroMass chi.primitiveCharacter + epsilon / 2) /
          (Real.sqrt x * Real.log x) + (epsilon / 2) / (Real.sqrt x * Real.log x) :=
            add_le_add hMain hError
      _ = _ := by ring

/-- ERH is equivalent to the actual paired critical integral inequality for
every nonprincipal complex Dirichlet character, primitive or imprimitive,
with the canonical primitive zero-mass coefficient. -/
theorem dirichletERH_iff_imprimitivePairedCriticalBound
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Not (chi = 1)) :
    DirichletERH chi <-> ImprimitivePairedDirichletCriticalBound chi := by
  have hPrimitive := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
    chi hchi
  exact (dirichletERH_iff_primitive chi hchi).trans
    ((dirichletERH_iff_pairedDirichletCriticalBound hPrimitive chi.primitiveCharacter_isPrimitive).trans
      (imprimitivePairedCriticalBound_iff_primitive chi hchi).symm)

end

end RobinBV.NumberField
