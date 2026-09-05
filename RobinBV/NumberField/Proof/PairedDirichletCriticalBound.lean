import RobinBV.NumberField.Proof.PairedDirichletEndpointBounds

/-!
# Paired Dirichlet critical-scale estimates

The actual exponent-one arithmetic integral is bounded by the complete paired
inverse-square zero mass and an explicit parity-dependent lower-order term.
The zero-kernel factor retains its logarithmic secondary corrections.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

/-- Norm of a complete primitive-character zero kernel sum. -/
theorem norm_tsum_primitiveL_robinZeroKernel_div_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) {n : Nat} (hn : 1 <= n)
    {x : Real} (hx : 1 < x) :
    norm (tsum (fun p : QuadraticLZeroIndex chi =>
      Robin1984.robinZeroKernel n (quadraticLZeroValue p) x / quadraticLZeroValue p)) <=
      quadraticLZeroMass chi * quadraticRobinZeroKernelScale n x := by
  let C := quadraticRobinZeroKernelScale n x
  have hMajor : Summable (fun p : QuadraticLZeroIndex chi =>
      (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat) * C) :=
    (summable_quadraticLZeroWeight hchi hPrimitive).mul_right C
  have hPointwise : forall p : QuadraticLZeroIndex chi,
      norm (Robin1984.robinZeroKernel n (quadraticLZeroValue p) x / quadraticLZeroValue p) <=
        (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat) * C := by
    intro p
    exact Robin1984.norm_robinZeroKernel_div_rho_le_robinXiZeroWeight hn p.2
      (quadraticLZeroValue_re_eq_half_of_dirichletERH hchi hPrimitive hERH p) hx
  have hSeries := hMajor.of_norm_bounded hPointwise
  calc
    _ <= tsum (fun p : QuadraticLZeroIndex chi =>
        norm (Robin1984.robinZeroKernel n (quadraticLZeroValue p) x / quadraticLZeroValue p)) :=
      norm_tsum_le_tsum_norm hSeries.norm
    _ <= tsum (fun p : QuadraticLZeroIndex chi =>
        (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat) * C) :=
      hSeries.norm.tsum_le_tsum hPointwise hMajor
    _ = _ := by rw [tsum_mul_right]; rfl

/-- The paired mass, including both multiplicity-counted families, controls
the paired kernel without a factor lost in the index transfer. -/
theorem norm_tsum_pairedDirichlet_robinZeroKernel_div_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) {n : Nat} (hn : 1 <= n)
    {x : Real} (hx : 1 < x) :
    norm (tsum (fun p : PairedDirichletZeroIndex chi =>
      Robin1984.robinZeroKernel n (pairedDirichletZeroValue p) x / pairedDirichletZeroValue p)) <=
      pairedDirichletZeroMass chi * quadraticRobinZeroKernelScale n x := by
  have hi := BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hp := BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive
  have he := (dirichletERH_inv_iff_of_isPrimitive hPrimitive).2 hERH
  rw [tsum_pairedDirichletZeroKernel_eq_sum hchi
    (fun rho => Robin1984.robinZeroKernel n rho x / rho)
    (summable_primitiveCharacter_robinZeroKernel_div hchi hPrimitive hERH hn hx)
    (summable_primitiveCharacter_robinZeroKernel_div hi hp he hn hx)]
  calc
    _ <= norm (tsum (fun p : QuadraticLZeroIndex chi =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x / quadraticLZeroValue p)) +
      norm (tsum (fun p : QuadraticLZeroIndex (Inv.inv chi) =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x / quadraticLZeroValue p)) :=
      norm_add_le _ _
    _ <= quadraticLZeroMass chi * quadraticRobinZeroKernelScale n x +
        quadraticLZeroMass (Inv.inv chi) * quadraticRobinZeroKernelScale n x :=
      add_le_add (norm_tsum_primitiveL_robinZeroKernel_div_le hchi hPrimitive hERH hn hx)
        (norm_tsum_primitiveL_robinZeroKernel_div_le hi hp he hn hx)
    _ = _ := by rw [pairedDirichletZeroMass_eq_sum hchi hPrimitive]; ring

/-- Expanded critical-scale zero-kernel bound, with its logarithmic corrections. -/
theorem norm_tsum_pairedDirichlet_robinZeroKernel_one_le_explicit
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) {x : Real} (hx : 1 < x) :
    norm (tsum (fun p : PairedDirichletZeroIndex chi =>
      Robin1984.robinZeroKernel 1 (pairedDirichletZeroValue p) x / pairedDirichletZeroValue p)) <=
      pairedDirichletZeroMass chi / (Real.sqrt x * Real.log x) *
        (1 + 1 / Real.log x + 4 / (Real.log x) ^ 2) := by
  have h := norm_tsum_pairedDirichlet_robinZeroKernel_div_le
    hchi hPrimitive hERH (n := 1) (by norm_num) hx
  rw [quadraticRobinZeroKernelScale_one_eq,
    quadraticCriticalKernelBase_eq (by linarith : 0 <= x)] at h
  unfold quadraticRobinZeroKernelCorrection at h
  convert h using 1; ring

/-- Explicit even-parity critical estimate for the actual paired arithmetic
integral. The leading zero-mass coefficient is not inflated. -/
theorem norm_pairedDirichletWeightedIntegral_one_even_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hEven : DirichletCharacter.Even chi) (hERH : DirichletERH chi)
    {x : Real} (hx : 3 <= x) :
    norm (pairedDirichletWeightedIntegral chi 1 x) <=
      pairedDirichletZeroMass chi / (Real.sqrt x * Real.log x) *
        (1 + 1 / Real.log x + 4 / (Real.log x) ^ 2) +
      (1 + 1 / (2 * Real.log x + 1)) *
        (2 + pairedDirichletEvenRemainderConstant N (quadraticLZeroMass chi) / Real.log x) *
          x ^ (-(1 : Real)) := by
  have hFormula := (pairedDirichletWeightedIntegral_one_eq_even_explicit
    hchi hPrimitive hEven hERH hx).2
  have hZero := norm_tsum_pairedDirichlet_robinZeroKernel_one_le_explicit
    hchi hPrimitive hERH (by linarith : 1 < x)
  have hRemainder := norm_pairedDirichletEvenEndpointCorrection_le
    hchi hPrimitive hEven hERH hx
  rw [hFormula]
  exact (norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using hZero) hRemainder)

/-- Explicit odd-parity critical estimate, with logarithmic decay in the
entire nonzero-kernel remainder. -/
theorem norm_pairedDirichletWeightedIntegral_one_odd_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hOdd : DirichletCharacter.Odd chi) (hERH : DirichletERH chi)
    {x : Real} (hx : 3 <= x) :
    norm (pairedDirichletWeightedIntegral chi 1 x) <=
      pairedDirichletZeroMass chi / (Real.sqrt x * Real.log x) *
        (1 + 1 / Real.log x + 4 / (Real.log x) ^ 2) +
      (1 + 1 / (2 * Real.log x + 1)) *
        (pairedDirichletOddRemainderConstant N (quadraticLZeroMass chi) / Real.log x) *
          x ^ (-(1 : Real)) := by
  have hFormula := (pairedDirichletWeightedIntegral_one_eq_odd_explicit
    hchi hPrimitive hOdd hERH hx).2
  have hZero := norm_tsum_pairedDirichlet_robinZeroKernel_one_le_explicit
    hchi hPrimitive hERH (by linarith : 1 < x)
  have hRemainder := norm_pairedDirichletOddEndpointCorrection_le
    hchi hPrimitive hOdd hERH hx
  rw [hFormula]
  exact (norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using hZero) hRemainder)

/-- A character-fixed reciprocal remainder suffices for the eventual
critical criterion; the sharper parity estimates remain available above. -/
theorem exists_pairedDirichletWeightedIntegral_reciprocal_remainder
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) :
    exists A : Real, And (0 <= A) (forall x : Real, 3 <= x ->
      norm (pairedDirichletWeightedIntegral chi 1 x) <=
        pairedDirichletZeroMass chi * quadraticRobinZeroKernelScale 1 x +
          A * x ^ (-(1 : Real))) := by
  let Ce := pairedDirichletEvenRemainderConstant N (quadraticLZeroMass chi)
  let Co := pairedDirichletOddRemainderConstant N (quadraticLZeroMass chi)
  let C := Ce + Co
  let A := 2 * (2 + C / Real.log 3)
  have he0 : 0 <= Ce := pairedDirichletEvenRemainderConstant_nonneg N _
  have ho0 : 0 <= Co := pairedDirichletOddRemainderConstant_nonneg N _
  have hC0 : 0 <= C := add_nonneg he0 ho0
  have hLog3 : 0 < Real.log (3 : Real) := Real.log_pos (by norm_num)
  have hA0 : 0 <= A := by dsimp only [A]; positivity
  refine Exists.intro A (And.intro hA0 ?_)
  intro x hx
  have hxPos : 0 < x := by linarith
  have hxLog : 0 < Real.log x := Real.log_pos (by linarith)
  have hLog : Real.log 3 <= Real.log x := Real.log_le_log (by norm_num) hx
  have hDen : 0 < 2 * Real.log x + 1 := by positivity
  have hFactorNonneg : 0 <= 1 + 1 / (2 * Real.log x + 1) := by positivity
  have hFactor : 1 + 1 / (2 * Real.log x + 1) <= 2 := by
    have hInv := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1)
      (show 1 <= 2 * Real.log x + 1 by linarith)
    norm_num only [one_div_one] at hInv
    linarith
  have hCoefficient (D : Real) (hD0 : 0 <= D) (hDC : D <= C) :
      (1 + 1 / (2 * Real.log x + 1)) * (2 + D / Real.log x) <= A := by
    have hFirst := div_le_div_of_nonneg_left hD0 hLog3 hLog
    have hSecond := div_le_div_of_nonneg_right hDC hLog3.le
    exact mul_le_mul hFactor (by linarith)
      (by positivity) (by norm_num)
  have hZeroScale :
      pairedDirichletZeroMass chi * quadraticRobinZeroKernelScale 1 x =
        pairedDirichletZeroMass chi / (Real.sqrt x * Real.log x) *
          (1 + 1 / Real.log x + 4 / (Real.log x) ^ 2) := by
    rw [quadraticRobinZeroKernelScale_one_eq, quadraticCriticalKernelBase_eq hxPos.le]
    unfold quadraticRobinZeroKernelCorrection
    ring
  cases chi.even_or_odd with
  | inl hEven =>
    have hEstimate := norm_pairedDirichletWeightedIntegral_one_even_le
      hchi hPrimitive hEven hERH hx
    rw [<- hZeroScale] at hEstimate
    apply hEstimate.trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (hCoefficient Ce he0 (by dsimp only [C]; linarith)) (by positivity))
  | inr hOdd =>
    have hEstimate := norm_pairedDirichletWeightedIntegral_one_odd_le
      hchi hPrimitive hOdd hERH hx
    rw [<- hZeroScale] at hEstimate
    have hCoefficientOdd :
        (1 + 1 / (2 * Real.log x + 1)) * (Co / Real.log x) <= A :=
      (mul_le_mul_of_nonneg_left
        (show Co / Real.log x <= 2 + Co / Real.log x by linarith) hFactorNonneg).trans
          (hCoefficient Co ho0 (by dsimp only [C]; linarith))
    exact hEstimate.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hCoefficientOdd (by positivity)))

/-- The critical paired Chebyshev-integral bound used for the Dirichlet ERH
criterion. Its converse is a separate analytic theorem. -/
def PairedDirichletCriticalBound
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    Filter.Eventually (fun x : Real =>
      norm (pairedDirichletWeightedIntegral chi 1 x) <=
        (pairedDirichletZeroMass chi + epsilon) / (Real.sqrt x * Real.log x)) Filter.atTop

/-- ERH implies the critical paired arithmetic bound for every nonprincipal
primitive character, with either parity and no extra analytic input. -/
theorem pairedDirichletCriticalBound_of_dirichletERH
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) : PairedDirichletCriticalBound chi := by
  intro epsilon hEpsilon
  choose A hA hEstimate using
    exists_pairedDirichletWeightedIntegral_reciprocal_remainder hchi hPrimitive hERH
  let M := pairedDirichletZeroMass chi
  have hM : 0 <= M := by
    dsimp only [M, pairedDirichletZeroMass]
    exact tsum_nonneg (fun _ => sq_nonneg _)
  let delta := epsilon / (2 * (M + 1))
  let eta := epsilon / (2 * (A + 1))
  have hDelta : 0 < delta := by dsimp only [delta]; positivity
  have hEta : 0 < eta := by dsimp only [eta]; positivity
  have hCoefficient (a : Real) (ha : 0 <= a) :
      a * (epsilon / (2 * (a + 1))) <= epsilon / 2 := by
    calc
      _ <= (a + 1) * (epsilon / (2 * (a + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp
  have hMDelta : M * delta <= epsilon / 2 := hCoefficient M hM
  have hAEta : A * eta <= epsilon / 2 := hCoefficient A hA
  have hScale := eventually_quadraticRobinZeroKernelScale_one_le hDelta
  have hSmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).bound hEta
  filter_upwards [hScale, hSmall, Filter.eventually_ge_atTop (3 : Real)] with x hScale hSmall hx
  have hxPos : 0 < x := by linarith
  have hxOne : 1 < x := by linarith
  have hLogPos := Real.log_pos hxOne
  have hSqrtPos := Real.sqrt_pos.2 hxPos
  have hDenPos : 0 < Real.sqrt x * Real.log x := mul_pos hSqrtPos hLogPos
  have hBaseNonneg : 0 <= x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) := by positivity
  have hZeroBound :
      M * quadraticRobinZeroKernelScale 1 x <=
        (M + epsilon / 2) / (Real.sqrt x * Real.log x) := by
    calc
      _ <= M * ((1 + delta) * (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x))) :=
        mul_le_mul_of_nonneg_left hScale hM
      _ = (M * (1 + delta)) * (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) := by ring
      _ <= (M + epsilon / 2) * (x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hMDelta]) hBaseNonneg
      _ = _ := by rw [quadraticCriticalKernelBase_eq hxPos.le]; ring
  have hLog : Real.log x <= eta * Real.sqrt x := by
    have hRpowPos : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hxPos _
    simpa only [Real.norm_eq_abs, abs_of_pos hLogPos, abs_of_pos hRpowPos,
      Real.sqrt_eq_rpow] using hSmall
  have hScaled : A * Real.log x <= (epsilon / 2) * Real.sqrt x := by
    calc
      _ <= A * (eta * Real.sqrt x) := mul_le_mul_of_nonneg_left hLog hA
      _ = (A * eta) * Real.sqrt x := by ring
      _ <= _ := mul_le_mul_of_nonneg_right hAEta (Real.sqrt_nonneg x)
  have hKey : (A * x ^ (-(1 : Real))) * (Real.sqrt x * Real.log x) <= epsilon / 2 := by
    calc
      _ = (A * Real.log x) * (Real.sqrt x / x) := by rw [Real.rpow_neg_one]; ring
      _ <= ((epsilon / 2) * Real.sqrt x) * (Real.sqrt x / x) :=
        mul_le_mul_of_nonneg_right hScaled (by positivity)
      _ = epsilon / 2 := by
        rw [div_eq_mul_inv]
        calc
          _ = (epsilon / 2) * (Real.sqrt x * Real.sqrt x) * Inv.inv x := by ring
          _ = (epsilon / 2) * x * Inv.inv x := by rw [Real.mul_self_sqrt hxPos.le]
          _ = _ := by field_simp [hxPos.ne']
  have hRemainderBound : A * x ^ (-(1 : Real)) <=
      (epsilon / 2) / (Real.sqrt x * Real.log x) := by
    calc
      _ = ((A * x ^ (-(1 : Real))) * (Real.sqrt x * Real.log x)) /
          (Real.sqrt x * Real.log x) := by field_simp [hDenPos.ne']
      _ <= _ := div_le_div_of_nonneg_right hKey hDenPos.le
  calc
    norm (pairedDirichletWeightedIntegral chi 1 x) <=
        M * quadraticRobinZeroKernelScale 1 x + A * x ^ (-(1 : Real)) := hEstimate x hx
    _ <= (M + epsilon / 2) / (Real.sqrt x * Real.log x) +
        (epsilon / 2) / (Real.sqrt x * Real.log x) := add_le_add hZeroBound hRemainderBound
    _ = _ := by dsimp only [M]; ring

end

end RobinBV.NumberField
