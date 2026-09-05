import RobinBV.NumberField.Proof.CharacterWeightedHigherRemainder
import RobinBV.NumberField.Proof.PairedDirichletCriticalBound

/-!
# Actual ERH weighted estimates at every higher exponent

The Hadamard constant is the actual completed-L logarithmic derivative,
not an additional analytic premise. The entire multiplicity-counted zero
sum and parity-dependent gamma remainder supply the higher-weight bound.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex Filter

noncomputable section

/-- Actual higher-weight estimate for every nonprincipal primitive even
character under its ERH, retaining the full logarithmic corrections. -/
theorem norm_primitiveCharacterWeightedIntegral_higher_even_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hChi : Not (chi = 1)) (hPrimitive : chi.IsPrimitive)
    (hEven : chi.Even) (hERH : DirichletERH chi)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 2 <= x) :
    norm (dirichletCharacterWeightedIntegral chi n x) <=
      quadraticLZeroMass chi * quadraticRobinZeroKernelScale n x +
        (x ^ (-(n : Real)) +
          (norm ((Real.log N : Complex) / 2 - logDeriv (symmetricCompletedLFunction chi) 0 -
              (Real.log Real.pi : Complex) / 2 - (Real.eulerMascheroniConstant : Complex) / 2) +
            2 * Real.log (2 * Real.pi) + Inv.inv (n : Real)) *
              (x ^ (-(n : Real)) * Inv.inv (Real.log x))) := by
  have hxOne : 1 < x := by linarith
  rw [<- primitiveCharacterPrimePowerSum_eq_weightedIntegral chi hn hxOne,
    primitiveCharacterPrimePowerSum_eq_even_explicit hChi hPrimitive hEven hERH
      (primitiveCharacter_endpoint_isHadamardConstant hChi hPrimitive) hn hxOne]
  have hZero := norm_tsum_primitiveL_robinZeroKernel_div_le
    hChi hPrimitive hERH (by omega : 1 <= n) hxOne
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa only [norm_neg] using hZero)
    (norm_primitiveCharacterEvenWeightedRemainder_le N _ hn hx))

/-- Actual higher-weight odd-character estimate. The entire nonzero-kernel
remainder keeps its extra logarithmic saving. -/
theorem norm_primitiveCharacterWeightedIntegral_higher_odd_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hChi : Not (chi = 1)) (hPrimitive : chi.IsPrimitive)
    (hOdd : chi.Odd) (hERH : DirichletERH chi)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 2 <= x) :
    norm (dirichletCharacterWeightedIntegral chi n x) <=
      quadraticLZeroMass chi * quadraticRobinZeroKernelScale n x +
        (norm ((Real.log N : Complex) / 2 - logDeriv (symmetricCompletedLFunction chi) 0 -
            (Real.log Real.pi : Complex) / 2 - (Real.eulerMascheroniConstant : Complex) / 2 +
              quadraticOddGammaConstant) + 1) *
          (x ^ (-(n : Real)) * Inv.inv (Real.log x)) := by
  have hxOne : 1 < x := by linarith
  rw [<- primitiveCharacterPrimePowerSum_eq_weightedIntegral chi hn hxOne,
    primitiveCharacterPrimePowerSum_eq_odd_explicit hChi hPrimitive hOdd hERH
      (primitiveCharacter_endpoint_isHadamardConstant hChi hPrimitive) hn hxOne]
  have hZero := norm_tsum_primitiveL_robinZeroKernel_div_le
    hChi hPrimitive hERH (by omega : 1 <= n) hxOne
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa only [norm_neg] using hZero)
    (norm_primitiveCharacterOddWeightedRemainder_le N _ (by omega) hx))

/-- A fixed constant bounds the complete nonzero-kernel remainder at
every higher exponent. The constant is derived from the actual parity
formulas; it is not a new analytic input. -/
theorem exists_primitiveCharacterWeightedIntegral_higher_remainder
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hChi : Not (chi = 1)) (hPrimitive : chi.IsPrimitive) (hERH : DirichletERH chi)
    {n : Nat} (hn : 2 <= n) :
    exists A : Real, And (0 <= A) (forall x : Real, 3 <= x ->
      norm (dirichletCharacterWeightedIntegral chi n x) <=
        quadraticLZeroMass chi * quadraticRobinZeroKernelScale n x + A * x ^ (-(n : Real))) := by
  let B : Complex := logDeriv (symmetricCompletedLFunction chi) 0
  let Ce : Real := norm ((Real.log N : Complex) / 2 - B - (Real.log Real.pi : Complex) / 2 -
    (Real.eulerMascheroniConstant : Complex) / 2) + 2 * Real.log (2 * Real.pi) + Inv.inv (n : Real)
  let Co : Real := norm ((Real.log N : Complex) / 2 - B - (Real.log Real.pi : Complex) / 2 -
    (Real.eulerMascheroniConstant : Complex) / 2 + quadraticOddGammaConstant) + 1
  let C : Real := Ce + Co
  let A : Real := 1 + C * Inv.inv (Real.log 3)
  have hLogPi : 0 <= Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hCe : 0 <= Ce := by dsimp only [Ce]; positivity
  have hCo : 0 <= Co := by dsimp only [Co]; positivity
  have hC : 0 <= C := add_nonneg hCe hCo
  have hLog3 : 0 < Real.log (3 : Real) := Real.log_pos (by norm_num)
  have hA : 0 <= A := by dsimp only [A]; positivity
  refine Exists.intro A (And.intro hA ?_)
  intro x hx
  have hxPos : 0 < x := by linarith
  have hPower : 0 <= x ^ (-(n : Real)) := Real.rpow_nonneg hxPos.le _
  have hInvLog : Inv.inv (Real.log x) <= Inv.inv (Real.log 3) := by
    simpa only [one_div] using one_div_le_one_div_of_le hLog3 (Real.log_le_log (by norm_num) hx)
  have hRem (D : Real) (hD : 0 <= D) (hDC : D <= C) :
      D * (x ^ (-(n : Real)) * Inv.inv (Real.log x)) <=
        (C * Inv.inv (Real.log 3)) * x ^ (-(n : Real)) := by
    calc
      _ = (D * Inv.inv (Real.log x)) * x ^ (-(n : Real)) := by ring
      _ <= (D * Inv.inv (Real.log 3)) * x ^ (-(n : Real)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hInvLog hD) hPower
      _ <= _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDC (inv_pos.mpr hLog3).le) hPower
  cases chi.even_or_odd with
  | inl hEven =>
    have hEstimate := norm_primitiveCharacterWeightedIntegral_higher_even_le
      hChi hPrimitive hEven hERH hn (by linarith : 2 <= x)
    have hSmall := hRem Ce hCe (by dsimp only [C]; linarith)
    apply hEstimate.trans
    apply add_le_add le_rfl
    change x ^ (-(n : Real)) + Ce * (x ^ (-(n : Real)) * Inv.inv (Real.log x)) <= _
    calc
      _ <= x ^ (-(n : Real)) + (C * Inv.inv (Real.log 3)) * x ^ (-(n : Real)) :=
        add_le_add le_rfl hSmall
      _ = _ := by dsimp only [A]; ring
  | inr hOdd =>
    have hEstimate := norm_primitiveCharacterWeightedIntegral_higher_odd_le
      hChi hPrimitive hOdd hERH hn (by linarith : 2 <= x)
    have hSmall := hRem Co hCo (by dsimp only [C]; linarith)
    apply hEstimate.trans
    apply add_le_add le_rfl
    change Co * (x ^ (-(n : Real)) * Inv.inv (Real.log x)) <= _
    calc
      _ <= (C * Inv.inv (Real.log 3)) * x ^ (-(n : Real)) := hSmall
      _ <= _ := by dsimp only [A]; nlinarith

private theorem higherKernelScale_scaled_tendsto
    {n : Nat} (hn : 1 <= n) {s : Real} (hs : 1 / 2 < s) :
    Tendsto (fun x : Real => (x ^ ((n : Real) - s) * Real.log x) *
      quadraticRobinZeroKernelScale n x) atTop (nhds (0 : Real)) := by
  have hInv : Tendsto (fun x : Real => Inv.inv (Real.log x)) atTop (nhds (0 : Real)) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hCoefficient : Tendsto (fun x : Real => (n : Real) + Inv.inv (Real.log x) +
      (2 / ((n : Real) - 1 / 2)) * Inv.inv (Real.log x) ^ 2) atTop (nhds (n : Real)) := by
    convert (hInv.const_add (n : Real)).add ((hInv.pow 2).const_mul (2 / ((n : Real) - 1 / 2))) using 1
    norm_num
  have hPower : Tendsto (fun x : Real => x ^ ((1 / 2 : Real) - s)) atTop (nhds (0 : Real)) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hs)
  have h := hPower.mul hCoefficient
  rw [zero_mul] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : Real)] with x hx
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLog := (Real.log_pos hx).ne'
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn
  have hDen : Not ((1 / 2 : Real) - (n : Real) = 0) := by linarith
  have hPowers : x ^ ((n : Real) - s) * x ^ ((1 / 2 : Real) - (n : Real)) =
      x ^ ((1 / 2 : Real) - s) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  symm
  calc
    _ = (x ^ ((n : Real) - s) * x ^ ((1 / 2 : Real) - (n : Real))) *
        ((n : Real) + Inv.inv (Real.log x) +
          (2 / ((n : Real) - 1 / 2)) * Inv.inv (Real.log x) ^ 2) := by
      unfold quadraticRobinZeroKernelScale
      simp only [show (1 / 2 : Real) - (n : Real) = -((n : Real) - 1 / 2) by ring,
        neg_div_neg_eq]
      field_simp [hLog, show Not ((n : Real) - 1 / 2 = 0) by linarith]
      ring
    _ = _ := by rw [hPowers]

/-- ERH gives a complete power-saving higher-weight integral estimate
above every exponent s>1/2, for every nonprincipal primitive complex
character and either parity. No pointwise Chebyshev bound is assumed. -/
theorem primitiveCharacterWeightedIntegral_higher_scaled_tendsto
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hChi : Not (chi = 1)) (hPrimitive : chi.IsPrimitive) (hERH : DirichletERH chi)
    {n : Nat} (hn : 2 <= n) {s : Real} (hs : 1 / 2 < s) :
    Tendsto (fun x : Real => ((x ^ ((n : Real) - s) * Real.log x : Real) : Complex) *
      dirichletCharacterWeightedIntegral chi n x) atTop (nhds (0 : Complex)) := by
  choose A hA hEstimate using exists_primitiveCharacterWeightedIntegral_higher_remainder
    hChi hPrimitive hERH hn
  have hsPos : 0 < s := by linarith
  have hLogPower : Tendsto (fun x : Real => x ^ (-s) * Real.log x) atTop (nhds (0 : Real)) := by
    have h := (isLittleO_log_rpow_atTop hsPos).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    rw [Real.rpow_neg hx.le]
    ring
  have hUpper : Tendsto (fun x : Real => quadraticLZeroMass chi *
      ((x ^ ((n : Real) - s) * Real.log x) * quadraticRobinZeroKernelScale n x) +
        A * (x ^ (-s) * Real.log x)) atTop (nhds (0 : Real)) := by
    have h := ((higherKernelScale_scaled_tendsto (by omega : 1 <= n) hs).const_mul
      (quadraticLZeroMass chi)).add (hLogPower.const_mul A)
    simpa only [mul_zero, add_zero] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_ge_atTop (3 : Real)] with x hx
  have hxOne : 1 < x := by linarith
  have hxPos : 0 < x := by linarith
  have hScale : 0 <= x ^ ((n : Real) - s) * Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_pos hxOne).le
  have hPowers : x ^ ((n : Real) - s) * x ^ (-(n : Real)) = x ^ (-s) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale]
  calc
    _ <= (x ^ ((n : Real) - s) * Real.log x) *
        (quadraticLZeroMass chi * quadraticRobinZeroKernelScale n x + A * x ^ (-(n : Real))) :=
      mul_le_mul_of_nonneg_left (hEstimate x hx) hScale
    _ = quadraticLZeroMass chi *
        ((x ^ ((n : Real) - s) * Real.log x) * quadraticRobinZeroKernelScale n x) +
          A * ((x ^ ((n : Real) - s) * x ^ (-(n : Real))) * Real.log x) := by ring
    _ = _ := by rw [hPowers]

end

end RobinBV.NumberField
