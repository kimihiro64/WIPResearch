import RobinBV.NumberField.Proof.CharacterRootPrimeERH
import RobinBV.NumberField.Proof.PrincipalCharacterEndpoint
import RobinBV.NumberField.Proof.RiemannHigherWeightDecay

/-!
# Principal root-prime model errors under RH

The primitive principal Chebyshev tail is the exact rational root tail.
The full rational RH estimate, psi-minus-theta correction and finite
conductor correction give the model-subtracted principal estimate.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set

noncomputable section

/-- The primitive principal root tail differs from its complete model
by exactly the pulled-back rational weighted error, with factor 1/k. -/
theorem primitivePrincipalRootChebyshevTail_sub_model
    {N : Nat} [NeZero N] {k : Nat} (hk : 2 <= k) {x : Real} (hx : 1 < x) :
    rootCharacterChebyshevTail (1 : DirichletCharacter Complex N).primitiveCharacter k x -
      ((integral (volume.restrict (Ioi x)) (fun t : Real =>
        t ^ (Inv.inv (k : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex) =
      ((Inv.inv (k : Real) *
        Robin1984.robinPsiWeightedErrorIntegral k (x ^ (Inv.inv (k : Real))) : Real) : Complex) := by
  have hPsi : rootCharacterChebyshevTail (1 : DirichletCharacter Complex N).primitiveCharacter k x =
      ((integral (volume.restrict (Ioi x)) (fun t : Real =>
        Chebyshev.psi (t ^ (Inv.inv (k : Real))) * Robin1984.robinRealWeight 1 t) : Real) : Complex) := by
    unfold rootCharacterChebyshevTail
    rw [<- integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [characterChebyshevSum_primitive_principal_eq_psi]
    simp only [Complex.ofReal_mul]
  rw [hPsi, Robin1984.integral_psi_root_mul_robinRealWeight_eq (by norm_num : 1 <= (1 : Nat)) hk hx,
    Robin1984.integral_rpow_mul_robinRealWeight 1 (Inv.inv (k : Real)) hx]
  simp only [Nat.mul_one, Complex.ofReal_add, Complex.ofReal_inv, add_sub_cancel_left]

/-- The complete model-subtracted primitive principal root Chebyshev
tail decays above the half-root exponent, using actual RH. -/
theorem primitivePrincipalRootChebyshevTail_centered_scaled_tendsto
    {N : Nat} [NeZero N] (hRH : RiemannHypothesis) {k : Nat} (hk : 2 <= k)
    {s : Real} (hs : 1 / 2 < (k : Real) * s) :
    Tendsto (fun x : Real => ((x ^ (1 - s) * Real.log x : Real) : Complex) *
      (rootCharacterChebyshevTail (1 : DirichletCharacter Complex N).primitiveCharacter k x -
        ((integral (volume.restrict (Ioi x)) (fun t : Real =>
          t ^ (Inv.inv (k : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex)))
      atTop (nhds (0 : Complex)) := by
  have hkPos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hRoot : Tendsto (fun x : Real => x ^ (Inv.inv (k : Real))) atTop atTop :=
    tendsto_rpow_atTop (inv_pos.mpr hkPos)
  have hReal := (riemannPsiWeightedErrorIntegral_scaled_tendsto hRH (by omega : 1 <= k) hs).comp hRoot
  have h := (Complex.continuous_ofReal.tendsto (0 : Real)).comp hReal
  simp only [Complex.ofReal_zero] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : Real)] with x hx
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hPower : (x ^ (Inv.inv (k : Real))) ^ ((k : Real) - (k : Real) * s) = x ^ (1 - s) := by
    rw [<- Real.rpow_mul hxPos.le]
    congr 1
    field_simp [hkPos.ne']
  dsimp only [Function.comp_def]
  rw [primitivePrincipalRootChebyshevTail_sub_model hk hx, hPower, Real.log_rpow hxPos]
  simp only [Complex.ofReal_mul]
  ring

/-- For every positive principal modulus, the full root-prime tail minus
its exact model decays under RH above the half-root exponent. All prime
powers and every finite excluded conductor prime are accounted for. -/
theorem principalRootPrimeCharacterTail_centered_scaled_tendsto
    {N : Nat} [NeZero N] (hRH : RiemannHypothesis) {k : Nat} (hk : 2 <= k)
    {s : Real} (hs : 1 / 2 < (k : Real) * s) :
    Tendsto (fun x : Real => ((x ^ (1 - s) * Real.log x : Real) : Complex) *
      (rootPrimeCharacterTail (1 : DirichletCharacter Complex N) (Inv.inv (k : Real)) x -
        ((integral (volume.restrict (Ioi x)) (fun t : Real =>
          t ^ (Inv.inv (k : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex)))
      atTop (nhds (0 : Complex)) := by
  have hkPos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hsPos : 0 < s := by nlinarith
  have hr : Inv.inv (k : Real) < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le
      (n := 1) (k := k) (by norm_num) hk
  have hPsi := primitivePrincipalRootChebyshevTail_centered_scaled_tendsto (N := N) hRH hk hs
  have hDifference := rootCharacterChebyshevTail_sub_prime_scaled_tendsto
    (1 : DirichletCharacter Complex N).primitiveCharacter k hk hs
  have hConductor := rootPrimeCharacterTail_sub_primitive_scaled_tendsto
    (1 : DirichletCharacter Complex N) hr hsPos
  have h := (hPsi.sub hDifference).add hConductor
  simp only [sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [] with x
  ring

end

end RobinBV.NumberField
