import RobinBV.NumberField.Proof.DirichletZeroLeadingExpansion
import RobinBV.NumberField.Proof.PrincipalCharacterZeros
import RobinBV.NumberField.Proof.PrincipalRootPrimeERH
import RobinBV.NumberField.Proof.RiemannZeroLeadingExpansion
import RobinBV.NumberField.Proof.RootCharacterConductorDecay

/-!
# Actual complete root-character zero expansion

Principal characters use the actual xi divisor, and nonprincipal
characters use the canonical primitive completed-L divisor. Full parity,
trivial and conductor corrections vanish at the selected root scale.
Every complex phase and multiplicity remains in the leading series.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- Canonical complete root zero series: zeta for principal characters,
and the actual primitive completed-L divisor otherwise. Central zeros
are included and no assertion of zero mean is part of this definition. -/
def rootCharacterZeroSeries
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (k : Nat) (x : Real) : Complex :=
  letI : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  if chi = 1 then
    tsum (fun p : RiemannXiDivisorZeroIndex =>
      (k : Complex) / (riemannXiDivisorZeroValue p * ((k : Complex) - riemannXiDivisorZeroValue p)) *
        (x : Complex) ^ ((riemannXiDivisorZeroValue p - 1 / 2) / (k : Complex)))
  else
    tsum (fun p : QuadraticLZeroIndex chi.primitiveCharacter =>
      (k : Complex) / (quadraticLZeroValue p * ((k : Complex) - quadraticLZeroValue p)) *
        (x : Complex) ^ ((quadraticLZeroValue p - 1 / 2) / (k : Complex)))

/-- Actual primitive nonprincipal root arithmetic equals the negative
complete root zero series up to a vanishing critical-root error. -/
theorem primitiveRootCharacterChebyshevTail_add_zeroSeries_tendsto
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hChi : Not (chi = 1)) (hPrimitive : chi.IsPrimitive) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) :
    Tendsto (fun x : Real =>
      ((x ^ (1 - Inv.inv ((2 * k : Nat) : Real)) * Real.log x : Real) : Complex) *
        rootCharacterChebyshevTail chi k x +
      tsum (fun p : QuadraticLZeroIndex chi =>
        (k : Complex) / (quadraticLZeroValue p * ((k : Complex) - quadraticLZeroValue p)) *
          (x : Complex) ^ ((quadraticLZeroValue p - 1 / 2) / (k : Complex))))
      atTop (nhds (0 : Complex)) := by
  have hkPos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hRoot : Tendsto (fun x : Real => x ^ (Inv.inv (k : Real))) atTop atTop :=
    tendsto_rpow_atTop (inv_pos.mpr hkPos)
  have h := (primitiveDirichletWeightedIntegral_add_leadingZeroSeries_scaled_tendsto hChi hPrimitive hERH hk).comp hRoot
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : Real)] with x hx
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hPower : (x ^ (Inv.inv (k : Real))) ^ ((k : Real) - 1 / 2) =
      x ^ (1 - Inv.inv ((2 * k : Nat) : Real)) := by
    rw [<- Real.rpow_mul hxPos.le]
    congr 1
    push_cast
    field_simp [hkPos.ne']
  dsimp only [Function.comp_def]
  rw [rootCharacterChebyshevTail_eq_higherIntegral chi (by omega) hx,
    <- zeroKernelLeadingSum_root_scaled_eq (fun p : QuadraticLZeroIndex chi => quadraticLZeroValue p) k (by omega) hx,
    hPower, Real.log_rpow hxPos]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- The primitive principal root tail minus its entire model equals
the negative complete zeta root zero series up to vanishing error. -/
theorem primitivePrincipalRootChebyshevTail_add_zeroSeries_tendsto
    {N : Nat} [NeZero N] (hRH : RiemannHypothesis) {k : Nat} (hk : 2 <= k) :
    Tendsto (fun x : Real =>
      ((x ^ (1 - Inv.inv ((2 * k : Nat) : Real)) * Real.log x : Real) : Complex) *
        (rootCharacterChebyshevTail (1 : DirichletCharacter Complex N).primitiveCharacter k x -
          ((integral (volume.restrict (Ioi x)) (fun t : Real =>
            t ^ (Inv.inv (k : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex)) +
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        (k : Complex) / (riemannXiDivisorZeroValue p * ((k : Complex) - riemannXiDivisorZeroValue p)) *
          (x : Complex) ^ ((riemannXiDivisorZeroValue p - 1 / 2) / (k : Complex))))
      atTop (nhds (0 : Complex)) := by
  have hkPos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hRoot : Tendsto (fun x : Real => x ^ (Inv.inv (k : Real))) atTop atTop :=
    tendsto_rpow_atTop (inv_pos.mpr hkPos)
  have h := (riemannWeightedIntegral_add_leadingZeroSeries_scaled_tendsto hRH (by omega : 1 <= k)).comp hRoot
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : Real)] with x hx
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hPower : (x ^ (Inv.inv (k : Real))) ^ ((k : Real) - 1 / 2) =
      x ^ (1 - Inv.inv ((2 * k : Nat) : Real)) := by
    rw [<- Real.rpow_mul hxPos.le]
    congr 1
    push_cast
    field_simp [hkPos.ne']
  dsimp only [Function.comp_def]
  rw [primitivePrincipalRootChebyshevTail_sub_model hk hx,
    <- zeroKernelLeadingSum_root_scaled_eq riemannXiDivisorZeroValue k (by omega) hx,
    hPower, Real.log_rpow hxPos]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- For every positive-modulus character, actual ERH gives the complete
canonical root zero expansion. All principal, parity and imprimitive
cases use proved arithmetic providers and retain every zero multiplicity. -/
theorem rootCharacterChebyshevTail_centered_add_zeroSeries_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) :
    Tendsto (fun x : Real =>
      ((x ^ (1 - Inv.inv ((2 * k : Nat) : Real)) * Real.log x : Real) : Complex) *
        (rootCharacterChebyshevTail chi k x - (if chi = 1 then (1 : Complex) else 0) *
          ((integral (volume.restrict (Ioi x)) (fun t : Real =>
            t ^ (Inv.inv (k : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex)) +
        rootCharacterZeroSeries chi k x) atTop (nhds (0 : Complex)) := by
  have hs : 0 < Inv.inv ((2 * k : Nat) : Real) := by positivity
  have hConductor := rootCharacterChebyshevTail_sub_primitive_scaled_tendsto chi k hk hs
  by_cases hChi : chi = 1
  next =>
    subst chi
    have hRH := (dirichletERH_principal_iff_riemannHypothesis (N := N)).1 hERH
    have h := (primitivePrincipalRootChebyshevTail_add_zeroSeries_tendsto (N := N) hRH hk).add hConductor
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [] with x
    simp only [rootCharacterZeroSeries, ite_true, one_mul]
    ring
  next =>
    let : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
    have hPrimitive := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hChi
    have hERHPrimitive := (dirichletERH_iff_primitive chi hChi).1 hERH
    have h := (primitiveRootCharacterChebyshevTail_add_zeroSeries_tendsto
      hPrimitive chi.primitiveCharacter_isPrimitive hERHPrimitive hk).add hConductor
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [] with x
    simp only [rootCharacterZeroSeries, if_neg hChi, zero_mul, sub_zero]
    ring

end

end RobinBV.NumberField
