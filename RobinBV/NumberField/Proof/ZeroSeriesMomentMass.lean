import RobinBV.NumberField.Proof.DirichletShiftedZeroMass
import RobinBV.NumberField.Proof.RiemannShiftedZeroMass
import RobinBV.NumberField.Proof.ZeroSeriesSecondMoment

/-!
# Evaluated complete second moments with repeated-zero correction

The diagonal is evaluated by the actual completed logarithmic derivative.
The full nonnegative repeated-index mass remains explicit. No simple-zero
hypothesis is imposed.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex BombieriVinogradov.SiegelWalfisz
open scoped Classical

noncomputable section

private theorem criticalRootSeries_moment_mass {I : Type*} (rho : I -> Complex)
    (hRe : forall i, (rho i).re=1/2)
    (hZ : Summable (fun i => (Inv.inv (norm (rho i)))^2))
    {k : Nat} (hk : 2 <= k) :
    tsum (fun p : Prod I I => if rho p.1=rho p.2 then
      ((k : Complex)/(rho p.1*((k : Complex)-rho p.1))) *
        star ((k : Complex)/(rho p.2*((k : Complex)-rho p.2))) else 0) =
      (((k : Real)/((k : Real)-1) *
        (tsum (fun i => (Inv.inv (norm (rho i)))^2) -
          tsum (fun i => (Inv.inv (norm ((k : Complex)-rho i)))^2)) +
        Complex.pointRepeatMass rho (fun z => (k : Complex)/(z*((k : Complex)-z))) : Real) : Complex) := by
  let c : Complex -> Complex := fun z => (k : Complex)/(z*((k : Complex)-z))
  have hkR : (1 : Real) < k := by exact_mod_cast (by omega : 1 < k)
  have hC : Summable (fun i => norm (c (rho i))) := by
    simpa only [c, Complex.ofReal_natCast] using
      (Complex.summable_real_div_mul_sub_of_re_eq_half rho hRe hZ hkR.le).norm
  have hDiag : tsum (fun i => norm (c (rho i))^2) =
      (k : Real)/((k : Real)-1) *
        (tsum (fun i => (Inv.inv (norm (rho i)))^2) -
          tsum (fun i => (Inv.inv (norm ((k : Complex)-rho i)))^2)) := by
    simpa only [c, Complex.ofReal_natCast] using
      Complex.tsum_norm_real_div_mul_sub_sq_eq_of_re_eq_half rho hRe hZ hkR
  change tsum (fun p : Prod I I => if rho p.1=rho p.2 then c (rho p.1)*star (c (rho p.2)) else 0) = _
  rw [Complex.tsum_equalPoint_mul_star_eq_mass rho c,
    Complex.pointCollisionMass_eq_diagonal_add_repeat rho c hC, hDiag]

/-- Actual completed logarithmic derivative: xi in the principal case,
and the symmetric primitive completion otherwise. -/
def rootCharacterCompletedLogDeriv {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (z : Complex) : Complex := by
  letI : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  exact if chi=1 then logDeriv riemannXi z
    else logDeriv (symmetricCompletedLFunction chi.primitiveCharacter) z

/-- Actual full repeated-zero contribution to the root-series second moment. -/
def rootCharacterZeroRepeatMass {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (k : Nat) : Real := by
  letI : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  let c : Complex -> Complex := fun z => (k : Complex)/(z*((k : Complex)-z))
  exact if chi=1 then Complex.pointRepeatMass riemannXiDivisorZeroValue c
    else Complex.pointRepeatMass (fun p : QuadraticLZeroIndex chi.primitiveCharacter => quadraticLZeroValue p) c

/-- Repeated canonical zeros can only increase the full second-moment mass. -/
theorem rootCharacterZeroRepeatMass_nonneg {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (k : Nat) :
    0 <= rootCharacterZeroRepeatMass chi k := by
  unfold rootCharacterZeroRepeatMass
  split_ifs <;> exact Complex.pointRepeatMass_nonneg _ _

/-- Exact completed-function evaluation of the full canonical second moment.
The entire nonnegative repeated-zero correction is retained. -/
theorem rootCharacterZeroSecondMoment_eq_logDeriv_add_repeat
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) :
    rootCharacterZeroSecondMoment chi k =
      (((k : Real)/((k : Real)-1) *
        (-2*(rootCharacterCompletedLogDeriv chi 0).re -
          (rootCharacterCompletedLogDeriv chi (k : Complex)).re/((k : Real)-1/2)) +
        rootCharacterZeroRepeatMass chi k : Real) : Complex) := by
  have hkR : (1 : Real) <= k := by exact_mod_cast (by omega : 1 <= k)
  by_cases hChi : chi=1
  next =>
    subst chi
    have hRH := (dirichletERH_principal_iff_riemannHypothesis (N := N)).1 hERH
    have h := criticalRootSeries_moment_mass riemannXiDivisorZeroValue
      (Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH)
      Robin1984.summable_robinXiZeroWeight hk
    have hZ : tsum (fun p : RiemannXiDivisorZeroIndex =>
        (Inv.inv (norm (riemannXiDivisorZeroValue p)))^2) =
        -2*(logDeriv riemannXi 0).re := by
      rw [Robin1984.robinXiZeroConstant_eq_of_riemannHypothesis hRH]
      have hEndpoint := congrArg Complex.re neg_two_mul_logDeriv_riemannXi_zero_eq
      norm_num at hEndpoint
      linarith
    have hM : tsum (fun p : RiemannXiDivisorZeroIndex =>
        (Inv.inv (norm ((k : Complex)-riemannXiDivisorZeroValue p)))^2) =
        (logDeriv riemannXi (k : Complex)).re/((k : Real)-1/2) := by
      simpa only [riemannShiftedZeroMass, Complex.ofReal_natCast] using
        riemann_shiftedZeroMass_eq_re_logDeriv hRH hkR
    rw [hZ, hM] at h
    simpa only [rootCharacterZeroSecondMoment, rootCharacterZeroRepeatMass,
      rootCharacterCompletedLogDeriv, ite_true] using h
  next =>
    let : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
    have hPrimitive := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hChi
    have hERHPrimitive := (dirichletERH_iff_primitive chi hChi).1 hERH
    have h := criticalRootSeries_moment_mass
      (fun p : QuadraticLZeroIndex chi.primitiveCharacter => quadraticLZeroValue p)
      (quadraticLZeroValue_re_eq_half_of_dirichletERH hPrimitive chi.primitiveCharacter_isPrimitive hERHPrimitive)
      (summable_quadraticLZeroWeight hPrimitive chi.primitiveCharacter_isPrimitive) hk
    have hZ : tsum (fun p : QuadraticLZeroIndex chi.primitiveCharacter =>
        (Inv.inv (norm (quadraticLZeroValue p)))^2) =
        -2*(logDeriv (symmetricCompletedLFunction chi.primitiveCharacter) 0).re := by
      simpa only [quadraticLZeroMass] using
        quadraticLZeroMass_eq_neg_two_mul_re_logDeriv_zero hPrimitive chi.primitiveCharacter_isPrimitive hERHPrimitive
    have hM : tsum (fun p : QuadraticLZeroIndex chi.primitiveCharacter =>
        (Inv.inv (norm ((k : Complex)-quadraticLZeroValue p)))^2) =
        (logDeriv (symmetricCompletedLFunction chi.primitiveCharacter) (k : Complex)).re/((k : Real)-1/2) := by
      simpa only [dirichletShiftedZeroMass, Complex.ofReal_natCast] using
        primitiveDirichlet_shiftedZeroMass_eq_re_logDeriv hPrimitive chi.primitiveCharacter_isPrimitive hERHPrimitive hkR
    rw [hZ, hM] at h
    simpa only [rootCharacterZeroSecondMoment, rootCharacterZeroRepeatMass,
      rootCharacterCompletedLogDeriv, if_neg hChi] using h

/-- The evaluated diagonal is a lower bound for the actual complete mass;
this does not require the canonical zeros to be simple. -/
theorem rootCharacterZeroSecondMoment_re_lower_bound
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) :
    (k : Real)/((k : Real)-1) *
      (-2*(rootCharacterCompletedLogDeriv chi 0).re -
        (rootCharacterCompletedLogDeriv chi (k : Complex)).re/((k : Real)-1/2)) <=
      (rootCharacterZeroSecondMoment chi k).re := by
  rw [rootCharacterZeroSecondMoment_eq_logDeriv_add_repeat chi hERH hk, Complex.ofReal_re]
  exact le_add_of_nonneg_right (rootCharacterZeroRepeatMass_nonneg chi k)

end

end RobinBV.NumberField
