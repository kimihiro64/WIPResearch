import RobinBV.Mathlib.Analysis.Complex.ShiftedInverseSquare
import RobinBV.Mathlib.Analysis.Fourier.ExponentialCovariance
import RobinBV.NumberField.Proof.RootCharacterZeroExpansion

/-!
# Complete second moments of the actual canonical root zero series

Every coincident zero pair is retained, so the diagonal is not substituted
for the full multiplicity-squared contribution.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter

noncomputable section

private theorem criticalRootSeries_data {I : Type*} (rho : I -> Complex)
    (hRe : forall i, (rho i).re=(1/2 : Real))
    (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2))
    {k : Nat} (hk : 1 <= k) :
    And (Countable I) (Summable (fun i => norm ((k : Complex)/(rho i*((k : Complex)-rho i))))) := by
  have hRho (i : I) : Not (rho i=0) := by
    intro h
    have hi := hRe i
    simp [h] at hi
  have hkR : (1 : Real) <= k := by exact_mod_cast hk
  exact And.intro (Complex.countable_of_summable_inv_norm_sq rho hRho hWeight)
    (by simpa only [Complex.ofReal_natCast] using
      (Complex.summable_real_div_mul_sub_of_re_eq_half rho hRe hWeight hkR).norm)

private theorem criticalRootSeries_secondMoment {I : Type*} (rho : I -> Complex)
    (hRe : forall i, (rho i).re=(1/2 : Real))
    (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2))
    {k m : Nat} (hk : 1 <= k) (hm : 1 <= m) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      (tsum (fun i => (k : Complex)/(rho i*((k : Complex)-rho i)) *
        ((((Nat.floor (Real.exp t) : Real)^m : Real) : Complex)^((rho i-1/2)/(k : Complex))))) *
      star (tsum (fun i => (k : Complex)/(rho i*((k : Complex)-rho i)) *
        ((((Nat.floor (Real.exp t) : Real)^m : Real) : Complex)^((rho i-1/2)/(k : Complex)))))))
      atTop (nhds (tsum (fun p : Prod I I => if rho p.1=rho p.2 then
        ((k : Complex)/(rho p.1*((k : Complex)-rho p.1))) *
          star ((k : Complex)/(rho p.2*((k : Complex)-rho p.2))) else 0))) := by
  have hData := criticalRootSeries_data rho hRe hWeight hk
  let : Countable I := hData.1
  exact Complex.tendsto_criticalLinePowerSum_secondMoment rho
    (fun i => (k : Complex)/(rho i*((k : Complex)-rho i))) hRe hData.2 hk hm

private theorem criticalRootSeries_norm_bound {I : Type*} (rho : I -> Complex)
    (hRe : forall i, (rho i).re=(1/2 : Real))
    (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2))
    {k : Nat} (hk : 1 <= k) :
    exists C : Real, And (0 <= C) (forall x : Real, 0 < x ->
      norm (tsum (fun i => (k : Complex)/(rho i*((k : Complex)-rho i)) *
        (x : Complex)^((rho i-1/2)/(k : Complex)))) <= C) := by
  let c : I -> Complex := fun i => (k : Complex)/(rho i*((k : Complex)-rho i))
  have hData := criticalRootSeries_data rho hRe hWeight hk
  refine Exists.intro (tsum (fun i => norm (c i))) (And.intro (tsum_nonneg (fun i => norm_nonneg _)) ?_)
  intro x hx
  simpa only [pow_one] using Complex.norm_criticalLinePowerSum_le rho c hRe hData.2 k 1 hx

/-- Complete equal-zero pair sum of the actual canonical family. Each copy
in the divisor index participates separately, retaining squared multiplicity. -/
def rootCharacterZeroSecondMoment {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (k : Nat) : Complex := by
  classical
  letI : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  let c : Complex -> Complex := fun z => (k : Complex)/(z*((k : Complex)-z))
  exact if chi=1 then tsum (fun p : Prod RiemannXiDivisorZeroIndex RiemannXiDivisorZeroIndex =>
    if riemannXiDivisorZeroValue p.1=riemannXiDivisorZeroValue p.2 then
      c (riemannXiDivisorZeroValue p.1)*star (c (riemannXiDivisorZeroValue p.2)) else 0)
  else tsum (fun p : Prod (QuadraticLZeroIndex chi.primitiveCharacter) (QuadraticLZeroIndex chi.primitiveCharacter) =>
    if quadraticLZeroValue p.1=quadraticLZeroValue p.2 then
      c (quadraticLZeroValue p.1)*star (c (quadraticLZeroValue p.2)) else 0)

/-- Exact logarithmic-floor second moment for every actual character root
zero series. Only ERH of this character is assumed. -/
theorem rootCharacterZeroSeries_power_secondMoment_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) (m : Nat) (hm : 1 <= m) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      rootCharacterZeroSeries chi k ((Nat.floor (Real.exp t) : Real)^m) *
        star (rootCharacterZeroSeries chi k ((Nat.floor (Real.exp t) : Real)^m))))
      atTop (nhds (rootCharacterZeroSecondMoment chi k)) := by
  by_cases hChi : chi=1
  next =>
    subst chi
    have hRH := (dirichletERH_principal_iff_riemannHypothesis (N := N)).1 hERH
    simpa only [rootCharacterZeroSeries, rootCharacterZeroSecondMoment, ite_true] using
      criticalRootSeries_secondMoment riemannXiDivisorZeroValue
        (Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH)
        Robin1984.summable_robinXiZeroWeight (by omega : 1 <= k) hm
  next =>
    let : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
    have hPrimitive := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hChi
    have hERHPrimitive := (dirichletERH_iff_primitive chi hChi).1 hERH
    simpa only [rootCharacterZeroSeries, rootCharacterZeroSecondMoment, if_neg hChi] using
      criticalRootSeries_secondMoment (fun p : QuadraticLZeroIndex chi.primitiveCharacter => quadraticLZeroValue p)
        (quadraticLZeroValue_re_eq_half_of_dirichletERH hPrimitive chi.primitiveCharacter_isPrimitive hERHPrimitive)
        (summable_quadraticLZeroWeight hPrimitive chi.primitiveCharacter_isPrimitive) (by omega : 1 <= k) hm

/-- Actual ERH supplies a uniform full-series bound on all positive inputs.
No bound is added to the arithmetic theorem as a separate hypothesis. -/
theorem exists_rootCharacterZeroSeries_norm_bound
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) :
    exists C : Real, And (0 <= C) (forall x : Real, 0 < x ->
      norm (rootCharacterZeroSeries chi k x) <= C) := by
  by_cases hChi : chi=1
  next =>
    subst chi
    have hRH := (dirichletERH_principal_iff_riemannHypothesis (N := N)).1 hERH
    simpa only [rootCharacterZeroSeries, ite_true] using
      criticalRootSeries_norm_bound riemannXiDivisorZeroValue
        (Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH)
        Robin1984.summable_robinXiZeroWeight (by omega : 1 <= k)
  next =>
    let : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
    have hPrimitive := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hChi
    have hERHPrimitive := (dirichletERH_iff_primitive chi hChi).1 hERH
    simpa only [rootCharacterZeroSeries, if_neg hChi] using
      criticalRootSeries_norm_bound (fun p : QuadraticLZeroIndex chi.primitiveCharacter => quadraticLZeroValue p)
        (quadraticLZeroValue_re_eq_half_of_dirichletERH hPrimitive chi.primitiveCharacter_isPrimitive hERHPrimitive)
        (summable_quadraticLZeroWeight hPrimitive chi.primitiveCharacter_isPrimitive) (by omega : 1 <= k)

end

end RobinBV.NumberField
