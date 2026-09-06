import RobinBV.NumberField.Proof.ZeroSeriesSecondMoment

/-!
# Complete covariance of actual character zero families

Every cross-family, multiplicity and scaled-frequency collision remains.
No disjointness or linear independence of zero ordinates is assumed.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter
open scoped Classical

noncomputable section

/-- Complete actual covariance mass for two canonical zero families on
possibly different fixed power clocks. Each divisor-index copy participates. -/
def rootCharacterZeroCovariance {N M : Nat} [NeZero N] [NeZero M]
    (chi : DirichletCharacter Complex N) (eta : DirichletCharacter Complex M)
    (k l m n : Nat) : Complex := by
  letI : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  letI : NeZero eta.conductor := NeZero.mk eta.conductor_ne_zero
  let cross : {I J : Type} -> (I -> Complex) -> (J -> Complex) -> Complex :=
    fun {I J} rho tau => tsum (fun p : Prod I J =>
      if (m : Real)*(rho p.1).im/(k : Real)=(n : Real)*(tau p.2).im/(l : Real) then
        ((k : Complex)/(rho p.1*((k : Complex)-rho p.1))) *
          star ((l : Complex)/(tau p.2*((l : Complex)-tau p.2))) else 0)
  exact if chi=1 then
    if eta=1 then cross riemannXiDivisorZeroValue riemannXiDivisorZeroValue
    else cross riemannXiDivisorZeroValue
      (fun p : QuadraticLZeroIndex eta.primitiveCharacter => quadraticLZeroValue p)
  else if eta=1 then
    cross (fun p : QuadraticLZeroIndex chi.primitiveCharacter => quadraticLZeroValue p)
      riemannXiDivisorZeroValue
  else cross
    (fun p : QuadraticLZeroIndex chi.primitiveCharacter => quadraticLZeroValue p)
    (fun p : QuadraticLZeroIndex eta.primitiveCharacter => quadraticLZeroValue p)

/-- Exact complete covariance of any two actual root zero series under
their respective ERH hypotheses, including unrelated positive moduli. -/
theorem rootCharacterZeroSeries_power_covariance_tendsto
    {N M : Nat} [NeZero N] [NeZero M]
    (chi : DirichletCharacter Complex N) (eta : DirichletCharacter Complex M)
    (hChiERH : DirichletERH chi) (hEtaERH : DirichletERH eta)
    {k l : Nat} (hk : 2 <= k) (hl : 2 <= l) (m n : Nat) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      rootCharacterZeroSeries chi k ((Nat.floor (Real.exp t) : Real)^m) *
        star (rootCharacterZeroSeries eta l ((Nat.floor (Real.exp t) : Real)^n))))
      atTop (nhds (rootCharacterZeroCovariance chi eta k l m n)) := by
  have hData {I : Type} (rho : I -> Complex)
      (hRe : forall i, (rho i).re=(1/2 : Real))
      (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2))
      {j : Nat} (hj : 1 <= j) :
      And (Countable I) (Summable (fun i => norm ((j : Complex)/(rho i*((j : Complex)-rho i))))) := by
    have hRho (i : I) : Not (rho i=0) := by
      intro h
      have hi := hRe i
      simp [h] at hi
    have hjR : (1 : Real) <= j := by exact_mod_cast hj
    exact And.intro (Complex.countable_of_summable_inv_norm_sq rho hRho hWeight)
      (by simpa only [Complex.ofReal_natCast] using
        (Complex.summable_real_div_mul_sub_of_re_eq_half rho hRe hWeight hjR).norm)
  have hRoot {I J : Type} (rho : I -> Complex) (tau : J -> Complex)
      (hRe : forall i, (rho i).re=(1/2 : Real))
      (hReTau : forall j, (tau j).re=(1/2 : Real))
      (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2))
      (hWeightTau : Summable (fun j => (Inv.inv (norm (tau j)))^2)) :
      Tendsto (Complex.intervalMean (fun t : Real =>
        (tsum (fun i => (k : Complex)/(rho i*((k : Complex)-rho i)) *
          ((((Nat.floor (Real.exp t) : Real)^m : Real) : Complex)^((rho i-1/2)/(k : Complex))))) *
        star (tsum (fun j => (l : Complex)/(tau j*((l : Complex)-tau j)) *
          ((((Nat.floor (Real.exp t) : Real)^n : Real) : Complex)^((tau j-1/2)/(l : Complex)))))))
        atTop (nhds (tsum (fun p : Prod I J =>
          if (m : Real)*(rho p.1).im/(k : Real)=(n : Real)*(tau p.2).im/(l : Real) then
            ((k : Complex)/(rho p.1*((k : Complex)-rho p.1))) *
              star ((l : Complex)/(tau p.2*((l : Complex)-tau p.2))) else 0))) := by
    have hRhoData := hData rho hRe hWeight (by omega : 1 <= k)
    have hTauData := hData tau hReTau hWeightTau (by omega : 1 <= l)
    let : Countable I := hRhoData.1
    let : Countable J := hTauData.1
    exact Complex.tendsto_criticalLinePowerSum_covariance rho
      (fun i => (k : Complex)/(rho i*((k : Complex)-rho i))) tau
      (fun j => (l : Complex)/(tau j*((l : Complex)-tau j)))
      hRe hReTau hRhoData.2 hTauData.2 k l m n
  by_cases hChi : chi=1
  next =>
    subst chi
    have hRH := (dirichletERH_principal_iff_riemannHypothesis (N := N)).1 hChiERH
    have hXiRe := Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH
    by_cases hEta : eta=1
    next =>
      subst eta
      simpa only [rootCharacterZeroSeries, rootCharacterZeroCovariance, ite_true] using
        hRoot riemannXiDivisorZeroValue riemannXiDivisorZeroValue
          hXiRe hXiRe Robin1984.summable_robinXiZeroWeight Robin1984.summable_robinXiZeroWeight
    next =>
      let : NeZero eta.conductor := NeZero.mk eta.conductor_ne_zero
      have hPrimitive := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one eta hEta
      have hERHPrimitive := (dirichletERH_iff_primitive eta hEta).1 hEtaERH
      simpa only [rootCharacterZeroSeries, rootCharacterZeroCovariance, ite_true, if_neg hEta] using
        hRoot riemannXiDivisorZeroValue
          (fun p : QuadraticLZeroIndex eta.primitiveCharacter => quadraticLZeroValue p)
          hXiRe
          (quadraticLZeroValue_re_eq_half_of_dirichletERH hPrimitive eta.primitiveCharacter_isPrimitive hERHPrimitive)
          Robin1984.summable_robinXiZeroWeight
          (summable_quadraticLZeroWeight hPrimitive eta.primitiveCharacter_isPrimitive)
  next =>
    let : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
    have hPrimitiveChi := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hChi
    have hERHPrimitiveChi := (dirichletERH_iff_primitive chi hChi).1 hChiERH
    have hChiRe := quadraticLZeroValue_re_eq_half_of_dirichletERH
      hPrimitiveChi chi.primitiveCharacter_isPrimitive hERHPrimitiveChi
    have hChiWeight := summable_quadraticLZeroWeight hPrimitiveChi chi.primitiveCharacter_isPrimitive
    by_cases hEta : eta=1
    next =>
      subst eta
      have hRH := (dirichletERH_principal_iff_riemannHypothesis (N := M)).1 hEtaERH
      simpa only [rootCharacterZeroSeries, rootCharacterZeroCovariance, if_neg hChi, ite_true] using
        hRoot (fun p : QuadraticLZeroIndex chi.primitiveCharacter => quadraticLZeroValue p)
          riemannXiDivisorZeroValue hChiRe
          (Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH)
          hChiWeight Robin1984.summable_robinXiZeroWeight
    next =>
      let : NeZero eta.conductor := NeZero.mk eta.conductor_ne_zero
      have hPrimitiveEta := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one eta hEta
      have hERHPrimitiveEta := (dirichletERH_iff_primitive eta hEta).1 hEtaERH
      simpa only [rootCharacterZeroSeries, rootCharacterZeroCovariance, if_neg hChi, if_neg hEta] using
        hRoot (fun p : QuadraticLZeroIndex chi.primitiveCharacter => quadraticLZeroValue p)
          (fun p : QuadraticLZeroIndex eta.primitiveCharacter => quadraticLZeroValue p)
          hChiRe
          (quadraticLZeroValue_re_eq_half_of_dirichletERH hPrimitiveEta eta.primitiveCharacter_isPrimitive hERHPrimitiveEta)
          hChiWeight (summable_quadraticLZeroWeight hPrimitiveEta eta.primitiveCharacter_isPrimitive)

end

end RobinBV.NumberField
