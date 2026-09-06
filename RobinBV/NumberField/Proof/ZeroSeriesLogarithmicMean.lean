import Robin1984.Mathlib.NumberTheory.LSeries.RiemannZetaReal
import RobinBV.Mathlib.Analysis.Complex.ShiftedInverseSquare
import RobinBV.Mathlib.Analysis.Fourier.ExponentialMean
import RobinBV.NumberField.Proof.RootCharacterZeroExpansion

/-!
# Exact logarithmic mean of the actual canonical root zero series

The mean retains the actual central multiplicity. All other frequencies
average out, with the full summable zero family and no frequency gap.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory

noncomputable section

private theorem criticalFamily_countable {I : Type*} (rho : I -> Complex)
    (hRe : forall i, (rho i).re = (1/2 : Real))
    (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2)) : Countable I := by
  have hSupport : Function.support (fun i => (Inv.inv (norm (rho i)))^2) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    have hRho : Not (rho i=0) := by
      intro h
      have hi := hRe i
      simp [h] at hi
    simp [Function.mem_support, hRho]
  have h := hWeight.countable_support
  rw [hSupport] at h
  exact Set.countable_univ_iff.mp h

private theorem centralFamily_finite {I : Type*} (rho : I -> Complex)
    (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2)) :
    Finite {i : I // rho i=(1/2 : Complex)} := by
  have hConstant : Summable (fun _i : {i : I // rho i=(1/2 : Complex)} => (4 : Real)) := by
    apply (hWeight.subtype (fun i => rho i=(1/2 : Complex))).congr
    intro i
    dsimp only [Function.comp_def]
    rw [i.property]
    norm_num
  exact Finite.of_summable_const (by norm_num : (0 : Real)<4) hConstant

private theorem rootPhase_exp_eq {rho : Complex} (hRe : rho.re=(1/2 : Real))
    (k : Nat) (t : Real) :
    ((Real.exp t : Real) : Complex)^((rho-(1/2 : Complex))/(k : Complex)) =
      Complex.exp (((rho.im/(k : Real) : Real) : Complex)*Complex.I*(t : Complex)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
    <- Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
  congr 1
  have hRho : rho-(1/2 : Complex)=(rho.im : Complex)*Complex.I := by
    apply Complex.ext
    next => simp [hRe]
    next => simp
  rw [hRho]
  push_cast
  ring

private theorem centralCoefficientSum {I : Type*} (rho : I -> Complex)
    (hRe : forall i, (rho i).re=(1/2 : Real))
    (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2))
    {k : Nat} (hk : 1 <= k) :
    tsum (fun i => if (rho i).im/(k : Real)=0 then
      (k : Complex)/(rho i*((k : Complex)-rho i)) else 0) =
      (2*(k : Complex)/((k : Complex)-1/2)) *
        (Nat.card {i : I // rho i=(1/2 : Complex)} : Complex) := by
  classical
  let S : Set I := {i | rho i=(1/2 : Complex)}
  let C : Complex := 2*(k : Complex)/((k : Complex)-1/2)
  have hkR : Not ((k : Real)=0) := by exact_mod_cast (by omega : Not (k=0))
  have hkLe : (1 : Real) <= k := by exact_mod_cast hk
  have hDen : Not ((k : Complex)-1/2=0) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  have hFunction : (fun i => if (rho i).im/(k : Real)=0 then
      (k : Complex)/(rho i*((k : Complex)-rho i)) else 0) = S.indicator (fun _ => C) := by
    funext i
    by_cases hi : rho i=(1/2 : Complex)
    next =>
      have hs : Membership.mem S i := hi
      rw [if_pos (by simp [hi]), Set.indicator_of_mem hs]
      rw [hi]
      dsimp only [C]
      field_simp [hDen]
    next =>
      have him : Not ((rho i).im=0) := by
        intro him
        apply hi
        apply Complex.ext
        next => simp [hRe i]
        next => simpa using him
      have hs : Not (Membership.mem S i) := hi
      rw [if_neg (div_ne_zero him hkR), Set.indicator_of_notMem hs]
  rw [hFunction, <- tsum_subtype]
  let : Finite S := centralFamily_finite rho hWeight
  let : Fintype S := Fintype.ofFinite S
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change (Fintype.card S : Complex)*C = C*(Nat.card S : Complex)
  rw [Nat.card_eq_fintype_card]
  ring

private theorem criticalRootSeries_mean {I : Type*} (rho : I -> Complex)
    (hRe : forall i, (rho i).re=(1/2 : Real))
    (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2))
    {k : Nat} (hk : 1 <= k) :
    Tendsto (fun T : Real => Inv.inv (T : Complex)*intervalIntegral
      (fun t : Real => tsum (fun i => (k : Complex)/(rho i*((k : Complex)-rho i))*
        ((Real.exp t : Real) : Complex)^((rho i-1/2)/(k : Complex)))) 0 T volume)
      atTop (nhds ((2*(k : Complex)/((k : Complex)-1/2))*
        (Nat.card {i : I // rho i=(1/2 : Complex)} : Complex))) := by
  let : Countable I := criticalFamily_countable rho hRe hWeight
  let c : I -> Complex := fun i => (k : Complex)/(rho i*((k : Complex)-rho i))
  let omega : I -> Real := fun i => (rho i).im/(k : Real)
  have hkR : (1 : Real) <= k := by exact_mod_cast hk
  have hC : Summable (fun i => norm (c i)) := by
    simpa only [c, Complex.ofReal_natCast] using
      (Complex.summable_real_div_mul_sub_of_re_eq_half rho hRe hWeight hkR).norm
  have h := Complex.tendsto_exponentialSeriesMean c omega hC
  have hCenter : tsum (fun i => if omega i=0 then c i else 0) =
      (2*(k : Complex)/((k : Complex)-1/2))*
        (Nat.card {i : I // rho i=(1/2 : Complex)} : Complex) :=
    centralCoefficientSum rho hRe hWeight hk
  rw [hCenter] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro T
  unfold Complex.exponentialSeriesMean Complex.intervalMean Complex.exponentialSeries
  congr 1
  apply intervalIntegral.integral_congr
  intro t _ht
  apply tsum_congr
  intro i
  dsimp only [c, omega]
  rw [rootPhase_exp_eq (hRe i)]

private theorem criticalRootSeries_power_logFloor_mean {I : Type*} (rho : I -> Complex)
    (hRe : forall i, (rho i).re=(1/2 : Real))
    (hWeight : Summable (fun i => (Inv.inv (norm (rho i)))^2))
    {k : Nat} (hk : 1 <= k) (m : Nat) (hm : 1 <= m) :
    Tendsto (Complex.intervalMean (fun t : Real => tsum (fun i =>
      (k : Complex)/(rho i*((k : Complex)-rho i))*
        ((((Nat.floor (Real.exp t) : Real)^m : Real) : Complex)^((rho i-1/2)/(k : Complex))))))
      atTop (nhds ((2*(k : Complex)/((k : Complex)-1/2))*
        (Nat.card {i : I // rho i=(1/2 : Complex)} : Complex))) := by
  let : Countable I := criticalFamily_countable rho hRe hWeight
  let c : I -> Complex := fun i => (k : Complex)/(rho i*((k : Complex)-rho i))
  let omega : I -> Real := fun i => (m : Real)*(rho i).im/(k : Real)
  have hkR : (1 : Real) <= k := by exact_mod_cast hk
  have hmR : Not ((m : Real)=0) := by exact_mod_cast (by omega : Not (m=0))
  have hC : Summable (fun i => norm (c i)) := by
    simpa only [c, Complex.ofReal_natCast] using
      (Complex.summable_real_div_mul_sub_of_re_eq_half rho hRe hWeight hkR).norm
  have h := Complex.tendsto_exponentialSeries_logFloorMean c omega hC
  have hCenter : tsum (fun i => if omega i=0 then c i else 0) =
      (2*(k : Complex)/((k : Complex)-1/2))*
        (Nat.card {i : I // rho i=(1/2 : Complex)} : Complex) := by
    simpa only [omega, c, mul_div_assoc, mul_eq_zero, hmR, false_or] using
      centralCoefficientSum rho hRe hWeight hk
  rw [hCenter] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with T hT
  unfold Complex.intervalMean
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have htI : Membership.mem (Set.Icc (0 : Real) T) t := by
    simpa only [Set.uIcc_of_le hT.le] using ht
  let P : Real := Nat.floor (Real.exp t)
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast (Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr htI.1))
  have hPow := pow_pos hP m
  unfold Complex.exponentialSeries
  apply tsum_congr
  intro i
  have hPhase : (((P^m : Real) : Complex)^((rho i-1/2)/(k : Complex))) =
      Complex.exp ((omega i : Complex)*Complex.I*(Real.log P : Complex)) := by
    calc
      _ = ((Real.exp (Real.log (P^m)) : Real) : Complex)^((rho i-1/2)/(k : Complex)) := by
        rw [Real.exp_log hPow]
      _ = Complex.exp ((((rho i).im/(k : Real) : Real) : Complex)*Complex.I*(Real.log (P^m) : Complex)) :=
        rootPhase_exp_eq (hRe i) k (Real.log (P^m))
      _ = _ := by
        rw [Real.log_pow]
        congr 1
        dsimp only [omega]
        push_cast
        ring
  change c i*Complex.exp ((omega i : Complex)*Complex.I*(Real.log P : Complex)) =
    c i*((P^m : Real) : Complex)^((rho i-1/2)/(k : Complex))
  rw [hPhase]

/-- Actual central multiplicity of the canonical primitive zero family;
principal characters use the actual xi divisor. -/
def rootCharacterCentralMultiplicity {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) : Nat := by
  classical
  letI : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  exact if chi=1 then Nat.card {p : RiemannXiDivisorZeroIndex //
    riemannXiDivisorZeroValue p=(1/2 : Complex)}
  else Nat.card {p : QuadraticLZeroIndex chi.primitiveCharacter //
    quadraticLZeroValue p=(1/2 : Complex)}

/-- The actual xi family has no central zero, unconditionally. -/
theorem rootCharacterCentralMultiplicity_principal_eq_zero
    (N : Nat) [NeZero N] :
    rootCharacterCentralMultiplicity (1 : DirichletCharacter Complex N)=0 := by
  have hEmpty : IsEmpty {p : RiemannXiDivisorZeroIndex //
      riemannXiDivisorZeroValue p=(1/2 : Complex)} := IsEmpty.mk (fun p => by
    have hXi := riemannXiDivisorZeroValue_eq_zero p.val
    rw [p.property] at hXi
    have hZeta := Robin1984.riemannZeta_eq_zero_of_riemannXi_eq_zero
      (by norm_num : Not ((1/2 : Complex)=0)) (by norm_num : Not ((1/2 : Complex)=1)) hXi
    exact RiemannZeta.real_ne_zero_of_mem_Ioo_zero_one
      (s := (1/2 : Real)) (by constructor <;> norm_num) (by simpa using hZeta))
  let : IsEmpty {p : RiemannXiDivisorZeroIndex //
    riemannXiDivisorZeroValue p=(1/2 : Complex)} := hEmpty
  simp only [rootCharacterCentralMultiplicity, ite_true]
  exact @Nat.card_of_isEmpty _ hEmpty

/-- The actual root zero series has an exact logarithmic mean determined
by its central multiplicity. No assertion that central zeros are absent is used. -/
theorem rootCharacterZeroSeries_logMean_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) :
    Tendsto (fun T : Real => Inv.inv (T : Complex)*intervalIntegral
      (fun t : Real => rootCharacterZeroSeries chi k (Real.exp t)) 0 T volume)
      atTop (nhds ((2*(k : Complex)/((k : Complex)-1/2))*
        (rootCharacterCentralMultiplicity chi : Complex))) := by
  by_cases hChi : chi=1
  next =>
    subst chi
    have hRH := (dirichletERH_principal_iff_riemannHypothesis (N := N)).1 hERH
    simpa only [rootCharacterZeroSeries, rootCharacterCentralMultiplicity, ite_true] using
      criticalRootSeries_mean riemannXiDivisorZeroValue
        (Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH)
        Robin1984.summable_robinXiZeroWeight (by omega : 1 <= k)
  next =>
    let : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
    have hPrimitive := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hChi
    have hERHPrimitive := (dirichletERH_iff_primitive chi hChi).1 hERH
    simpa only [rootCharacterZeroSeries, rootCharacterCentralMultiplicity, if_neg hChi] using
      criticalRootSeries_mean (fun p : QuadraticLZeroIndex chi.primitiveCharacter => quadraticLZeroValue p)
        (quadraticLZeroValue_re_eq_half_of_dirichletERH hPrimitive chi.primitiveCharacter_isPrimitive hERHPrimitive)
        (summable_quadraticLZeroWeight hPrimitive chi.primitiveCharacter_isPrimitive) (by omega : 1 <= k)

/-- Every positive power of the logarithmically sampled cutoff has the
same actual root-series mean; all canonical central multiplicities remain. -/
theorem rootCharacterZeroSeries_power_logFloorMean_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) (m : Nat) (hm : 1 <= m) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      rootCharacterZeroSeries chi k ((Nat.floor (Real.exp t) : Real)^m)))
      atTop (nhds ((2*(k : Complex)/((k : Complex)-1/2))*
        (rootCharacterCentralMultiplicity chi : Complex))) := by
  by_cases hChi : chi=1
  next =>
    subst chi
    have hRH := (dirichletERH_principal_iff_riemannHypothesis (N := N)).1 hERH
    simpa only [rootCharacterZeroSeries, rootCharacterCentralMultiplicity, ite_true] using
      criticalRootSeries_power_logFloor_mean riemannXiDivisorZeroValue
        (Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH)
        Robin1984.summable_robinXiZeroWeight (by omega : 1 <= k) m hm
  next =>
    let : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
    have hPrimitive := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hChi
    have hERHPrimitive := (dirichletERH_iff_primitive chi hChi).1 hERH
    simpa only [rootCharacterZeroSeries, rootCharacterCentralMultiplicity, if_neg hChi] using
      criticalRootSeries_power_logFloor_mean (fun p : QuadraticLZeroIndex chi.primitiveCharacter => quadraticLZeroValue p)
        (quadraticLZeroValue_re_eq_half_of_dirichletERH hPrimitive chi.primitiveCharacter_isPrimitive hERHPrimitive)
        (summable_quadraticLZeroWeight hPrimitive chi.primitiveCharacter_isPrimitive) (by omega : 1 <= k) m hm

end

end RobinBV.NumberField
