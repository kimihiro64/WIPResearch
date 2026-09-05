import PrimeNumberTheoremAnd.Consequences
import RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimeChebyshev
import RobinBV.NumberField.Proof.QuadraticCharacterEndpoint

/-!
# Character prime moments from the actual Siegel-Walfisz theorem

The complete elementary prime-power remainder transfers the proved SW
estimate to logarithmic prime averages. Principal averages use ordinary PNT
and the finite conductor correction. No prime-moment hypothesis is added.
The eventual cutoffs here may depend on the character's fixed modulus.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter Asymptotics BombieriVinogradov.SiegelWalfisz
open scoped Classical

noncomputable section

private theorem theta_ratio_tendsto :
    Tendsto (fun P : Nat => Chebyshev.theta (P : Real) / (P : Real)) atTop (nhds (1 : Real)) := by
  have hNe : Filter.Eventually (fun x : Real => Not (id x = 0)) atTop := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    exact hx.ne'
  have hReal : Tendsto (fun x : Real => Chebyshev.theta x / x) atTop (nhds (1 : Real)) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hNe).1 chebyshev_asymptotic
  exact hReal.comp tendsto_natCast_atTop_atTop

private theorem psi_sub_theta_ratio_tendsto :
    Tendsto (fun P : Nat => (Chebyshev.psi (P : Real) - Chebyshev.theta (P : Real)) /
      (P : Real)) atTop (nhds (0 : Real)) := by
  have hNe : Filter.Eventually (fun x : Real => Not (x = 0)) atTop := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    exact hx.ne'
  have hReal : Tendsto (fun x : Real => Chebyshev.psi x / x) atTop (nhds (1 : Real)) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hNe).1 WeakPNT''
  have hNat : Tendsto (fun P : Nat => Chebyshev.psi (P : Real) / (P : Real))
      atTop (nhds (1 : Real)) := hReal.comp tendsto_natCast_atTop_atTop
  simpa only [sub_self, sub_div] using hNat.sub theta_ratio_tendsto

/-- The existing Siegel-Walfisz provider gives a vanishing normalized
Mangoldt sum for every fixed nonprincipal character, primitive or not. -/
theorem characterChebyshevSum_div_tendsto_zero
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hChi : Not (chi = 1)) :
    Tendsto (fun P : Nat => characterChebyshevSum P chi / (P : Complex)) atTop (nhds 0) := by
  obtain hK := exists_characterChebyshevSum_log_decay
  let K : Real := hK.choose
  have hLog : Tendsto (fun P : Nat => Real.log (P : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hMod := hLog.eventually (Filter.eventually_ge_atTop (N : Real))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (g := fun P : Nat => K / Real.log P)
  next =>
    filter_upwards [Filter.eventually_ge_atTop (2 : Nat), hMod] with P hP hN
    have hPPos : (0 : Real) < P := by exact_mod_cast (show 0 < P by omega)
    rw [norm_div, Complex.norm_natCast]
    calc
      _ <= (K * ((P : Real) / Real.log P)) / (P : Real) :=
        div_le_div_of_nonneg_right (hK.choose_spec.2 chi hChi hP hN) hPPos.le
      _ = _ := by field_simp [hPPos.ne']
  next =>
    exact hLog.const_div_atTop K

/-- Every higher prime power is retained in the transfer from weighted
Mangoldt sums to logarithmic prime sums; its normalized norm vanishes. -/
theorem characterChebyshevSum_sub_primeSum_div_tendsto
    {N : Nat} (chi : DirichletCharacter Complex N) :
    Tendsto (fun P : Nat =>
      (characterChebyshevSum P chi - chi.primeChebyshevSum P) / (P : Complex))
        atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (g := fun P : Nat => (Chebyshev.psi (P : Real) - Chebyshev.theta (P : Real)) /
      (P : Real))
  next =>
    apply Filter.Eventually.of_forall
    intro P
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right
      (chi.norm_sum_vonMangoldt_sub_primeChebyshevSum_le P) (Nat.cast_nonneg P)
  next =>
    exact psi_sub_theta_ratio_tendsto

/-- The logarithmic prime average of any fixed nonprincipal complex
character tends to zero, with no primitivity or parity restriction. -/
theorem primeChebyshevSum_div_tendsto_zero
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hChi : Not (chi = 1)) :
    Tendsto (fun P : Nat => chi.primeChebyshevSum P / (P : Complex)) atTop (nhds 0) := by
  have h := (characterChebyshevSum_div_tendsto_zero chi hChi).sub
    (characterChebyshevSum_sub_primeSum_div_tendsto chi)
  convert h using 1
  next =>
    funext P
    ring
  next =>
    simp

/-- The principal prime average tends to one. The full finite correction at
the bad primes is retained before taking the fixed-modulus limit. -/
theorem primeChebyshevSum_principal_div_tendsto_one
    {N : Nat} [NeZero N] :
    Tendsto (fun P : Nat => (1 : DirichletCharacter Complex N).primeChebyshevSum P /
      (P : Complex)) atTop (nhds 1) := by
  have hPrimitive (P : Nat) :
      (1 : DirichletCharacter Complex N).primitiveCharacter.primeChebyshevSum P =
        (Chebyshev.theta (P : Real) : Complex) := by
    unfold DirichletCharacter.primeChebyshevSum
    rw [Chebyshev.theta_eq_sum_primesLE_log, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro p _
    have hValue : (1 : DirichletCharacter Complex N).primitiveCharacter p = 1 := by
      rw [DirichletCharacter.primitiveCharacter_one]
      apply MulChar.one_apply
      have hConductor : (1 : DirichletCharacter Complex N).conductor = 1 :=
        DirichletCharacter.conductor_one
      rw [hConductor]
      exact isUnit_of_subsingleton _
    rw [hValue, mul_one]
  have hDifference : Tendsto (fun P : Nat =>
      ((1 : DirichletCharacter Complex N).primeChebyshevSum P -
        (Chebyshev.theta (P : Real) : Complex)) / (P : Complex)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (g := fun P : Nat => Finset.sum N.primeFactors (fun p => Real.log p) / (P : Real))
    next =>
      apply Filter.Eventually.of_forall
      intro P
      rw [norm_div, Complex.norm_natCast, <- hPrimitive P]
      exact div_le_div_of_nonneg_right
        ((1 : DirichletCharacter Complex N).norm_primeChebyshevSum_sub_primitive_le P)
        (Nat.cast_nonneg P)
    next =>
      exact Filter.Tendsto.const_div_atTop
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop) _
  have hTheta : Tendsto (fun P : Nat => (Chebyshev.theta (P : Real) : Complex) / (P : Complex))
      atTop (nhds (1 : Complex)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_one] using
      theta_ratio_tendsto.ofReal
  convert hDifference.add hTheta using 1
  next =>
    funext P
    ring
  next =>
    simp

/-- Every fixed complex character has the prime average dictated by its
principality, with both principal and nonprincipal cases proved. -/
theorem primeChebyshevSum_div_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    Tendsto (fun P : Nat => chi.primeChebyshevSum P / (P : Complex))
      atTop (nhds (if chi = 1 then (1 : Complex) else 0)) := by
  classical
  by_cases hChi : chi = 1
  case pos =>
    rw [hChi, if_pos rfl]
    exact primeChebyshevSum_principal_div_tendsto_one
  case neg =>
    rw [if_neg hChi]
    exact primeChebyshevSum_div_tendsto_zero chi hChi

/-- The complete finite positive-power prime moment tends to the number
of principal character powers in the prefix. No zero-power evaluation at
nonunits is used. -/
theorem characterPrimePowerMoment_div_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) :
    Tendsto (fun P : Nat =>
      Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
        Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) / (P : Complex))
      atTop (nhds (Finset.sum (Finset.Icc 1 m)
        (fun j => if chi ^ j = 1 then (1 : Complex) else 0))) := by
  classical
  have h := tendsto_finsetSum (Finset.Icc 1 m)
    (fun j _ => primeChebyshevSum_div_tendsto (chi ^ j))
  convert h using 1
  funext P
  rw [<- Finset.sum_div]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  unfold DirichletCharacter.primeChebyshevSum
  apply Finset.sum_congr rfl
  intro p _
  rw [MulChar.pow_apply' chi (by have hPos := (Finset.mem_Icc.mp hj).1; omega)]

end

end RobinBV.NumberField
