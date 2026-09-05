import RobinBV.NumberField.Proof.DirichletCharacterWeightedArithmetic
import RobinBV.NumberField.Proof.ImprimitiveEndpointCorrection
import RobinBV.NumberField.Proof.ImprimitivePrimePowerCorrection

/-!
# Absolute endpoint reconstruction at each excluded prime

At a fixed prime, every power is retained and the integrals of the norms
have a complete geometric majorant even at exponent one. This is stronger
than the global untwisted exponent-two convergence input: restricting the
base prime permits the endpoint sum-integral interchange unconditionally.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

/-- Complete geometric domination for one fixed prime, including exponent
zero (whose von Mangoldt coefficient vanishes). -/
theorem integral_norm_fixedPrimeIndicator_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {p : Nat} (hp : Nat.Prime p) (k : Nat) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real =>
      norm (dirichletCharacterPrimePowerIndicator chi 1 (p ^ k) t)) <=
        (Real.log p * Inv.inv (Real.log x)) * (Inv.inv (p : Real)) ^ k := by
  have hLeft := integrableOn_dirichletCharacterPrimePowerIndicator chi
    (by norm_num : 1 <= (1 : Nat)) hx (p ^ k)
  have hRight := Robin1984.integrableOn_robinPrimePowerIndicator
    (by norm_num : 1 <= (1 : Nat)) hx (p ^ k)
  have hCompare : integral (volume.restrict (Ioi x)) (fun t : Real =>
      norm (dirichletCharacterPrimePowerIndicator chi 1 (p ^ k) t)) <=
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          norm (Robin1984.robinPrimePowerIndicator 1 (p ^ k) t : Complex)) := by
    apply integral_mono_ae hLeft.norm hRight.ofReal.norm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_dirichletCharacterPrimePowerIndicator_le chi (hx.trans ht)
  have hPositiveIntegral : integral (volume.restrict (Ioi x)) (fun t : Real =>
      norm (Robin1984.robinPrimePowerIndicator 1 (p ^ k) t : Complex)) =
        integral (volume.restrict (Ioi x)) (Robin1984.robinPrimePowerIndicator 1 (p ^ k)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Robin1984.robinPrimePowerIndicator_nonneg (hx.trans ht))]
  have hIntegral := Robin1984.integral_robinPrimePowerIndicator
    (by norm_num : 1 <= (1 : Nat)) hx (p ^ k)
  have hRealIntegral : integral (volume.restrict (Ioi x))
      (Robin1984.robinPrimePowerIndicator 1 (p ^ k)) =
        ((ArithmeticFunction.vonMangoldt (p ^ k) : Complex) *
          Robin1984.robinCutoffMellinTest 1 x (p ^ k : Nat)).re := by
    rw [<- hIntegral, integral_complex_ofReal, Complex.ofReal_re]
  have hVM : ArithmeticFunction.vonMangoldt (p ^ k) <= Real.log p := by
    by_cases hk : k = 0
    case pos =>
      subst k
      simpa using (Real.log_nonneg (show (1 : Real) <= p by exact_mod_cast hp.one_le))
    case neg =>
      rw [ArithmeticFunction.vonMangoldt_apply_pow hk,
        ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hPowerPos : (0 : Real) < (p ^ k : Nat) := by exact_mod_cast Nat.pow_pos hp.pos
  have hCutoff := Robin1984.norm_robinCutoffMellinTest_le 1 hx hPowerPos
  calc
    _ <= integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm (Robin1984.robinPrimePowerIndicator 1 (p ^ k) t : Complex)) := hCompare
    _ = ((ArithmeticFunction.vonMangoldt (p ^ k) : Complex) *
        Robin1984.robinCutoffMellinTest 1 x (p ^ k : Nat)).re := by
      rw [hPositiveIntegral, hRealIntegral]
    _ <= norm ((ArithmeticFunction.vonMangoldt (p ^ k) : Complex) *
        Robin1984.robinCutoffMellinTest 1 x (p ^ k : Nat)) :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    _ = ArithmeticFunction.vonMangoldt (p ^ k) *
        norm (Robin1984.robinCutoffMellinTest 1 x (p ^ k : Nat)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ <= Real.log p * (Inv.inv (Real.log x) * (p ^ k : Nat) ^ (-(1 : Real))) := by
      exact mul_le_mul hVM (by simpa only [Nat.cast_one] using hCutoff) (norm_nonneg _)
        (Real.log_nonneg (by exact_mod_cast hp.one_le))
    _ = _ := by
      rw [Real.rpow_neg_one, Nat.cast_pow, inv_pow]
      ring

/-- Absolute norm-integral summability for all powers of one prime at the
critical endpoint. No character cancellation or ERH assumption is needed. -/
theorem summable_integral_norm_fixedPrimeIndicators
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {p : Nat} (hp : Nat.Prime p) {x : Real} (hx : 1 < x) :
    Summable (fun k : Nat => integral (volume.restrict (Ioi x)) (fun t : Real =>
      norm (dirichletCharacterPrimePowerIndicator chi 1 (p ^ k) t))) := by
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hInvPos : 0 < Inv.inv (p : Real) := inv_pos.mpr hpPos
  have hMul : Inv.inv (p : Real) * (p : Real) = 1 := by field_simp [hpPos.ne']
  have hInv : norm (Inv.inv (p : Real)) < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hInvPos]
    nlinarith
  have hMajor := (summable_geometric_of_norm_lt_one hInv).mul_left
    (Real.log p * Inv.inv (Real.log x))
  exact Summable.of_nonneg_of_le
    (fun k => integral_nonneg (fun t => norm_nonneg _))
    (fun k => integral_norm_fixedPrimeIndicator_le chi hp k hx) hMajor

/-- The infinite fixed-prime indicator sum equals its exact finite
Chebyshev step, including every power at the cutoff. -/
theorem tsum_fixedPrimeIndicators_eq
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {p : Nat} (hp : Nat.Prime p) {t : Real} (ht : 1 < t) :
    tsum (fun k : Nat => dirichletCharacterPrimePowerIndicator chi 1 (p ^ k) t) =
      ((Real.log p : Complex) * Finset.sum (Finset.Icc 1 (Nat.log p (Nat.floor t)))
        (fun k => chi (p : ZMod N) ^ k)) * (Robin1984.robinRealWeight 1 t : Complex) := by
  have htNonneg : 0 <= t := by linarith
  have hFloorPos : 0 < Nat.floor t := by
    have hOne : 1 <= Nat.floor t := Nat.le_floor (by simpa only [Nat.cast_one] using ht.le)
    omega
  have hSupport : forall k : Nat,
      Not (Membership.mem (Finset.Icc 1 (Nat.log p (Nat.floor t))) k) ->
        dirichletCharacterPrimePowerIndicator chi 1 (p ^ k) t = 0 := by
    intro k hk
    by_cases hkZero : k = 0
    case pos =>
      subst k
      simp [dirichletCharacterPrimePowerIndicator,
        BombieriVinogradov.SiegelWalfisz.twistedMangoldtSequence]
    case neg =>
      have hOutside : Not ((p ^ k : Nat) <= t) := by
        intro hInside
        have hFloor : p ^ k <= Nat.floor t := (Nat.le_floor_iff htNonneg).2 hInside
        have hLog := Nat.le_log_of_pow_le hp.one_lt hFloor
        exact hk (Finset.mem_Icc.mpr (And.intro (by omega) hLog))
      unfold dirichletCharacterPrimePowerIndicator
      exact Set.indicator_of_notMem (s := Ici ((p ^ k : Nat) : Real)) hOutside _
  rw [tsum_eq_sum hSupport, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hRange := Finset.mem_Icc.mp hk
  have hkNe : Not (k = 0) := by omega
  have hFloor : p ^ k <= Nat.floor t := Nat.pow_le_of_le_log hFloorPos.ne' hRange.2
  have hInside : (p ^ k : Nat) <= t := (Nat.le_floor_iff htNonneg).1 hFloor
  unfold dirichletCharacterPrimePowerIndicator
  rw [Set.indicator_of_mem (s := Ici ((p ^ k : Nat) : Real)) hInside]
  unfold BombieriVinogradov.SiegelWalfisz.twistedMangoldtSequence
  rw [ArithmeticFunction.vonMangoldt_apply_pow hkNe,
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, map_pow]
  ring

/-- Absolute endpoint Fubini for the complete power sequence of one prime. -/
theorem fixedPrimeCutoffSeries_eq_integral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {p : Nat} (hp : Nat.Prime p) {x : Real} (hx : 1 < x) :
    tsum (fun k : Nat =>
      BombieriVinogradov.SiegelWalfisz.twistedMangoldtSequence chi (p ^ k) *
        Robin1984.robinCutoffMellinTest 1 x (p ^ k : Nat)) =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        ((Real.log p : Complex) * Finset.sum (Finset.Icc 1 (Nat.log p (Nat.floor t)))
          (fun k => chi (p : ZMod N) ^ k)) * (Robin1984.robinRealWeight 1 t : Complex)) := by
  have hInt (k : Nat) := integrableOn_dirichletCharacterPrimePowerIndicator chi
    (by norm_num : 1 <= (1 : Nat)) hx (p ^ k)
  calc
    _ = tsum (fun k : Nat => integral (volume.restrict (Ioi x))
        (dirichletCharacterPrimePowerIndicator chi 1 (p ^ k))) := by
      apply tsum_congr
      intro k
      exact (integral_dirichletCharacterPrimePowerIndicator chi
        (by norm_num : 1 <= (1 : Nat)) hx (p ^ k)).symm
    _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
        tsum (fun k : Nat => dirichletCharacterPrimePowerIndicator chi 1 (p ^ k) t)) :=
      integral_tsum_of_summable_integral_norm hInt
        (summable_integral_norm_fixedPrimeIndicators chi hp hx)
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact tsum_fixedPrimeIndicators_eq chi hp (hx.trans ht)

/-- At each real argument the fixed-prime indicator sequence has finite
support, so its pointwise series is summable as well as integrable in norm. -/
theorem summable_fixedPrimeIndicators
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {p : Nat} (hp : Nat.Prime p) {t : Real} (ht : 1 < t) :
    Summable (fun k : Nat => dirichletCharacterPrimePowerIndicator chi 1 (p ^ k) t) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 (Nat.log p (Nat.floor t)))
  intro k hk
  by_cases hkZero : k = 0
  case pos =>
    subst k
    simp [dirichletCharacterPrimePowerIndicator,
      BombieriVinogradov.SiegelWalfisz.twistedMangoldtSequence]
  case neg =>
    have hOutside : Not ((p ^ k : Nat) <= t) := by
      intro hInside
      have hFloor : p ^ k <= Nat.floor t := (Nat.le_floor_iff (by linarith : 0 <= t)).2 hInside
      have hLog := Nat.le_log_of_pow_le hp.one_lt hFloor
      exact hk (Finset.mem_Icc.mpr (And.intro (by omega) hLog))
    unfold dirichletCharacterPrimePowerIndicator
    exact Set.indicator_of_notMem (s := Ici ((p ^ k : Nat) : Real)) hOutside _

/-- The actual complete change-of-level endpoint integral is exactly the
absolutely convergent sum of all excluded prime-power cutoff terms. -/
theorem dirichletWeightedIntegral_sub_primitive_eq_primePowerSeries
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Not (chi = 1)) {x : Real} (hx : 3 <= x) :
    dirichletCharacterWeightedIntegral chi 1 x -
        dirichletCharacterWeightedIntegral chi.primitiveCharacter 1 x =
      -Finset.sum N.primeFactors (fun p => tsum (fun k : Nat =>
        BombieriVinogradov.SiegelWalfisz.twistedMangoldtSequence chi.primitiveCharacter (p ^ k) *
          Robin1984.robinCutoffMellinTest 1 x (p ^ k : Nat))) := by
  classical
  have hxOne : 1 < x := by linarith
  let P : Type := {p : Nat // Membership.mem N.primeFactors p}
  let F : Prod P Nat -> Real -> Complex := fun a =>
    dirichletCharacterPrimePowerIndicator chi.primitiveCharacter 1 (a.1.1 ^ a.2)
  have hInt (a : Prod P Nat) : IntegrableOn (F a) (Ioi x) :=
    integrableOn_dirichletCharacterPrimePowerIndicator chi.primitiveCharacter
      (by norm_num : 1 <= (1 : Nat)) hxOne (a.1.1 ^ a.2)
  have hNormInt : Summable (fun a : Prod P Nat =>
      integral (volume.restrict (Ioi x)) (fun t : Real => norm (F a t))) := by
    apply (summable_prod_of_nonneg (fun a => integral_nonneg (fun t => norm_nonneg _))).2
    constructor
    next =>
      intro p
      exact summable_integral_norm_fixedPrimeIndicators chi.primitiveCharacter
        (Nat.mem_primeFactors.mp p.2).1 hxOne
    next =>
      apply summable_of_ne_finset_zero (s := Finset.univ)
      intro p hp
      exact False.elim (hp (Finset.mem_univ p))
  have hSumInt : Summable (fun a : Prod P Nat => integral (volume.restrict (Ioi x)) (F a)) :=
    hNormInt.of_norm_bounded (fun a => norm_integral_le_integral_norm _)
  have hPoint (t : Real) (ht : 1 < t) : Summable (fun a : Prod P Nat => F a t) := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun a => norm_nonneg _)).2
    constructor
    next =>
      intro p
      exact (summable_fixedPrimeIndicators chi.primitiveCharacter
        (Nat.mem_primeFactors.mp p.2).1 ht).norm
    next =>
      apply summable_of_ne_finset_zero (s := Finset.univ)
      intro p hp
      exact False.elim (hp (Finset.mem_univ p))
  have hLeft : tsum (fun a : Prod P Nat => integral (volume.restrict (Ioi x)) (F a)) =
      Finset.sum N.primeFactors (fun p => tsum (fun k : Nat =>
        BombieriVinogradov.SiegelWalfisz.twistedMangoldtSequence chi.primitiveCharacter (p ^ k) *
          Robin1984.robinCutoffMellinTest 1 x (p ^ k : Nat))) := by
    rw [hSumInt.tsum_prod, tsum_fintype]
    calc
      _ = Finset.sum Finset.univ (fun p : P => tsum (fun k : Nat =>
          BombieriVinogradov.SiegelWalfisz.twistedMangoldtSequence chi.primitiveCharacter (p.1 ^ k) *
            Robin1984.robinCutoffMellinTest 1 x (p.1 ^ k : Nat))) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply tsum_congr
        intro k
        exact integral_dirichletCharacterPrimePowerIndicator chi.primitiveCharacter
          (by norm_num : 1 <= (1 : Nat)) hxOne (p.1 ^ k)
      _ = _ := Finset.sum_coe_sort N.primeFactors (fun p : Nat => tsum (fun k : Nat =>
        BombieriVinogradov.SiegelWalfisz.twistedMangoldtSequence chi.primitiveCharacter (p ^ k) *
          Robin1984.robinCutoffMellinTest 1 x (p ^ k : Nat)))
  have hRight : integral (volume.restrict (Ioi x)) (fun t : Real =>
      tsum (fun a : Prod P Nat => F a t)) =
      -(dirichletCharacterWeightedIntegral chi 1 x -
        dirichletCharacterWeightedIntegral chi.primitiveCharacter 1 x) := by
    rw [dirichletWeightedIntegral_sub_primitive_eq chi hchi hx, <- integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htOne : 1 < t := hxOne.trans ht
    dsimp only
    rw [(hPoint t htOne).tsum_prod, tsum_fintype]
    calc
      _ = Finset.sum Finset.univ (fun p : P =>
          ((Real.log p.1 : Complex) *
            Finset.sum (Finset.Icc 1 (Nat.log p.1 (Nat.floor t)))
              (fun k => chi.primitiveCharacter (p.1 : ZMod chi.conductor) ^ k)) *
                (Robin1984.robinRealWeight 1 t : Complex)) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact tsum_fixedPrimeIndicators_eq chi.primitiveCharacter
          (Nat.mem_primeFactors.mp p.2).1 htOne
      _ = Finset.sum N.primeFactors (fun p =>
          ((Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 (Nat.log p (Nat.floor t)))
              (fun k => chi.primitiveCharacter (p : ZMod chi.conductor) ^ k)) *
                (Robin1984.robinRealWeight 1 t : Complex)) :=
        Finset.sum_coe_sort N.primeFactors (fun p : Nat =>
          ((Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 (Nat.log p (Nat.floor t)))
              (fun k => chi.primitiveCharacter (p : ZMod chi.conductor) ^ k)) *
                (Robin1984.robinRealWeight 1 t : Complex))
      _ = _ := by
        rw [characterChebyshevSum_sub_primitive_eq_sum_primePowers chi (Nat.floor t),
          neg_mul, neg_neg, Finset.sum_mul]
  have hAll := integral_tsum_of_summable_integral_norm hInt hNormInt
  rw [hLeft, hRight] at hAll
  linear_combination hAll

end

end RobinBV.NumberField
