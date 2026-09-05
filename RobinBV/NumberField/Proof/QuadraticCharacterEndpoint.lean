import BombieriVinogradov.Assembly.SiegelWalfisz.Main
import BombieriVinogradov.Helpers.RealAnalysis.PolynomialExponentialAbsorption
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Robin1984.NicolasLandau.WeightedPsiIntegral
import RobinBV.NumberField.Proof.QuadraticDedekindWeightedError

/-!
# Complex character endpoint integrability and quadratic specialization

This module derives logarithmic decay for every nonprincipal complex character
from Siegel-Walfisz and proves integrability against the Nicolas weight at
exponent one. It preserves the quadratic specializations used by the field
criterion, but the full norm bound needs neither primitivity nor self-duality.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set

noncomputable section

theorem exists_characterChebyshevSum_log_decay :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        Ne chi 1 -> forall {x : Nat}, 2 <= x ->
          (N : Real) <= Real.log x ->
            norm (characterChebyshevSum x chi) <=
              K * ((x : Real) / Real.log x)) := by
  have hSW := BombieriVinogradov.SiegelWalfisz.siegel_walfisz
  let a : Real := hSW.choose
  have ha : 0 < a := hSW.choose_spec.1
  have hPowerWitness := hSW.choose_spec.2 1 (by norm_num : (0 : Real) < 1)
  let C : Real := hPowerWitness.choose
  have hC : 0 < C := hPowerWitness.choose_spec.1
  let K : Real := C * (2 / a ^ 2)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine Exists.intro K (And.intro hK ?_)
  intro N inst chi hchi x hx hMod
  have hxReal : (1 : Real) < (x : Real) := by exact_mod_cast hx
  have hLogPos : 0 < Real.log (x : Real) := Real.log_pos hxReal
  have hLogNonneg : 0 <= Real.log (x : Real) := hLogPos.le
  have hSWBound := hPowerWitness.choose_spec.2 chi hchi hx (by simpa using hMod)
  have hTaylor :=
    BombieriVinogradov.RealAnalysis.pow_mul_exp_neg_mul_le_factorial_div_pow
      ha (Real.sqrt_nonneg (Real.log (x : Real))) 2
  have hSquare : (Real.sqrt (Real.log (x : Real))) ^ 2 =
      Real.log (x : Real) := Real.sq_sqrt hLogNonneg
  rw [hSquare] at hTaylor
  norm_num at hTaylor
  have hExp : Real.exp (-(a * Real.sqrt (Real.log (x : Real)))) <=
      (2 / a ^ 2) / Real.log (x : Real) := by
    calc
      Real.exp (-(a * Real.sqrt (Real.log (x : Real)))) =
          (Real.log (x : Real) *
            Real.exp (-(a * Real.sqrt (Real.log (x : Real))))) /
              Real.log (x : Real) := by field_simp [hLogPos.ne']
      _ <= (2 / a ^ 2) / Real.log (x : Real) :=
        div_le_div_of_nonneg_right hTaylor hLogPos.le
  calc
    norm (characterChebyshevSum x chi) <=
        C * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := hSWBound
    _ <= C * ((x : Real) * ((2 / a ^ 2) / Real.log x)) := by
      gcongr
    _ = K * ((x : Real) / Real.log x) := by
      dsimp [K]
      ring

theorem natFloor_div_log_le_two_mul_div_log
    {t : Real} (ht : 4 <= t) :
    ((Nat.floor t : Nat) : Real) / Real.log (Nat.floor t : Nat) <=
      2 * (t / Real.log t) := by
  let n : Nat := Nat.floor t
  have hnFour : 4 <= n := by
    exact Nat.le_floor ht
  have hnPos : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hFloor : (n : Real) <= t := by
    exact Nat.floor_le (by linarith)
  have hLower : t / 2 <= (n : Real) := by
    have hLt := Nat.lt_floor_add_one t
    change t < (n : Real) + 1 at hLt
    linarith
  have hLogTPos : 0 < Real.log t := Real.log_pos (by linarith)
  have hLogNPos : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hLogFour : 2 * Real.log (2 : Real) <= Real.log t := by
    calc
      2 * Real.log (2 : Real) = Real.log (4 : Real) := by
        rw [show (4 : Real) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num : Ne (2 : Real) 0) (by norm_num : Ne (2 : Real) 0)]
        ring
      _ <= Real.log t := Real.log_le_log (by norm_num) ht
  have hHalfLog : (1 / 2 : Real) * Real.log t <= Real.log (n : Real) := by
    calc
      (1 / 2 : Real) * Real.log t <= Real.log t - Real.log (2 : Real) := by
        linarith
      _ = Real.log (t / 2) :=
        (Real.log_div (by linarith : Ne t 0) (by norm_num : Ne (2 : Real) 0)).symm
      _ <= Real.log (n : Real) := Real.log_le_log (by positivity) hLower
  have hInv := one_div_le_one_div_of_le
    (mul_pos (by norm_num : (0 : Real) < 1 / 2) hLogTPos) hHalfLog
  change (n : Real) / Real.log (n : Real) <= 2 * (t / Real.log t)
  calc
    (n : Real) / Real.log (n : Real) =
        (n : Real) * (1 / Real.log (n : Real)) := by ring
    _ <= t * (1 / Real.log (n : Real)) :=
      mul_le_mul_of_nonneg_right hFloor (by positivity)
    _ <= t * (1 / ((1 / 2 : Real) * Real.log t)) :=
      mul_le_mul_of_nonneg_left hInv (by linarith)
    _ = 2 * (t / Real.log t) := by
      field_simp [hLogTPos.ne']

/-- The full complex character sum is dominated by the untwisted Mangoldt sum. -/
theorem norm_characterChebyshevSum_le_psi
    {N : Nat} (chi : DirichletCharacter Complex N) (x : Nat) :
    norm (characterChebyshevSum x chi) <= Chebyshev.psi x := by
  have hAll : forall S : Finset Nat,
      norm (S.sum fun n => (ArithmeticFunction.vonMangoldt n : Complex) * chi n) <=
        S.sum (fun n => ArithmeticFunction.vonMangoldt n) := by
    intro S
    apply (norm_sum_le S _).trans
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (chi.norm_le_one n) ArithmeticFunction.vonMangoldt_nonneg
  have hBound := hAll (Finset.Icc 1 x)
  have hPsi := rationalChebyshevSum_eq_psi x
  unfold rationalChebyshevSum at hPsi
  norm_cast at hPsi
  rw [hPsi] at hBound
  exact hBound

theorem exists_characterChebyshevStep_log_decay
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (hchi : Ne chi 1) :
    exists K : Real, And (0 < K) (exists X : Real,
      And (4 <= X) (And (Real.exp 1 <= X) (forall t : Real, X <= t ->
        norm (characterChebyshevSum (Nat.floor t) chi) <=
          K * (t / Real.log t)))) := by
  have hWitness := exists_characterChebyshevSum_log_decay
  let K0 : Real := hWitness.choose
  have hK0 : 0 < K0 := hWitness.choose_spec.1
  let K : Real := 2 * K0
  let X : Real := max 4 (max (Real.exp 1)
    ((Nat.ceil (Real.exp (N : Real)) : Nat) : Real))
  have hK : 0 < K := by dsimp [K]; positivity
  refine Exists.intro K (And.intro hK (Exists.intro X
    (And.intro (le_max_left 4 _) (And.intro
      (le_trans (le_max_left (Real.exp 1) _) (le_max_right 4 _)) ?_))))
  intro t ht
  let n : Nat := Nat.floor t
  have htFour : 4 <= t := (le_max_left 4 _).trans ht
  have hnFour : 4 <= n := Nat.le_floor htFour
  have hCeil : Real.exp (N : Real) <=
      ((Nat.ceil (Real.exp (N : Real)) : Nat) : Real) :=
    Nat.le_ceil (Real.exp (N : Real))
  have hCeilFloor : Nat.ceil (Real.exp (N : Real)) <= n := by
    apply Nat.le_floor
    exact (le_trans (le_max_right (Real.exp 1) _)
      (le_max_right 4 _)).trans ht
  have hMod : (N : Real) <= Real.log (n : Real) := by
    calc
      (N : Real) = Real.log (Real.exp (N : Real)) :=
        (Real.log_exp _).symm
      _ <= Real.log (n : Real) :=
        Real.log_le_log (Real.exp_pos _) (hCeil.trans (by exact_mod_cast hCeilFloor))
  have hNat := hWitness.choose_spec.2 chi
    hchi (x := n) (by omega) hMod
  change norm (characterChebyshevSum n chi) <= K * (t / Real.log t)
  calc
    norm (characterChebyshevSum n chi) <=
        K0 * ((n : Real) / Real.log (n : Real)) := hNat
    _ <= K0 * (2 * (t / Real.log t)) :=
      mul_le_mul_of_nonneg_left (natFloor_div_log_le_two_mul_div_log htFour) hK0.le
    _ = K * (t / Real.log t) := by dsimp [K]; ring

/-- Siegel-Walfisz makes the full complex character contribution integrable
at the Nicolas endpoint, without primitivity or a real-valuedness assumption. -/
theorem integrableOn_characterChebyshevStep_mul_weight_one
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hchi : Ne chi 1) :
    IntegrableOn (fun t : Real =>
      characterChebyshevSum (Nat.floor t) chi *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi 3) := by
  have hDecayWitness := exists_characterChebyshevStep_log_decay chi hchi
  let K : Real := hDecayWitness.choose
  have hK : 0 < K := hDecayWitness.choose_spec.1
  let X : Real := hDecayWitness.choose_spec.2.choose
  have hXFour : 4 <= X := hDecayWitness.choose_spec.2.choose_spec.1
  have hExpOne : Real.exp 1 <= X := hDecayWitness.choose_spec.2.choose_spec.2.1
  have hDecay := hDecayWitness.choose_spec.2.choose_spec.2.2
  have hStepMeasurable : Measurable
      (fun t : Real => characterChebyshevSum (Nat.floor t) chi) :=
    (measurable_of_countable (fun k : Nat => characterChebyshevSum k chi)).comp
      Nat.measurable_floor
  have hWeightMeasurable : Measurable (Robin1984.robinRealWeight 1) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  have hBase : IntegrableOn (fun t : Real =>
      Inv.inv t / (Real.log t) ^ 2) (Ioi X) := by
    simpa only using integrableOn_inv_div_log_sq_Ioi
      (lt_of_lt_of_le (by norm_num : (1 : Real) < 4) hXFour)
  have hMajor : IntegrableOn (fun t : Real =>
      (2 * K) * (Inv.inv t / (Real.log t) ^ 2)) (Ioi X) :=
    hBase.const_mul (2 * K)
  have hTail : IntegrableOn (fun t : Real =>
      characterChebyshevSum (Nat.floor t) chi *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi X) := by
    apply hMajor.mono'
    next =>
      exact (hStepMeasurable.mul
        (Complex.continuous_ofReal.measurable.comp hWeightMeasurable)).aestronglyMeasurable
    next =>
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htFour : 4 < t := lt_of_le_of_lt hXFour ht
      have htPos : 0 < t := lt_trans (by norm_num : (0 : Real) < 4) htFour
      have hLogPos : 0 < Real.log t := Real.log_pos (by linarith)
      have hLogOne : 1 <= Real.log t := by
        calc
          (1 : Real) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ <= Real.log t := Real.log_le_log (Real.exp_pos 1)
            (hExpOne.trans ht.le)
      have hInvLog : 1 / Real.log t <= 1 := by
        have hRaw := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hLogOne
        simpa only [one_div_one] using hRaw
      have hWeightNonneg : 0 <= Robin1984.robinRealWeight 1 t :=
        Robin1984.robinRealWeight_nonneg (by linarith)
      have hStep := hDecay t ht.le
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hWeightNonneg]
      calc
        norm (characterChebyshevSum (Nat.floor t) chi) *
            Robin1984.robinRealWeight 1 t <=
          (K * (t / Real.log t)) * Robin1984.robinRealWeight 1 t :=
            mul_le_mul_of_nonneg_right hStep hWeightNonneg
        _ = K * (Inv.inv t / (Real.log t) ^ 2) *
            (1 + 1 / Real.log t) := by
          rw [quadraticDedekindRealWeight_one_eq_nicolasTailKernel (by linarith)]
          unfold quadraticDedekindNicolasTailKernel
          field_simp [htPos.ne', hLogPos.ne']
        _ <= K * (Inv.inv t / (Real.log t) ^ 2) * 2 := by
          have hFactor : 1 + 1 / Real.log t <= 2 := by linarith
          apply mul_le_mul_of_nonneg_left hFactor
          positivity
        _ = (2 * K) * (Inv.inv t / (Real.log t) ^ 2) := by ring
  have hWeightCompact : IntegrableOn (Robin1984.robinRealWeight 1) (Ioc 3 X) :=
    (Robin1984.integrableOn_robinRealWeight
      (by norm_num : 1 <= (1 : Nat)) (by norm_num : (1 : Real) < 3)).mono_set
        Ioc_subset_Ioi_self
  have hWeightComplex : IntegrableOn (fun t : Real =>
      (Robin1984.robinRealWeight 1 t : Complex)) (Ioc 3 X) := hWeightCompact.ofReal
  have hStepAEMeasurable : AEStronglyMeasurable
      (fun t : Real => characterChebyshevSum (Nat.floor t) chi)
      (volume.restrict (Ioc 3 X)) := hStepMeasurable.aestronglyMeasurable
  have hCompactRaw : IntegrableOn (fun t : Real =>
      (Robin1984.robinRealWeight 1 t : Complex) *
        characterChebyshevSum (Nat.floor t) chi) (Ioc 3 X) := by
    apply hWeightComplex.mul_bdd (c := Chebyshev.psi X) hStepAEMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    calc
      norm (characterChebyshevSum (Nat.floor t) chi) <=
          Chebyshev.psi (Nat.floor t) := norm_characterChebyshevSum_le_psi chi _
      _ = Chebyshev.psi t := (Chebyshev.psi_eq_psi_coe_floor t).symm
      _ <= Chebyshev.psi X := Chebyshev.psi_mono ht.2
  have hCompact : IntegrableOn (fun t : Real =>
      characterChebyshevSum (Nat.floor t) chi *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioc 3 X) := by
    simpa only [mul_comm] using hCompactRaw
  have hAll := hCompact.union hTail
  rw [Ioc_union_Ioi_eq_Ioi (by linarith : (3 : Real) <= X)] at hAll
  exact hAll

theorem exists_quadraticCharacterChebyshevStep_log_decay
    (D : NumberField.OddFundamentalDiscriminant) :
    exists K : Real, And (0 < K) (exists X : Real,
      And (4 <= X) (And (Real.exp 1 <= X) (forall t : Real, X <= t ->
        abs (quadraticCharacterChebyshevStep D t) <=
          K * (t / Real.log t)))) := by
  have h := exists_characterChebyshevStep_log_decay D.character (quadraticCharacter_ne_one D)
  refine Exists.intro h.choose (And.intro h.choose_spec.1
    (Exists.intro h.choose_spec.2.choose
      (And.intro h.choose_spec.2.choose_spec.1
        (And.intro h.choose_spec.2.choose_spec.2.1 ?_))))
  intro t ht
  exact (Complex.abs_re_le_norm _).trans (h.choose_spec.2.choose_spec.2.2 t ht)

theorem integrableOn_quadraticCharacterChebyshevStep_mul_weight_one
    (D : NumberField.OddFundamentalDiscriminant) :
    IntegrableOn (fun t : Real =>
      quadraticCharacterChebyshevStep D t *
        Robin1984.robinRealWeight 1 t) (Ioi 3) := by
  have h := integrableOn_characterChebyshevStep_mul_weight_one
    D.character (quadraticCharacter_ne_one D)
  have hReal := h.re
  change IntegrableOn (fun t : Real =>
    (characterChebyshevSum (Nat.floor t) D.character *
      (Robin1984.robinRealWeight 1 t : Complex)).re) (Ioi 3) at hReal
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, quadraticCharacterChebyshevStep] using hReal

end

end RobinBV.NumberField
