import BombieriVinogradov.Assembly.SiegelWalfisz.Main
import BombieriVinogradov.Helpers.RealAnalysis.PolynomialExponentialAbsorption
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Robin1984.NicolasLandau.WeightedPsiIntegral
import RobinBV.NumberField.Proof.QuadraticDedekindWeightedError

/-!
# Quadratic character endpoint integrability

This module derives logarithmic decay for each fixed nonprincipal quadratic
character from Siegel-Walfisz and uses it to prove integrability of the
quadratic character contribution against the Nicolas weight at exponent one.
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

theorem exists_quadraticCharacterChebyshevStep_log_decay
    (D : NumberField.OddFundamentalDiscriminant) :
    exists K : Real, And (0 < K) (exists X : Real,
      And (4 <= X) (And (Real.exp 1 <= X) (forall t : Real, X <= t ->
        abs (quadraticCharacterChebyshevStep D t) <=
          K * (t / Real.log t)))) := by
  have hWitness := exists_characterChebyshevSum_log_decay
  let K0 : Real := hWitness.choose
  have hK0 : 0 < K0 := hWitness.choose_spec.1
  let K : Real := 2 * K0
  let X : Real := max 4 (max (Real.exp 1)
    ((Nat.ceil (Real.exp (D.modulus : Real)) : Nat) : Real))
  have hK : 0 < K := by dsimp [K]; positivity
  refine Exists.intro K (And.intro hK (Exists.intro X
    (And.intro (le_max_left 4 _) (And.intro
      (le_trans (le_max_left (Real.exp 1) _) (le_max_right 4 _)) ?_))))
  intro t ht
  let n : Nat := Nat.floor t
  have htFour : 4 <= t := (le_max_left 4 _).trans ht
  have hnFour : 4 <= n := Nat.le_floor htFour
  have hCeil : Real.exp (D.modulus : Real) <=
      ((Nat.ceil (Real.exp (D.modulus : Real)) : Nat) : Real) :=
    Nat.le_ceil (Real.exp (D.modulus : Real))
  have hCeilFloor : Nat.ceil (Real.exp (D.modulus : Real)) <= n := by
    apply Nat.le_floor
    exact (le_trans (le_max_right (Real.exp 1) _)
      (le_max_right 4 _)).trans ht
  have hMod : (D.modulus : Real) <= Real.log (n : Real) := by
    calc
      (D.modulus : Real) = Real.log (Real.exp (D.modulus : Real)) :=
        (Real.log_exp _).symm
      _ <= Real.log (n : Real) :=
        Real.log_le_log (Real.exp_pos _) (hCeil.trans (by exact_mod_cast hCeilFloor))
  have hNat := hWitness.choose_spec.2 D.character
    (quadraticCharacter_ne_one D) (x := n) (by omega) hMod
  unfold quadraticCharacterChebyshevStep
  change abs (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum n D.character).re <=
    K * (t / Real.log t)
  calc
    abs (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum n D.character).re <=
        norm (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum n D.character) :=
      Complex.abs_re_le_norm _
    _ <= K0 * ((n : Real) / Real.log (n : Real)) := hNat
    _ <= K0 * (2 * (t / Real.log t)) :=
      mul_le_mul_of_nonneg_left (natFloor_div_log_le_two_mul_div_log htFour) hK0.le
    _ = K * (t / Real.log t) := by dsimp [K]; ring

theorem integrableOn_quadraticCharacterChebyshevStep_mul_weight_one
    (D : NumberField.OddFundamentalDiscriminant) :
    IntegrableOn (fun t : Real =>
      quadraticCharacterChebyshevStep D t *
        Robin1984.robinRealWeight 1 t) (Ioi 3) := by
  have hDecayWitness := exists_quadraticCharacterChebyshevStep_log_decay D
  let K : Real := hDecayWitness.choose
  have hK : 0 < K := hDecayWitness.choose_spec.1
  let X : Real := hDecayWitness.choose_spec.2.choose
  have hXFour : 4 <= X := hDecayWitness.choose_spec.2.choose_spec.1
  have hExpOne : Real.exp 1 <= X := hDecayWitness.choose_spec.2.choose_spec.2.1
  have hDecay := hDecayWitness.choose_spec.2.choose_spec.2.2
  have hStepMeasurable : Measurable (quadraticCharacterChebyshevStep D) := by
    unfold quadraticCharacterChebyshevStep
    exact (measurable_of_countable (fun k : Nat =>
      (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum
        k D.character).re)).comp Nat.measurable_floor
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
      quadraticCharacterChebyshevStep D t *
        Robin1984.robinRealWeight 1 t) (Ioi X) := by
    apply hMajor.mono'
    next =>
      exact (hStepMeasurable.mul hWeightMeasurable).aestronglyMeasurable
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
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hWeightNonneg]
      calc
        abs (quadraticCharacterChebyshevStep D t) *
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
  have hStepAEMeasurable : AEStronglyMeasurable
      (quadraticCharacterChebyshevStep D) (volume.restrict (Ioc 3 X)) :=
    hStepMeasurable.aestronglyMeasurable
  have hCompactRaw : IntegrableOn (fun t : Real =>
      Robin1984.robinRealWeight 1 t * quadraticCharacterChebyshevStep D t)
      (Ioc 3 X) := by
    apply hWeightCompact.mul_bdd (c := Chebyshev.psi X) hStepAEMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    exact (abs_quadraticCharacterChebyshevStep_le_psi D t).trans
      (Chebyshev.psi_mono ht.2)
  have hCompact : IntegrableOn (fun t : Real =>
      quadraticCharacterChebyshevStep D t * Robin1984.robinRealWeight 1 t)
      (Ioc 3 X) := by
    simpa only [mul_comm] using hCompactRaw
  have hAll := hCompact.union hTail
  rw [Ioc_union_Ioi_eq_Ioi (by linarith : (3 : Real) <= X)] at hAll
  exact hAll

end

end RobinBV.NumberField
