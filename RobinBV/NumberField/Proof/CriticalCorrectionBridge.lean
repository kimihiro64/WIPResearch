import Mathlib.Analysis.Complex.Exponential
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RobinBV.NumberField.Definitions.RobinCriterion
import RobinBV.NumberField.Proof.IdealAbundancyEulerProduct

/-!
# From logarithmic defects to additive critical corrections

This module turns the ideal logarithmic-defect estimate into the additive
square-root correction used by the field Robin criterion.
-/

open UniqueFactorizationMonoid

namespace RobinBV.NumberField

noncomputable section

/-- A pointwise logarithmic defect bound at the critical scale yields an
additive square-root correction. -/
theorem exp_logDefect_le_add_criticalCorrection
    {a kappa H coefficient : Real}
    (ha : 0 < a) (hKappa : 0 < kappa) (hH : 1 < H)
    (hCoefficient : 0 <= coefficient)
    (hSmall :
      coefficient / (Real.sqrt H * Real.log H) <= 1)
    (hDefect :
      Real.log a - Real.eulerMascheroniConstant - Real.log kappa -
          Real.log (Real.log H) <=
        coefficient / (Real.sqrt H * Real.log H)) :
    a <=
      Real.exp Real.eulerMascheroniConstant * kappa * Real.log H +
        2 * Real.exp Real.eulerMascheroniConstant * kappa * coefficient /
          Real.sqrt H := by
  let u := coefficient / (Real.sqrt H * Real.log H)
  let base :=
    Real.exp Real.eulerMascheroniConstant * kappa * Real.log H
  have hSqrt : 0 < Real.sqrt H :=
    Real.sqrt_pos.2 (lt_trans (by norm_num) hH)
  have hLogH : 0 < Real.log H := Real.log_pos hH
  have hDenominator : 0 < Real.sqrt H * Real.log H :=
    mul_pos hSqrt hLogH
  have hUNonneg : 0 <= u := by
    exact div_nonneg hCoefficient (le_of_lt hDenominator)
  have hULe : u <= 1 := by
    exact hSmall
  have hLogBound :
      Real.log a <=
        Real.eulerMascheroniConstant + Real.log kappa +
          Real.log (Real.log H) + u := by
    dsimp [u]
    linarith
  have hExponential : a <= base * Real.exp u := by
    calc
      a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ <= Real.exp
          (Real.eulerMascheroniConstant + Real.log kappa +
            Real.log (Real.log H) + u) :=
        Real.exp_le_exp.mpr hLogBound
      _ = base * Real.exp u := by
        dsimp [base]
        rw [Real.exp_add, Real.exp_add, Real.exp_add,
          Real.exp_log hKappa, Real.exp_log hLogH]
  have hAbsU : abs u <= 1 := by
    rw [abs_of_nonneg hUNonneg]
    exact hULe
  have hTaylor := Real.abs_exp_sub_one_le hAbsU
  have hOneLeExp : 1 <= Real.exp u := Real.one_le_exp hUNonneg
  have hExpBound : Real.exp u <= 1 + 2 * u := by
    rw [abs_of_nonneg (sub_nonneg.mpr hOneLeExp),
      abs_of_nonneg hUNonneg] at hTaylor
    linarith
  have hBaseNonneg : 0 <= base := by
    dsimp [base]
    positivity
  have hMultiplied : base * Real.exp u <= base * (1 + 2 * u) :=
    mul_le_mul_of_nonneg_left hExpBound hBaseNonneg
  have hIdentity :
      base * (1 + 2 * u) =
        base +
          2 * Real.exp Real.eulerMascheroniConstant * kappa * coefficient /
            Real.sqrt H := by
    dsimp [base, u]
    field_simp [ne_of_gt hSqrt, ne_of_gt hLogH]
  exact hExponential.trans (hMultiplied.trans_eq hIdentity)

theorem idealAbundancy_pos
    {K : Type*} [Field K] [NumberField K]
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) :
    0 < idealAbundancy K I := by
  rw [idealAbundancy_eq_prod_local]
  apply Finset.prod_pos
  intro P hP
  have hPrime : Prime P.val :=
    prime_of_normalized_factor P.val
      (Multiset.mem_toFinset.mp P.property)
  have hNormNat : 0 < Ideal.absNorm P.val :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      (Subtype.mk P.val
        (mem_nonZeroDivisors_iff_ne_zero.mpr hPrime.ne_zero))
  have hNorm : 0 < (Ideal.absNorm P.val : Real) := by
    exact_mod_cast hNormNat
  apply div_pos
  next =>
    apply Finset.sum_pos'
    next =>
      intro j hj
      positivity
    next =>
      exact Exists.intro 0
        (And.intro (Finset.mem_univ 0) (by simp))
  next => positivity

variable (K : Type*) [Field K] [NumberField K]

theorem criticalScaleIdealRobinBound_of_eventualLogDefect
    {kappa coefficient : Real} (hKappa : 0 < kappa)
    (hCoefficient : 0 <= coefficient)
    (hBound : EventualIdealRobinLogDefectBound K kappa coefficient) :
    CriticalScaleIdealRobinBound K kappa := by
  choose X hX using hBound
  let baseCorrection :=
    2 * Real.exp Real.eulerMascheroniConstant * kappa * coefficient
  let correction := baseCorrection + 1
  apply Exists.intro correction
  apply And.intro
  next =>
    dsimp [correction, baseCorrection]
    positivity
  next =>
    unfold EventualIdealRobinBoundWithCriticalCorrection
    apply Exists.intro X
    intro I hLarge
    have hData := hX I hLarge
    let normValue : Real :=
      Ideal.absNorm
        (I : Ideal (_root_.NumberField.RingOfIntegers K))
    let H : Real := Real.log normValue
    have hNormNat : 0 < Ideal.absNorm
        (I : Ideal (_root_.NumberField.RingOfIntegers K)) :=
      Ideal.absNorm_pos_of_nonZeroDivisors I
    have hNorm : 0 < normValue := by
      dsimp [normValue]
      exact_mod_cast hNormNat
    have hH : 1 < H := by
      simpa [H, normValue] using hData.1
    have hSmall : coefficient / (Real.sqrt H * Real.log H) <= 1 := by
      simpa [H, normValue] using hData.2.1
    have hDefect :
        Real.log (idealAbundancy K I) -
              Real.eulerMascheroniConstant - Real.log kappa -
              Real.log (Real.log H) <=
            coefficient / (Real.sqrt H * Real.log H) := by
      simpa [H, normValue] using hData.2.2
    have hPointwise :=
      exp_logDefect_le_add_criticalCorrection
        (idealAbundancy_pos I) hKappa hH hCoefficient hSmall hDefect
    have hSqrt : 0 < Real.sqrt H :=
      Real.sqrt_pos.2 (lt_trans (by norm_num) hH)
    have hGap : baseCorrection / Real.sqrt H <
        correction / Real.sqrt H := by
      apply (div_lt_div_iff_of_pos_right hSqrt).2
      dsimp [correction]
      linarith
    have hAbundancy :
        idealAbundancy K I <
          Real.exp Real.eulerMascheroniConstant * kappa * Real.log H +
            correction / Real.sqrt H := by
      apply lt_of_le_of_lt hPointwise
      dsimp [baseCorrection] at hGap
      linarith
    have hMultiplied := mul_lt_mul_of_pos_right hAbundancy hNorm
    calc
      (idealDivisorSum K I : Real) = idealAbundancy K I * normValue := by
        dsimp [normValue]
        unfold idealAbundancy
        field_simp [ne_of_gt hNorm]
      _ <
          (Real.exp Real.eulerMascheroniConstant * kappa * Real.log H +
            correction / Real.sqrt H) * normValue := hMultiplied
      _ =
          Real.exp Real.eulerMascheroniConstant * kappa *
              Ideal.absNorm
                (I : Ideal (_root_.NumberField.RingOfIntegers K)) *
              Real.log (Real.log (Ideal.absNorm
                (I : Ideal (_root_.NumberField.RingOfIntegers K)) : Real)) +
            correction * Ideal.absNorm
              (I : Ideal (_root_.NumberField.RingOfIntegers K)) /
                Real.sqrt (Real.log (Ideal.absNorm
                  (I : Ideal (_root_.NumberField.RingOfIntegers K)) : Real)) := by
        dsimp [H, normValue]
        ring

end

end RobinBV.NumberField
