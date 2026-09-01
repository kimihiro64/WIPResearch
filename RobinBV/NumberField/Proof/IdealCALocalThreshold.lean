import RobinBV.NumberField.Proof.IdealCAObjective

/-!
# Local exponent thresholds for ideal CA objectives

Consecutive norm-local factors differ by an explicit positive multiplier.
The multiplier determines strict increase, equality, and weak decrease of the
local objective without any analytic assumption on `epsilon`.
-/

namespace RobinBV.NumberField

theorem idealCALocalFactor_pos
    (epsilon : Real) {q : Nat} (hq : 0 < q) (e : Nat) :
    0 < idealCALocalFactor epsilon q e := by
  unfold idealCALocalFactor
  positivity

theorem idealCALocalStepRatio_pos
    (epsilon : Real) {q : Nat} (hq : 0 < q) (e : Nat) :
    0 < idealCALocalStepRatio epsilon q e := by
  unfold idealCALocalStepRatio
  positivity

/-- Prime ideals with the same absolute norm have the same local exponent
transition ratio. -/
theorem idealCALocalStepRatio_eq_of_absNorm_eq
    {K : Type*} [Field K] [NumberField K]
    (epsilon : Real)
    {P Q : Ideal (_root_.NumberField.RingOfIntegers K)}
    (hNorm : Ideal.absNorm P = Ideal.absNorm Q)
    (e : Nat) :
    idealCALocalStepRatio epsilon (Ideal.absNorm P) e =
      idealCALocalStepRatio epsilon (Ideal.absNorm Q) e := by
  rw [hNorm]

/-- Exact one-step recurrence for the norm-local CA factor. -/
theorem idealCALocalFactor_succ_eq_mul_stepRatio
    (epsilon : Real) {q : Nat} (hq : 0 < q) (e : Nat) :
    idealCALocalFactor epsilon q (e + 1) =
      idealCALocalFactor epsilon q e *
        idealCALocalStepRatio epsilon q e := by
  unfold idealCALocalFactor idealCALocalStepRatio
  have hqReal : 0 < (q : Real) := by
    exact_mod_cast hq
  have hsum : 0 <
      (Finset.univ.sum fun j : Fin (e + 1) => (q : Real) ^ j.val) := by
    positivity
  have hqPow : 0 <= (q : Real) ^ e := by
    positivity
  rw [pow_succ]
  rw [Real.mul_rpow hqPow hqReal.le]
  rw [Real.rpow_add hqReal, Real.rpow_one]
  field_simp

/-- The local factor increases exactly when its step ratio exceeds one. -/
theorem idealCALocalFactor_lt_succ_iff_stepRatio_one_lt
    (epsilon : Real) {q : Nat} (hq : 0 < q) (e : Nat) :
    idealCALocalFactor epsilon q e <
        idealCALocalFactor epsilon q (e + 1) <->
      1 < idealCALocalStepRatio epsilon q e := by
  rw [idealCALocalFactor_succ_eq_mul_stepRatio epsilon hq e]
  have hpos := idealCALocalFactor_pos epsilon hq e
  simpa only [mul_one] using (mul_lt_mul_iff_of_pos_left hpos :
    (idealCALocalFactor epsilon q e * 1 <
        idealCALocalFactor epsilon q e *
          idealCALocalStepRatio epsilon q e <->
      1 < idealCALocalStepRatio epsilon q e))

/-- Consecutive local factors tie exactly when the step ratio is one. -/
theorem idealCALocalFactor_succ_eq_iff_stepRatio_eq_one
    (epsilon : Real) {q : Nat} (hq : 0 < q) (e : Nat) :
    idealCALocalFactor epsilon q (e + 1) =
        idealCALocalFactor epsilon q e <->
      idealCALocalStepRatio epsilon q e = 1 := by
  rw [idealCALocalFactor_succ_eq_mul_stepRatio epsilon hq e]
  have hpos := idealCALocalFactor_pos epsilon hq e
  simpa only [mul_one] using (mul_left_cancel_iff_of_pos hpos :
    (idealCALocalFactor epsilon q e *
          idealCALocalStepRatio epsilon q e =
        idealCALocalFactor epsilon q e * 1 <->
      idealCALocalStepRatio epsilon q e = 1))

/-- The next local factor is no larger exactly when the step ratio is at most
one. -/
theorem idealCALocalFactor_succ_le_iff_stepRatio_le_one
    (epsilon : Real) {q : Nat} (hq : 0 < q) (e : Nat) :
    idealCALocalFactor epsilon q (e + 1) <=
        idealCALocalFactor epsilon q e <->
      idealCALocalStepRatio epsilon q e <= 1 := by
  rw [idealCALocalFactor_succ_eq_mul_stepRatio epsilon hq e]
  have hpos := idealCALocalFactor_pos epsilon hq e
  simpa only [mul_one] using (mul_le_mul_iff_of_pos_left hpos :
    (idealCALocalFactor epsilon q e *
          idealCALocalStepRatio epsilon q e <=
        idealCALocalFactor epsilon q e * 1 <->
      idealCALocalStepRatio epsilon q e <= 1))

end RobinBV.NumberField
