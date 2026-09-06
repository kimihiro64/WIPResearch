import RobinBV.Mathlib.NumberTheory.MulChar.PositivePacket
import RobinBV.NumberField.Proof.MovingCharacterPacketIntegrals

/-!
# Exact squared-norm tails and negative character kernels

The pair-character arithmetic correction is a complete negative integral
of squared norms. Realness and nonpositivity hold for arbitrary complex
coefficients, without an assumed residue sign or any RH hypothesis.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- The actual arithmetic quadratic form on a finite character family. -/
def squaredCharacterPacketPrefix {N : Nat} [NeZero N] {I : Type*}
    (s : Finset I) (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (m P : Nat) : Complex :=
  centeredCharacterPacketPrefix (s.product s)
    (MulChar.normSquarePacketCharacter chi) (MulChar.normSquarePacketWeight c) m P

/-- Every admitted prime/exponent contributes exactly a full squared norm
to the pair-character higher-power step. -/
theorem squaredCharacterPacketHigherStep_eq
    {N : Nat} [NeZero N] {I : Type*}
    (s : Finset I) (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (P m : Nat) (t : Real) :
    characterPacketHigherStep (s.product s)
      (MulChar.normSquarePacketCharacter chi) (MulChar.normSquarePacketWeight c) P m t =
    (Nat.primesLE P).sum (fun p => (Real.log p : Complex) *
      (Finset.Icc (m+1) (Nat.log p (Nat.floor t))).sum (fun j =>
        ((norm (s.sum (fun i => c i * (chi i (p : ZMod N))^j)))^2 : Real))) := by
  unfold characterPacketHigherStep DirichletCharacter.primePowerHigherStep
  simp only [Complex.ofReal_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hJ : Not (j = 0) := by
    have hLow := (Finset.mem_Icc.mp hj).1
    omega
  rw [<- MulChar.sum_normSquarePacket_value_pow_eq s chi c j hJ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  ring

/-- The complete squared-norm integral representation of the actual
arithmetic quadratic form, with every higher prime power retained. -/
theorem squaredCharacterPacketPrefix_eq_neg_integral
    {N : Nat} [NeZero N] {I : Type*}
    (s : Finset I) (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (P m : Nat) (hm : 1 <= m) (hx : 3 <= (P : Real)^m) :
    squaredCharacterPacketPrefix s chi c m P =
      -integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
        ((Nat.primesLE P).sum (fun p => (Real.log p : Complex) *
          (Finset.Icc (m+1) (Nat.log p (Nat.floor t))).sum (fun j =>
            ((norm (s.sum (fun i => c i * (chi i (p : ZMod N))^j)))^2 : Real)))) *
          (Robin1984.robinRealWeight 1 t : Complex)) := by
  rw [squaredCharacterPacketPrefix, centeredCharacterPacketPrefix_eq_neg_integral
    _ _ _ P m hm hx]
  simp only [squaredCharacterPacketHigherStep_eq]

/-- The actual arithmetic quadratic form is real for arbitrary complex
coefficients, derived from the complete absolutely integrable tail. -/
theorem squaredCharacterPacketPrefix_im_eq_zero
    {N : Nat} [NeZero N] {I : Type*}
    (s : Finset I) (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (P m : Nat) (hm : 1 <= m) (hx : 3 <= (P : Real)^m) :
    (squaredCharacterPacketPrefix s chi c m P).im = 0 := by
  let f (t : Real) : Complex :=
    characterPacketHigherStep (s.product s)
      (MulChar.normSquarePacketCharacter chi) (MulChar.normSquarePacketWeight c) P m t *
        (Robin1984.robinRealWeight 1 t : Complex)
  have hInt : IntegrableOn f (Ioi ((P : Real)^m)) :=
    characterPacketHigherStep_integrable _ _ _ P m hm (by linarith)
  have hIm : (fun t : Real => (f t).im) = fun _ => (0 : Real) := by
    funext t
    dsimp only [f]
    rw [squaredCharacterPacketHigherStep_eq]
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.im_sum,
      mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  have h := Complex.imCLM.integral_comp_comm hInt
  change integral (volume.restrict (Ioi ((P : Real)^m))) (fun t => (f t).im) =
    (integral (volume.restrict (Ioi ((P : Real)^m))) f).im at h
  rw [hIm, integral_zero] at h
  rw [squaredCharacterPacketPrefix, centeredCharacterPacketPrefix_eq_neg_integral
    _ _ _ P m hm hx, Complex.neg_im]
  change -(integral (volume.restrict (Ioi ((P : Real)^m))) f).im = 0
  rw [<- h, neg_zero]

/-- The actual correction kernel is negative semidefinite: its quadratic
form is nonpositive for every finite family and every complex coefficient. -/
theorem squaredCharacterPacketPrefix_re_nonpos
    {N : Nat} [NeZero N] {I : Type*}
    (s : Finset I) (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (P m : Nat) (hm : 1 <= m) (hx : 3 <= (P : Real)^m) :
    (squaredCharacterPacketPrefix s chi c m P).re <= 0 := by
  apply centeredCharacterPacketPrefix_re_nonpos_of_residue_nonneg
    _ _ _ _ P m hm hx
  intro a
  simpa only [pow_one] using MulChar.sum_normSquarePacket_pow_re_nonneg s chi c 1 a

end

end RobinBV.NumberField
