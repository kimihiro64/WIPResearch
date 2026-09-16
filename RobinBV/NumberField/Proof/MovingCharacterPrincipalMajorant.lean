import RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimePowerPrincipalMajorant
import RobinBV.NumberField.Proof.MovingCharacterPacketIntegrals

/-!
# Exact principal majorization of actual arithmetic corrections

The comparison retains the complete same-modulus principal correction,
including both integral levels, every finite moment and conductor exclusion.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- The exact single-character prefix is its negative full higher-power
integral, with the entire finite moment already centered. -/
theorem centeredCharacterPrefix_eq_neg_integral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (P m : Nat) (hm : 1 <= m) (hx : 3 <= (P : Real)^m) :
    centeredCharacterPrefix chi m P =
      -integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
        (Nat.primesLE P).sum (fun p => chi.primePowerHigherStep p m t) *
          (Robin1984.robinRealWeight 1 t : Complex)) := by
  simpa only [centeredCharacterPacketPrefix, characterPacketHigherStep,
    Finset.sum_singleton, one_mul] using
      centeredCharacterPacketPrefix_eq_neg_integral ({()} : Finset Unit)
        (fun _ => chi) (fun _ => (1 : Complex)) P m hm hx

/-- Every actual character correction is bounded by the exact negative
real principal correction, without RH/ERH or a coarse root-log replacement. -/
theorem norm_centeredCharacterPrefix_le_neg_principal_re
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (P m : Nat) (hm : 1 <= m) (hx : 3 <= (P : Real)^m) :
    norm (centeredCharacterPrefix chi m P) <=
      -(centeredCharacterPrefix (1 : DirichletCharacter Complex N) m P).re := by
  have hxOne : 1 < (P : Real)^m := by linarith
  let fChi (t : Real) : Complex :=
    (Nat.primesLE P).sum (fun p => chi.primePowerHigherStep p m t) *
      (Robin1984.robinRealWeight 1 t : Complex)
  let fOne (t : Real) : Complex :=
    (Nat.primesLE P).sum (fun p =>
      (1 : DirichletCharacter Complex N).primePowerHigherStep p m t) *
        (Robin1984.robinRealWeight 1 t : Complex)
  have hInt : IntegrableOn fOne (Ioi ((P : Real)^m)) :=
    (higherCharacterPrimePower_integral_data
      (1 : DirichletCharacter Complex N) P m hm hxOne).1
  have hMajor : IntegrableOn (fun t => (fOne t).re) (Ioi ((P : Real)^m)) :=
    Complex.reCLM.integrable_comp hInt
  have hBound : Filter.Eventually (fun t : Real => norm (fChi t) <= (fOne t).re)
      (ae (volume.restrict (Ioi ((P : Real)^m)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hWeight := Robin1984.robinRealWeight_nonneg (n := 1) (hxOne.trans ht)
    dsimp only [fChi, fOne]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeight,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_right
      (chi.norm_sum_primePowerHigherStep_le_principal_re P m t) hWeight
  have h := norm_integral_le_of_norm_le hMajor hBound
  have hRe : integral (volume.restrict (Ioi ((P : Real)^m))) (fun t => (fOne t).re) =
      (integral (volume.restrict (Ioi ((P : Real)^m))) fOne).re :=
    Complex.reCLM.integral_comp_comm hInt
  rw [hRe] at h
  rw [centeredCharacterPrefix_eq_neg_integral chi P m hm hx, norm_neg,
    centeredCharacterPrefix_eq_neg_integral 1 P m hm hx, Complex.neg_re, neg_neg]
  exact h

/-- The exact principal correction has norm equal to its negative real part. -/
theorem principal_centeredCharacterPrefix_norm_eq_neg_re
    (N : Nat) [NeZero N] (P m : Nat) (hm : 1 <= m) (hx : 3 <= (P : Real)^m) :
    norm (centeredCharacterPrefix (1 : DirichletCharacter Complex N) m P) =
      -(centeredCharacterPrefix (1 : DirichletCharacter Complex N) m P).re := by
  apply le_antisymm (norm_centeredCharacterPrefix_le_neg_principal_re 1 P m hm hx)
  simpa only [Complex.neg_re, norm_neg] using
    Complex.re_le_norm (-centeredCharacterPrefix (1 : DirichletCharacter Complex N) m P)

/-- The exact same-modulus principal correction majorizes every actual
character correction in norm at every admissible cutoff. -/
theorem norm_centeredCharacterPrefix_le_principal_norm
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (P m : Nat) (hm : 1 <= m) (hx : 3 <= (P : Real)^m) :
    norm (centeredCharacterPrefix chi m P) <=
      norm (centeredCharacterPrefix (1 : DirichletCharacter Complex N) m P) := by
  rw [principal_centeredCharacterPrefix_norm_eq_neg_re N P m hm hx]
  exact norm_centeredCharacterPrefix_le_neg_principal_re chi P m hm hx

end

end RobinBV.NumberField
