import RobinBV.NumberField.Proof.MovingCharacterPacketCancellation

/-!
# Complete higher-power integrals of finite character packets

Every prime and every admitted exponent is retained. The positivity input
below is a finite residue-weight condition, not an analytic estimate.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- Complete higher-power step of a finite weighted character packet. -/
def characterPacketHigherStep {N : Nat} {I : Type*} (s : Finset I)
    (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (P m : Nat) (t : Real) : Complex :=
  s.sum (fun i => c i *
    (Nat.primesLE P).sum (fun p => (chi i).primePowerHigherStep p m t))

/-- Pointwise positivity on residues implies positivity of every complete
higher-power step, by evaluation at the corresponding residue powers. -/
theorem characterPacketHigherStep_re_nonneg
    {N : Nat} {I : Type*} (s : Finset I)
    (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (hPos : forall a : ZMod N, 0 <= (s.sum (fun i => c i * chi i a)).re)
    (P m : Nat) (t : Real) :
    0 <= (characterPacketHigherStep s chi c P m t).re := by
  have hExpand : characterPacketHigherStep s chi c P m t =
      (Nat.primesLE P).sum (fun p => (Real.log p : Complex) *
        (Finset.Icc (m+1) (Nat.log p (Nat.floor t))).sum (fun j =>
          s.sum (fun i => c i * (chi i (p : ZMod N))^j))) := by
    unfold characterPacketHigherStep DirichletCharacter.primePowerHigherStep
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hExpand, Complex.re_sum]
  apply Finset.sum_nonneg
  intro p hp
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro j hj
  simpa only [map_pow] using hPos ((p : ZMod N)^j)

private theorem characterPacketHigherStep_weight_eq
    {N : Nat} {I : Type*} (s : Finset I)
    (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (P m : Nat) (t : Real) :
    characterPacketHigherStep s chi c P m t*(Robin1984.robinRealWeight 1 t : Complex) =
      s.sum (fun i => c i *
        ((Nat.primesLE P).sum (fun p => (chi i).primePowerHigherStep p m t) *
          (Robin1984.robinRealWeight 1 t : Complex))) := by
  unfold characterPacketHigherStep
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Absolute integrability of the entire finite weighted character packet. -/
theorem characterPacketHigherStep_integrable
    {N : Nat} {I : Type*} (s : Finset I)
    (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (P m : Nat) (hm : 1 <= m) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real =>
      characterPacketHigherStep s chi c P m t*
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
  have hEach (i : I) : IntegrableOn (fun t : Real => c i *
      ((Nat.primesLE P).sum (fun p => (chi i).primePowerHigherStep p m t) *
        (Robin1984.robinRealWeight 1 t : Complex))) (Ioi x) :=
    (higherCharacterPrimePower_integral_data (chi i) P m hm hx).1.const_mul _
  have h := integrable_finsetSum s (fun i _ => hEach i)
  apply h.congr
  exact Filter.Eventually.of_forall (fun t =>
    (characterPacketHigherStep_weight_eq s chi c P m t).symm)

/-- Exact full-tail representation of the actual finite character prefix. -/
theorem centeredCharacterPacketPrefix_eq_neg_integral
    {N : Nat} [NeZero N] {I : Type*} (s : Finset I)
    (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (P m : Nat) (hm : 1 <= m) (hx : 3 <= (P : Real)^m) :
    centeredCharacterPacketPrefix s chi c m P =
      -integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
        characterPacketHigherStep s chi c P m t*
          (Robin1984.robinRealWeight 1 t : Complex)) := by
  have hxOne : 1 < (P : Real)^m := by linarith
  have hEach (i : I) : centeredCharacterPrefix (chi i) m P =
      -integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
        (Nat.primesLE P).sum (fun p => (chi i).primePowerHigherStep p m t) *
          (Robin1984.robinRealWeight 1 t : Complex)) := by
    have h := movingCharacterCorrection_prefix_eq_higher_integral
      (chi i) P m hm hx (by simp only [Nat.cast_pow]; exact le_rfl)
    dsimp only [centeredCharacterPrefix]
    rw [centeredCharacterWeightedIntegral_changeLevel_primorial_sub _ P hx]
    simpa only [Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc] using h
  have hInt (i : I) : IntegrableOn (fun t : Real => c i *
      ((Nat.primesLE P).sum (fun p => (chi i).primePowerHigherStep p m t) *
        (Robin1984.robinRealWeight 1 t : Complex))) (Ioi ((P : Real)^m)) :=
    (higherCharacterPrimePower_integral_data (chi i) P m hm hxOne).1.const_mul _
  have hFinite : integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
      characterPacketHigherStep s chi c P m t*(Robin1984.robinRealWeight 1 t : Complex)) =
      s.sum (fun i => c i * integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
        (Nat.primesLE P).sum (fun p => (chi i).primePowerHigherStep p m t) *
          (Robin1984.robinRealWeight 1 t : Complex))) := by
    have hFunction : (fun t : Real =>
        characterPacketHigherStep s chi c P m t*(Robin1984.robinRealWeight 1 t : Complex)) =
        (fun t : Real => s.sum (fun i => c i *
          ((Nat.primesLE P).sum (fun p => (chi i).primePowerHigherStep p m t) *
            (Robin1984.robinRealWeight 1 t : Complex)))) :=
      funext (characterPacketHigherStep_weight_eq s chi c P m)
    rw [hFunction, integral_finsetSum _ (fun i _ => hInt i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_const_mul _ _
  simp only [centeredCharacterPacketPrefix, hEach, mul_neg, Finset.sum_neg_distrib]
  rw [<- hFinite]

/-- A finite nonnegative residue filter gives a nonpositive real arithmetic
prefix through its complete higher-power integral. -/
theorem centeredCharacterPacketPrefix_re_nonpos_of_residue_nonneg
    {N : Nat} [NeZero N] {I : Type*} (s : Finset I)
    (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (hPos : forall a : ZMod N, 0 <= (s.sum (fun i => c i * chi i a)).re)
    (P m : Nat) (hm : 1 <= m) (hx : 3 <= (P : Real)^m) :
    (centeredCharacterPacketPrefix s chi c m P).re <= 0 := by
  have hInt := characterPacketHigherStep_integrable s chi c P m hm
    (by linarith : 1 < (P : Real)^m)
  have hRe : (integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
      characterPacketHigherStep s chi c P m t*(Robin1984.robinRealWeight 1 t : Complex))).re =
      integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
        (characterPacketHigherStep s chi c P m t*(Robin1984.robinRealWeight 1 t : Complex)).re) :=
    (Complex.reCLM.integral_comp_comm hInt).symm
  rw [centeredCharacterPacketPrefix_eq_neg_integral s chi c P m hm hx, Complex.neg_re, hRe]
  apply neg_nonpos.mpr
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (characterPacketHigherStep_re_nonneg s chi c hPos P m t)
    (Robin1984.robinRealWeight_nonneg (n := 1) ((by linarith : 1 < (P : Real)^m).trans ht))

end

end RobinBV.NumberField
