import RobinBV.NumberField.Proof.OrderSixPacketPositivity

/-!
# Complete integral sign of the positive sixth-order character filter

Every admitted higher prime power remains in the finite step, and every
integration is over the complete infinite tail with proved integrability.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- Complete higher-power step of the actual four-character packet. -/
def orderSixPacketHigherStep {N : Nat} (chi : DirichletCharacter Complex N)
    (P m : Nat) (t : Real) : Complex :=
  (Finset.univ : Finset (Fin 4)).sum (fun i => orderSixPacketWeights i *
    (Nat.primesLE P).sum (fun p => (orderSixPacketCharacters chi i).primePowerHigherStep p m t))

/-- Every complete higher step has nonnegative real part; the prime and
exponent sums are rearranged finitely, with no omitted powers. -/
theorem orderSixPacketHigherStep_re_nonneg
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hSix : chi^6=1)
    (P m : Nat) (t : Real) : 0 <= (orderSixPacketHigherStep chi P m t).re := by
  have hExpand : orderSixPacketHigherStep chi P m t =
      (Nat.primesLE P).sum (fun p => (Real.log p : Complex) *
        (Finset.Icc (m+1) (Nat.log p (Nat.floor t))).sum (fun j =>
          (Finset.univ : Finset (Fin 4)).sum (fun i => orderSixPacketWeights i *
            (orderSixPacketCharacters chi i (p : ZMod N))^j))) := by
    unfold orderSixPacketHigherStep DirichletCharacter.primePowerHigherStep
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
  exact orderSixPacket_powerSum_re_nonneg chi hSix j
    (by have hLow := (Finset.mem_Icc.mp hj).1; omega) (p : ZMod N)

private theorem orderSixPacketHigherStep_weight_eq
    {N : Nat} (chi : DirichletCharacter Complex N) (P m : Nat) (t : Real) :
    orderSixPacketHigherStep chi P m t*(Robin1984.robinRealWeight 1 t : Complex) =
      (Finset.univ : Finset (Fin 4)).sum (fun i => orderSixPacketWeights i *
        ((Nat.primesLE P).sum (fun p => (orderSixPacketCharacters chi i).primePowerHigherStep p m t) *
          (Robin1984.robinRealWeight 1 t : Complex))) := by
  unfold orderSixPacketHigherStep
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Absolute integrability of the entire weighted packet, from the actual
full higher-power providers for each of its four characters. -/
theorem orderSixPacketHigherStep_integrable
    {N : Nat} (chi : DirichletCharacter Complex N) (P m : Nat) (hm : 1 <= m)
    {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real =>
      orderSixPacketHigherStep chi P m t*(Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
  have hEach (i : Fin 4) : IntegrableOn (fun t : Real => orderSixPacketWeights i *
      ((Nat.primesLE P).sum (fun p => (orderSixPacketCharacters chi i).primePowerHigherStep p m t) *
        (Robin1984.robinRealWeight 1 t : Complex))) (Ioi x) :=
    (higherCharacterPrimePower_integral_data (orderSixPacketCharacters chi i) P m hm hx).1.const_mul _
  have h := integrable_finsetSum (Finset.univ : Finset (Fin 4)) (fun i _ => hEach i)
  apply h.congr
  exact Filter.Eventually.of_forall (fun t => (orderSixPacketHigherStep_weight_eq chi P m t).symm)

/-- Exact full-tail representation of the actual finite character packet
prefix. No limiting argument or sign assumption enters this identity. -/
theorem orderSixPacketPrefix_eq_neg_integral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (P m : Nat) (hm : 1 <= m)
    (hx : 3 <= (P : Real)^m) :
    centeredCharacterPacketPrefix (Finset.univ : Finset (Fin 4))
      (orderSixPacketCharacters chi) orderSixPacketWeights m P =
      -integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
        orderSixPacketHigherStep chi P m t*(Robin1984.robinRealWeight 1 t : Complex)) := by
  have hxOne : 1 < (P : Real)^m := by linarith
  have hEach (i : Fin 4) : centeredCharacterPrefix (orderSixPacketCharacters chi i) m P =
      -integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
        (Nat.primesLE P).sum (fun p => (orderSixPacketCharacters chi i).primePowerHigherStep p m t) *
          (Robin1984.robinRealWeight 1 t : Complex)) := by
    have h := movingCharacterCorrection_prefix_eq_higher_integral
      (orderSixPacketCharacters chi i) P m hm hx (by simp only [Nat.cast_pow]; exact le_rfl)
    dsimp only [centeredCharacterPrefix]
    rw [centeredCharacterWeightedIntegral_changeLevel_primorial_sub _ P hx]
    simpa only [Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc] using h
  have hInt (i : Fin 4) : IntegrableOn (fun t : Real => orderSixPacketWeights i *
      ((Nat.primesLE P).sum (fun p => (orderSixPacketCharacters chi i).primePowerHigherStep p m t) *
        (Robin1984.robinRealWeight 1 t : Complex))) (Ioi ((P : Real)^m)) :=
    (higherCharacterPrimePower_integral_data (orderSixPacketCharacters chi i) P m hm hxOne).1.const_mul _
  have hFinite : integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
      orderSixPacketHigherStep chi P m t*(Robin1984.robinRealWeight 1 t : Complex)) =
      (Finset.univ : Finset (Fin 4)).sum (fun i => orderSixPacketWeights i *
        integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
          (Nat.primesLE P).sum (fun p => (orderSixPacketCharacters chi i).primePowerHigherStep p m t) *
            (Robin1984.robinRealWeight 1 t : Complex))) := by
    have hFunction : (fun t : Real =>
        orderSixPacketHigherStep chi P m t*(Robin1984.robinRealWeight 1 t : Complex)) =
        (fun t : Real => (Finset.univ : Finset (Fin 4)).sum (fun i => orderSixPacketWeights i *
          ((Nat.primesLE P).sum (fun p => (orderSixPacketCharacters chi i).primePowerHigherStep p m t) *
            (Robin1984.robinRealWeight 1 t : Complex)))) :=
      funext (orderSixPacketHigherStep_weight_eq chi P m)
    rw [hFunction, integral_finsetSum _ (fun i _ => hInt i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_const_mul _ _
  simp only [centeredCharacterPacketPrefix, hEach, mul_neg, Finset.sum_neg_distrib]
  rw [<- hFinite]

/-- The actual packet prefix has nonpositive real part at every admissible
cutoff, from the full positive higher-power integral, without RH or ERH. -/
theorem orderSixPacketPrefix_re_nonpos
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hSix : chi^6=1)
    (P m : Nat) (hm : 1 <= m) (hx : 3 <= (P : Real)^m) :
    (centeredCharacterPacketPrefix (Finset.univ : Finset (Fin 4))
      (orderSixPacketCharacters chi) orderSixPacketWeights m P).re <= 0 := by
  have hInt := orderSixPacketHigherStep_integrable chi P m hm (by linarith : 1 < (P : Real)^m)
  have hRe : (integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
      orderSixPacketHigherStep chi P m t*(Robin1984.robinRealWeight 1 t : Complex))).re =
      integral (volume.restrict (Ioi ((P : Real)^m))) (fun t : Real =>
        (orderSixPacketHigherStep chi P m t*(Robin1984.robinRealWeight 1 t : Complex)).re) :=
    (Complex.reCLM.integral_comp_comm hInt).symm
  rw [orderSixPacketPrefix_eq_neg_integral chi P m hm hx, Complex.neg_re, hRe]
  apply neg_nonpos.mpr
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (orderSixPacketHigherStep_re_nonneg chi hSix P m t)
    (Robin1984.robinRealWeight_nonneg (n := 1) ((by linarith : 1 < (P : Real)^m).trans ht))

end

end RobinBV.NumberField
