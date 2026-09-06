import RobinBV.NumberField.Proof.OrderSixCharacterPacket

/-!
# Exact positive values of the sixth-order character packet

The real weights come from proved norm-square and idempotent identities.
Nonunits are treated by their actual zero character values.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter
open scoped Classical

noncomputable section

/-- The actual four-character packet evaluated on a residue. -/
def orderSixPacketValue {N : Nat} (chi : DirichletCharacter Complex N) (a : ZMod N) : Complex :=
  (Finset.univ : Finset (Fin 4)).sum (fun i =>
    orderSixPacketWeights i * orderSixPacketCharacters chi i a)

/-- Every character, including principal, vanishes at a nonunit. -/
theorem orderSixPacketValue_eq_zero_of_nonunit
    {N : Nat} (chi : DirichletCharacter Complex N) {a : ZMod N} (ha : Not (IsUnit a)) :
    orderSixPacketValue chi a=0 := by
  unfold orderSixPacketValue
  apply Finset.sum_eq_zero
  intro i hi
  rw [MulChar.map_nonunit _ ha, mul_zero]

/-- At units the actual packet equals its ordinary sixth-root polynomial. -/
theorem orderSixPacketValue_eq_polynomial_of_isUnit
    {N : Nat} (chi : DirichletCharacter Complex N) {a : ZMod N} (ha : IsUnit a) :
    orderSixPacketValue chi a=1-(chi a)^2-(chi a)^3+(chi a)^5 := by
  simp [orderSixPacketValue, Fin.sum_univ_succ, orderSixPacketCharacters, orderSixPacketWeights,
    MulChar.one_apply ha, MulChar.pow_apply' chi (by decide : Not ((2 : Nat)=0)) a,
    MulChar.pow_apply' chi (by decide : Not ((3 : Nat)=0)) a,
    MulChar.pow_apply' chi (by decide : Not ((5 : Nat)=0)) a, sub_eq_add_neg, add_assoc]

private theorem orderSixPacket_unit_data
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hSix : chi^6=1)
    {a : ZMod N} (ha : IsUnit a) :
    And ((chi a)^6=1)
      (And (orderSixPacketValue chi a=1-(chi a)^2-(chi a)^3+(chi a)^5)
        (star (orderSixPacketValue chi a)=1-(chi a)^4-(chi a)^3+chi a)) := by
  have hz : (chi a)^6=1 := by
    have h := congrArg (fun psi : DirichletCharacter Complex N => psi a) hSix
    rw [MulChar.pow_apply' chi (by decide : Not ((6 : Nat)=0)) a, MulChar.one_apply ha] at h
    exact h
  have hInv : Inv.inv chi=chi^5 := inv_eq_of_mul_eq_one_left (by rw [<- pow_succ, hSix])
  have hStar : star (chi a)=(chi a)^5 := by
    rw [MulChar.star_apply', hInv, MulChar.pow_apply' chi (by decide : Not ((5 : Nat)=0)) a]
  have hPeriod (k r : Nat) : (chi a)^(6*k+r)=(chi a)^r := by
    rw [pow_add, pow_mul, hz, one_pow, one_mul]
  have h10 : (chi a)^10=(chi a)^4 := by simpa using hPeriod 1 4
  have h15 : (chi a)^15=(chi a)^3 := by simpa using hPeriod 2 3
  have h25 : (chi a)^25=chi a := by simpa using hPeriod 4 1
  have hValue := orderSixPacketValue_eq_polynomial_of_isUnit chi ha
  have hStarValue : star (orderSixPacketValue chi a)=1-(chi a)^4-(chi a)^3+chi a := by
    rw [hValue]
    simp only [star_add, star_sub, star_one, star_pow, hStar, <- pow_mul, h10, h15, h25]
  exact And.intro hz (And.intro hValue hStarValue)

/-- Exact norm-square identity for all actual residue values. -/
theorem orderSixPacketValue_norm_sq_eq_four_mul_re
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hSix : chi^6=1) (a : ZMod N) :
    norm (orderSixPacketValue chi a)^2=4*(orderSixPacketValue chi a).re := by
  by_cases ha : IsUnit a
  next =>
    have hData := orderSixPacket_unit_data chi hSix ha
    have hProduct : orderSixPacketValue chi a*star (orderSixPacketValue chi a) =
        2*(orderSixPacketValue chi a+star (orderSixPacketValue chi a)) := by
      rw [hData.2.2, hData.2.1]
      linear_combination (3+chi a-(chi a)^2-(chi a)^3)*hData.1
    have hNorm : (orderSixPacketValue chi a*star (orderSixPacketValue chi a)).re =
        norm (orderSixPacketValue chi a)^2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hRe := congrArg Complex.re hProduct
    rw [hNorm] at hRe
    norm_num [Complex.mul_re, Complex.add_re, Complex.star_def, Complex.conj_re] at hRe
    nlinarith
  next =>
    rw [orderSixPacketValue_eq_zero_of_nonunit chi ha]
    simp

/-- The real packet value obeys an exact quadratic, not an approximate bound. -/
theorem orderSixPacketValue_re_sq_eq_three_mul_re
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hSix : chi^6=1) (a : ZMod N) :
    (orderSixPacketValue chi a).re^2=3*(orderSixPacketValue chi a).re := by
  by_cases ha : IsUnit a
  next =>
    have hData := orderSixPacket_unit_data chi hSix ha
    have hIdempotent : (orderSixPacketValue chi a+star (orderSixPacketValue chi a))^2 =
        6*(orderSixPacketValue chi a+star (orderSixPacketValue chi a)) := by
      rw [hData.2.2, hData.2.1]
      linear_combination (8+2*chi a-3*(chi a)^2-2*(chi a)^3+(chi a)^4)*hData.1
    have hRe := congrArg Complex.re hIdempotent
    norm_num [pow_two, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im] at hRe
    rcases hRe with hSum | hZero
    next => nlinarith
    next => rw [hZero]; norm_num
  next =>
    rw [orderSixPacketValue_eq_zero_of_nonunit chi ha]
    simp

/-- The actual real packet is nonnegative at every residue, including nonunits. -/
theorem orderSixPacketValue_re_nonneg
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hSix : chi^6=1) (a : ZMod N) :
    0 <= (orderSixPacketValue chi a).re := by
  have h := orderSixPacketValue_norm_sq_eq_four_mul_re chi hSix a
  nlinarith [sq_nonneg (norm (orderSixPacketValue chi a))]

/-- Exact real values of the sixth-order filter: zero or three. -/
theorem orderSixPacketValue_re_zero_or_three
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hSix : chi^6=1) (a : ZMod N) :
    Or ((orderSixPacketValue chi a).re=0) ((orderSixPacketValue chi a).re=3) := by
  have h := orderSixPacketValue_re_sq_eq_three_mul_re chi hSix a
  have hProduct : (orderSixPacketValue chi a).re*((orderSixPacketValue chi a).re-3)=0 := by nlinarith
  by_cases hZero : (orderSixPacketValue chi a).re=0
  next => exact Or.inl hZero
  next =>
    have hThree := (mul_eq_zero.mp hProduct).resolve_left hZero
    exact Or.inr (by linarith)

/-- Raising the packet characters is exactly the packet of the raised
character, including the principal zeroth power and nonunit values. -/
theorem orderSixPacket_powerValue_eq
    {N : Nat} (chi : DirichletCharacter Complex N) (j : Nat) (a : ZMod N) :
    (Finset.univ : Finset (Fin 4)).sum (fun i => orderSixPacketWeights i *
      ((orderSixPacketCharacters chi i)^j) a) = orderSixPacketValue (chi^j) a := by
  have hCharacters (i : Fin 4) :
      (orderSixPacketCharacters chi i)^j=orderSixPacketCharacters (chi^j) i := by
    dsimp only [orderSixPacketCharacters]
    split <;> simp_all only [one_pow, pow_right_comm]
  unfold orderSixPacketValue
  apply Finset.sum_congr rfl
  intro i hi
  rw [hCharacters i]

/-- Every positive-exponent value packet has nonnegative real part.
The positive exponent is explicit to make nonunit power evaluation valid. -/
theorem orderSixPacket_powerSum_re_nonneg
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hSix : chi^6=1)
    (j : Nat) (hj : Not (j=0)) (a : ZMod N) :
    0 <= ((Finset.univ : Finset (Fin 4)).sum (fun i =>
      orderSixPacketWeights i * (orderSixPacketCharacters chi i a)^j)).re := by
  have hSixPower : (chi^j)^6=1 := by rw [pow_right_comm, hSix, one_pow]
  have h := orderSixPacketValue_re_nonneg (chi^j) hSixPower a
  rw [<- orderSixPacket_powerValue_eq chi j a] at h
  have hPoint (i : Fin 4) : ((orderSixPacketCharacters chi i)^j) a =
      (orderSixPacketCharacters chi i a)^j := MulChar.pow_apply' _ hj a
  simpa only [hPoint] using h

end

end RobinBV.NumberField
