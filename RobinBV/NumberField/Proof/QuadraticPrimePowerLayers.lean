import RobinBV.NumberField.Proof.QuadraticPrimePowerTransfer

/-!
# Quadratic prime-power theta and gap layers

This module defines the actual prime-ideal theta mass at every rational
prime-power exponent. In a quadratic field only inertia degrees one and two
occur. Consequently the theta layer at `p` is exactly `Lambda_K(p)`, the layer
at `p^2` is the inert prime-ideal mass, and every theta layer of exponent at
least three vanishes. The complementary gap formulas isolate the leading
square contribution from the lower-order higher prime powers.
-/

namespace RobinBV.NumberField

noncomputable section

def quadraticPrimeIdealThetaPrimePowerMass
    (D : NumberField.OddFundamentalDiscriminant) (p k : Nat) : Complex :=
  (Nat.card
      {P : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.inertiaDeg P.val Int = k} : Complex) *
    ((((k : Nat) : Real) * Real.log p : Real) : Complex)

theorem quadraticPrimeIdealThetaPrimePowerMass_one
    (D : NumberField.OddFundamentalDiscriminant) {p : Nat}
    (hp : p.Prime) :
    quadraticPrimeIdealThetaPrimePowerMass D p 1 =
      quadraticDedekindMangoldtSequence D p := by
  unfold quadraticPrimeIdealThetaPrimePowerMass
  have hCard := D.card_primesOver_inertiaDeg_one_eq_one_add_character p hp
  rw [hCard]
  unfold quadraticDedekindMangoldtSequence
  unfold BombieriVinogradov.SiegelWalfisz.twistedMangoldtSequence
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
  push_cast
  ring

theorem quadraticPrimeIdealThetaPrimePowerMass_two
    (D : NumberField.OddFundamentalDiscriminant) (p : Nat) :
    quadraticPrimeIdealThetaPrimePowerMass D p 2 =
      quadraticPrimeIdealThetaSquareMass D p := by
  rfl

theorem quadraticPrimeIdealThetaPrimePowerMass_eq_zero_of_three_le
    (D : NumberField.OddFundamentalDiscriminant) {p k : Nat}
    (hp : p.Prime) (hk : 3 <= k) :
    quadraticPrimeIdealThetaPrimePowerMass D p k = 0 := by
  rcases D.character_isQuadratic p with hZero | hOne | hNeg
  next =>
    have hRamified := D.ramified_prime_card_and_inertiaDeg p hp hZero
    letI : IsEmpty
        {P : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.inertiaDeg P.val Int = k} :=
      IsEmpty.mk (fun P => by
        have hDegree := hRamified.2 P.val
        omega)
    unfold quadraticPrimeIdealThetaPrimePowerMass
    simp
  next =>
    have hSplit := D.split_prime_card_and_inertiaDeg p hp hOne
    letI : IsEmpty
        {P : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.inertiaDeg P.val Int = k} :=
      IsEmpty.mk (fun P => by
        have hDegree := hSplit.2 P.val
        omega)
    unfold quadraticPrimeIdealThetaPrimePowerMass
    simp
  next =>
    have hInert := D.inert_prime_card_and_inertiaDeg p hp hNeg
    letI : IsEmpty
        {P : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.inertiaDeg P.val Int = k} :=
      IsEmpty.mk (fun P => by
        have hDegree := hInert.2 P.val
        omega)
    unfold quadraticPrimeIdealThetaPrimePowerMass
    simp

theorem quadraticPrimeIdealThetaPrimePowerMass_eq_piecewise
    (D : NumberField.OddFundamentalDiscriminant) {p : Nat}
    (hp : p.Prime) (k : Nat) :
    quadraticPrimeIdealThetaPrimePowerMass D p k =
      if k = 1 then quadraticDedekindMangoldtSequence D p
      else if k = 2 then quadraticPrimeIdealThetaSquareMass D p
      else 0 := by
  by_cases hOne : k = 1
  next =>
    subst k
    rw [if_pos rfl]
    exact quadraticPrimeIdealThetaPrimePowerMass_one D hp
  next =>
    rw [if_neg hOne]
    by_cases hTwo : k = 2
    next =>
      subst k
      rw [if_pos rfl]
      exact quadraticPrimeIdealThetaPrimePowerMass_two D p
    next =>
      rw [if_neg hTwo]
      by_cases hZero : k = 0
      next =>
        subst k
        unfold quadraticPrimeIdealThetaPrimePowerMass
        simp
      next =>
        exact quadraticPrimeIdealThetaPrimePowerMass_eq_zero_of_three_le
          D hp (by omega)

def quadraticPrimePowerGapCoefficient
    (D : NumberField.OddFundamentalDiscriminant) (p k : Nat) : Complex :=
  quadraticDedekindMangoldtSequence D (p ^ k) -
    quadraticPrimeIdealThetaPrimePowerMass D p k

theorem quadraticPrimePowerGapCoefficient_one
    (D : NumberField.OddFundamentalDiscriminant) {p : Nat}
    (hp : p.Prime) :
    quadraticPrimePowerGapCoefficient D p 1 = 0 := by
  unfold quadraticPrimePowerGapCoefficient
  rw [quadraticPrimeIdealThetaPrimePowerMass_one D hp, pow_one]
  ring

theorem quadraticPrimePowerGapCoefficient_two
    (D : NumberField.OddFundamentalDiscriminant) {p : Nat}
    (hp : p.Prime) :
    quadraticPrimePowerGapCoefficient D p 2 =
      quadraticDedekindMangoldtSequence D p := by
  unfold quadraticPrimePowerGapCoefficient
  rw [quadraticPrimeIdealThetaPrimePowerMass_two]
  rw [quadraticPrimeIdealThetaSquareMass_eq_coefficient D hp]
  exact quadraticMangoldt_square_sub_thetaSquare_eq D p

theorem quadraticPrimePowerGapCoefficient_eq_of_three_le
    (D : NumberField.OddFundamentalDiscriminant) {p k : Nat}
    (hp : p.Prime) (hk : 3 <= k) :
    quadraticPrimePowerGapCoefficient D p k =
      quadraticDedekindMangoldtSequence D (p ^ k) := by
  unfold quadraticPrimePowerGapCoefficient
  rw [quadraticPrimeIdealThetaPrimePowerMass_eq_zero_of_three_le D hp hk]
  ring

theorem quadraticPrimePowerGapCoefficient_eq_piecewise
    (D : NumberField.OddFundamentalDiscriminant) {p k : Nat}
    (hp : p.Prime) :
    quadraticPrimePowerGapCoefficient D p k =
      if k = 2 then quadraticDedekindMangoldtSequence D p
      else if 3 <= k then quadraticDedekindMangoldtSequence D (p ^ k)
      else 0 := by
  by_cases hTwo : k = 2
  next =>
    subst k
    rw [if_pos rfl]
    exact quadraticPrimePowerGapCoefficient_two D hp
  next =>
    rw [if_neg hTwo]
    by_cases hThree : 3 <= k
    next =>
      rw [if_pos hThree]
      exact quadraticPrimePowerGapCoefficient_eq_of_three_le D hp hThree
    next =>
      rw [if_neg hThree]
      have hSmall : Or (k = 0) (k = 1) := by omega
      rcases hSmall with hZero | hOne
      next =>
        subst k
        unfold quadraticPrimePowerGapCoefficient
        unfold quadraticPrimeIdealThetaPrimePowerMass
        simp [quadraticDedekindMangoldtSequence,
          BombieriVinogradov.SiegelWalfisz.twistedMangoldtSequence]
      next =>
        subst k
        exact quadraticPrimePowerGapCoefficient_one D hp

end

end RobinBV.NumberField
