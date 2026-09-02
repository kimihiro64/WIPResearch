import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaSplitting
import RobinBV.NumberField.Proof.QuadraticDedekindPrimeSide

/-!
# Quadratic prime-square transfer

At a rational square, an inert prime is already the norm of a prime ideal and
belongs to the prime-ideal theta term. Removing that theta contribution from
the quadratic Dedekind von Mangoldt coefficient leaves exactly the degree-one
coefficient. The splitting-type corollaries explain why the leading
psi-minus-theta transfer does not naively double in quadratic fields.
-/

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz

noncomputable section

def quadraticPrimeIdealThetaSquareCoefficient
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) : Complex :=
  (D.character n ^ (2 : Nat) - D.character n) *
    (ArithmeticFunction.vonMangoldt n : Complex)

/-- The actual prime-ideal theta mass at the rational square `p^2`: every
prime ideal above `p` with inertia degree two contributes `log(p^2)`. -/
def quadraticPrimeIdealThetaSquareMass
    (D : NumberField.OddFundamentalDiscriminant) (p : Nat) : Complex :=
  (Nat.card
      {P : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.inertiaDeg P.val Int = 2} : Complex) *
    (((2 : Real) * Real.log p : Real) : Complex)

theorem quadraticMangoldt_square_sub_thetaSquare_eq
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) :
    quadraticDedekindMangoldtSequence D (n ^ (2 : Nat)) -
        quadraticPrimeIdealThetaSquareCoefficient D n =
      quadraticDedekindMangoldtSequence D n := by
  unfold quadraticDedekindMangoldtSequence
  unfold quadraticPrimeIdealThetaSquareCoefficient
  unfold twistedMangoldtSequence
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by norm_num)]
  have hCharacter :
      D.character ((n ^ (2 : Nat) : Nat) : ZMod D.modulus) =
        D.character n ^ (2 : Nat) := by
    rw [Nat.cast_pow, map_pow]
  rw [hCharacter]
  ring

theorem quadraticPrimeIdealThetaSquareCoefficient_im
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) :
    (quadraticPrimeIdealThetaSquareCoefficient D n).im = 0 := by
  unfold quadraticPrimeIdealThetaSquareCoefficient
  rcases D.character_isQuadratic n with hZero | hOne | hNeg
  next => rw [hZero]; simp
  next => rw [hOne]; simp
  next => rw [hNeg]; simp

theorem quadraticPrimeIdealThetaSquareCoefficient_re_nonneg
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) :
    0 <= (quadraticPrimeIdealThetaSquareCoefficient D n).re := by
  unfold quadraticPrimeIdealThetaSquareCoefficient
  rcases D.character_isQuadratic n with hZero | hOne | hNeg
  next => rw [hZero]; simp
  next => rw [hOne]; simp
  next =>
    rw [hNeg]
    simp [ArithmeticFunction.vonMangoldt_nonneg]

theorem quadraticMangoldt_square_eq_thetaSquare_add
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) :
    quadraticDedekindMangoldtSequence D (n ^ (2 : Nat)) =
      quadraticPrimeIdealThetaSquareCoefficient D n +
        quadraticDedekindMangoldtSequence D n := by
  have h := quadraticMangoldt_square_sub_thetaSquare_eq D n
  linear_combination h

theorem quadraticMangoldt_square_positive_decomposition
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) :
    And
      (quadraticDedekindMangoldtSequence D (n ^ (2 : Nat)) =
        quadraticPrimeIdealThetaSquareCoefficient D n +
          quadraticDedekindMangoldtSequence D n)
      (And
        (0 <= (quadraticPrimeIdealThetaSquareCoefficient D n).re)
        (0 <= (quadraticDedekindMangoldtSequence D n).re)) := by
  exact And.intro (quadraticMangoldt_square_eq_thetaSquare_add D n)
    (And.intro
      (quadraticPrimeIdealThetaSquareCoefficient_re_nonneg D n)
      (quadraticDedekindMangoldtSequence_re_nonneg D n))

theorem quadraticPrimeIdealThetaSquareMass_eq_coefficient
    (D : NumberField.OddFundamentalDiscriminant) {p : Nat}
    (hp : p.Prime) :
    quadraticPrimeIdealThetaSquareMass D p =
      quadraticPrimeIdealThetaSquareCoefficient D p := by
  rcases D.character_isQuadratic p with hZero | hOne | hNeg
  next =>
    have hRamified := D.ramified_prime_card_and_inertiaDeg p hp hZero
    letI : IsEmpty
        {P : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.inertiaDeg P.val Int = 2} :=
      IsEmpty.mk (fun P => by
        have hOne := hRamified.2 P.val
        omega)
    unfold quadraticPrimeIdealThetaSquareMass
    unfold quadraticPrimeIdealThetaSquareCoefficient
    rw [hZero, ArithmeticFunction.vonMangoldt_apply_prime hp]
    simp
  next =>
    have hSplit := D.split_prime_card_and_inertiaDeg p hp hOne
    letI : IsEmpty
        {P : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.inertiaDeg P.val Int = 2} :=
      IsEmpty.mk (fun P => by
        have hOneP := hSplit.2 P.val
        omega)
    unfold quadraticPrimeIdealThetaSquareMass
    unfold quadraticPrimeIdealThetaSquareCoefficient
    rw [hOne, ArithmeticFunction.vonMangoldt_apply_prime hp]
    simp
  next =>
    have hInert := D.inert_prime_card_and_inertiaDeg p hp hNeg
    let eAll :
        Equiv
          (Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField))
          {P : Ideal.primesOver
              (Ideal.span {(p : Int)})
              (NumberField.RingOfIntegers D.QuadraticField) //
            Ideal.inertiaDeg P.val Int = 2} := {
      toFun P := Subtype.mk P (hInert.2 P)
      invFun P := P.val
      left_inv P := rfl
      right_inv P := by apply Subtype.ext; rfl }
    have hCardAll := Nat.card_congr eAll
    have hCard :
        Nat.card
          {P : Ideal.primesOver
              (Ideal.span {(p : Int)})
              (NumberField.RingOfIntegers D.QuadraticField) //
            Ideal.inertiaDeg P.val Int = 2} = 1 := by
      rw [hInert.1] at hCardAll
      exact hCardAll.symm
    unfold quadraticPrimeIdealThetaSquareMass
    unfold quadraticPrimeIdealThetaSquareCoefficient
    rw [hCard, hNeg, ArithmeticFunction.vonMangoldt_apply_prime hp]
    push_cast
    ring

theorem quadraticPrimeIdealThetaSquareMass_re_nonneg
    (D : NumberField.OddFundamentalDiscriminant) {p : Nat}
    (hp : p.Prime) :
    0 <= (quadraticPrimeIdealThetaSquareMass D p).re := by
  rw [quadraticPrimeIdealThetaSquareMass_eq_coefficient D hp]
  exact quadraticPrimeIdealThetaSquareCoefficient_re_nonneg D p

theorem sum_quadraticMangoldt_square_sub_thetaSquareMass_eq
    (D : NumberField.OddFundamentalDiscriminant) (S : Finset Nat)
    (hPrime : forall p : Nat, Membership.mem S p -> p.Prime) :
    S.sum (fun p =>
        quadraticDedekindMangoldtSequence D (p ^ (2 : Nat)) -
          quadraticPrimeIdealThetaSquareMass D p) =
      S.sum (quadraticDedekindMangoldtSequence D) := by
  apply Finset.sum_congr rfl
  intro p hpS
  rw [quadraticPrimeIdealThetaSquareMass_eq_coefficient D (hPrime p hpS)]
  exact quadraticMangoldt_square_sub_thetaSquare_eq D p

theorem quadraticMangoldt_square_gap_split
    (D : NumberField.OddFundamentalDiscriminant) {p : Nat}
    (hp : p.Prime) (hSplit : D.character p = 1) :
    quadraticDedekindMangoldtSequence D (p ^ (2 : Nat)) -
        quadraticPrimeIdealThetaSquareCoefficient D p =
      2 * Real.log p := by
  rw [quadraticMangoldt_square_sub_thetaSquare_eq]
  unfold quadraticDedekindMangoldtSequence twistedMangoldtSequence
  rw [hSplit, ArithmeticFunction.vonMangoldt_apply_prime hp]
  push_cast
  ring

theorem quadraticMangoldt_square_gap_inert
    (D : NumberField.OddFundamentalDiscriminant) {p : Nat}
    (hp : p.Prime) (hInert : D.character p = -1) :
    quadraticDedekindMangoldtSequence D (p ^ (2 : Nat)) -
        quadraticPrimeIdealThetaSquareCoefficient D p = 0 := by
  rw [quadraticMangoldt_square_sub_thetaSquare_eq]
  unfold quadraticDedekindMangoldtSequence twistedMangoldtSequence
  rw [hInert, ArithmeticFunction.vonMangoldt_apply_prime hp]
  push_cast
  ring

theorem quadraticMangoldt_square_gap_ramified
    (D : NumberField.OddFundamentalDiscriminant) {p : Nat}
    (hp : p.Prime) (hRamified : D.character p = 0) :
    quadraticDedekindMangoldtSequence D (p ^ (2 : Nat)) -
        quadraticPrimeIdealThetaSquareCoefficient D p =
      Real.log p := by
  rw [quadraticMangoldt_square_sub_thetaSquare_eq]
  unfold quadraticDedekindMangoldtSequence twistedMangoldtSequence
  rw [hRamified, ArithmeticFunction.vonMangoldt_apply_prime hp]
  push_cast
  ring

end

end RobinBV.NumberField
