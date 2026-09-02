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
