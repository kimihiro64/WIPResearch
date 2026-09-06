/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic.Ring

/-!
# Positive finite packets of multiplicative characters

Conjugate-pair characters expand the entire squared norm of an arbitrary
finite character sum. Actual character powers include exponent zero and
nonunits; conversion to powers of values explicitly requires positive exponent.
-/

set_option autoImplicit false

namespace MulChar

open scoped Classical

noncomputable section

variable {R I : Type*} [CommRing R]

/-- Pair characters realizing the squared norm of a finite character sum. -/
def normSquarePacketCharacter (chi : I -> MulChar R Complex) (ij : Prod I I) :
    MulChar R Complex :=
  chi ij.1 * Inv.inv (chi ij.2)

/-- Conjugate coefficient products for a squared finite character sum. -/
def normSquarePacketWeight (c : I -> Complex) (ij : Prod I I) : Complex :=
  c ij.1 * star (c ij.2)

variable [Finite (Units R)]

/-- The complete pair-character packet at every actual character power is
exactly a real squared norm, including zero exponent and nonunit residues. -/
theorem sum_normSquarePacket_pow_eq
    (s : Finset I) (chi : I -> MulChar R Complex) (c : I -> Complex)
    (j : Nat) (a : R) :
    (s.product s).sum (fun ij => normSquarePacketWeight c ij *
      ((normSquarePacketCharacter chi ij)^j) a) =
      ((norm (s.sum (fun i => c i * ((chi i)^j) a)))^2 : Real) := by
  calc
    _ = (s.sum (fun i => c i * ((chi i)^j) a)) *
        star (s.sum (fun i => c i * ((chi i)^j) a)) := by
      rw [star_sum, Finset.sum_mul_sum, Finset.product_eq_sprod, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [normSquarePacketWeight, normSquarePacketCharacter]
      rw [mul_pow, inv_pow, MulChar.mul_apply, <- MulChar.star_apply']
      simp only [star_mul]
      ring
    _ = _ := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Squared character packets have nonnegative real weight at every power. -/
theorem sum_normSquarePacket_pow_re_nonneg
    (s : Finset I) (chi : I -> MulChar R Complex) (c : I -> Complex)
    (j : Nat) (a : R) :
    0 <= ((s.product s).sum (fun ij => normSquarePacketWeight c ij *
      ((normSquarePacketCharacter chi ij)^j) a)).re := by
  rw [sum_normSquarePacket_pow_eq, Complex.ofReal_re]
  exact sq_nonneg _

/-- Positive powers of values also give the entire real squared norm.
The nonzero exponent hypothesis is essential at nonunits. -/
theorem sum_normSquarePacket_value_pow_eq
    (s : Finset I) (chi : I -> MulChar R Complex) (c : I -> Complex)
    (j : Nat) (hj : Not (j = 0)) (a : R) :
    (s.product s).sum (fun ij => normSquarePacketWeight c ij *
      (normSquarePacketCharacter chi ij a)^j) =
      ((norm (s.sum (fun i => c i * (chi i a)^j)))^2 : Real) := by
  simpa only [MulChar.pow_apply' _ hj] using
    sum_normSquarePacket_pow_eq s chi c j a

end

end MulChar
