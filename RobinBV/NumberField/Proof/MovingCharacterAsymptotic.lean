import RobinBV.NumberField.Proof.CharacterPrimeMoments
import RobinBV.NumberField.Proof.MovingCharacterRemainder

/-!
# Complete moving character corrections and principal-power coefficients

The entire infinite-tail deletion integral is combined with the actual SW
prime moments. Each positive character power contributes one precisely when
it is principal. The square-scale shift distinguishes principal, quadratic
and higher-order characters without assuming ERH.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter
open scoped Classical

noncomputable section

/-- At every fixed positive integer power scale, the complete character
deletion integral has the coefficient given by its principal powers. -/
theorem movingCharacterCorrection_normalized_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (k : Nat) :
    Tendsto (fun P : Nat => (((P : Real) ^ k * Real.log P : Real) : Complex) *
      movingCharacterCorrection chi P ((P : Real) ^ (k + 1))) atTop
      (nhds (-Finset.sum (Finset.Icc 1 (k + 1))
        (fun j => if chi ^ j = 1 then (1 : Complex) else 0) / ((k + 1 : Nat) : Complex))) := by
  have hMoment := (characterPrimePowerMoment_div_tendsto chi (k + 1)).div_const
    ((k + 1 : Nat) : Complex)
  have h := (movingCharacterCorrection_moment_transfer_tendsto chi k).sub hMoment
  convert h using 1
  next =>
    funext P
    ring
  next =>
    ring

/-- The exact critical normalization at x=P^2 has shift -2 for the
principal character, -1 for a nonprincipal quadratic character, and zero
when the square of the character is nonprincipal. -/
theorem movingCharacter_square_critical_shift
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    Tendsto (fun P : Nat =>
      ((Real.sqrt ((P : Real) ^ 2) * Real.log ((P : Real) ^ 2) : Real) : Complex) *
        movingCharacterCorrection chi P ((P : Real) ^ 2)) atTop
      (nhds (-(if chi = 1 then (1 : Complex) else 0) -
        (if chi ^ 2 = 1 then (1 : Complex) else 0))) := by
  have h := (movingCharacterCorrection_normalized_tendsto chi 1).const_mul (2 : Complex)
  convert h using 1
  next =>
    funext P
    simp only [Real.sqrt_sq (Nat.cast_nonneg P), Real.log_pow, pow_one]
    push_cast
    ring
  next =>
    have hSet : Finset.Icc 1 (1 + 1) = ({1, 2} : Finset Nat) := by decide
    rw [hSet, Finset.sum_insert (by decide : Not (Membership.mem ({2} : Finset Nat) 1)),
      Finset.sum_singleton]
    norm_num only [pow_one, Nat.cast_add, Nat.cast_one]
    ring

end

end RobinBV.NumberField
