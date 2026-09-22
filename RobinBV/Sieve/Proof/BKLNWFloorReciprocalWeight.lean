/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Floor-bin reciprocal weight

The reciprocal weight at a height y >= 1 is bounded by the reciprocal of
the integer floor bin. This is the pointwise inequality used in the transfer
from zero ordinates to natural height bins.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem rob_bv_floor_reciprocal_weight_le
    {y w : Real} (hy : 1 <= y) (hw : 0 <= w) :
    w / y <= (1 / (Nat.floor y : Real)) * w := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hfloorNat : 0 < Nat.floor y := Nat.floor_pos.mpr hy
  have hfloor : 0 < (Nat.floor y : Real) := by exact_mod_cast hfloorNat
  have hfloorle : (Nat.floor y : Real) <= y := Nat.floor_le hypos.le
  have hrec : 1 / y <= 1 / (Nat.floor y : Real) := by
    exact (div_le_div_iff_of_pos_left one_pos hypos hfloor).2 hfloorle
  simpa [div_eq_mul_inv, mul_comm] using
    (mul_le_mul_of_nonneg_right hrec hw)

end RobinBV.Sieve
