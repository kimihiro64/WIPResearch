/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log

/-!
# Exact logarithmic position of a real cutoff between integer powers

The integer exponent selected by a real cutoff is bounded using both exact
integer logarithm endpoints. The logarithmic gap is nonnegative and strictly
smaller than the logarithm of the base, including at exact powers.
-/

set_option autoImplicit false

namespace Nat

/-- The selected integer power is at or below the actual real cutoff. -/
theorem pow_log_floor_le {b : Nat} {t : Real} (ht : 1 <= t) :
    ((b ^ Nat.log b (Nat.floor t) : Nat) : Real) <= t := by
  have hFloorOne : 1 <= Nat.floor t :=
    Nat.le_floor (by simpa only [Nat.cast_one] using ht)
  have hFloorNe : Not (Nat.floor t = 0) := by omega
  have hPow := Nat.pow_log_le_self b hFloorNe
  exact (show ((b ^ Nat.log b (Nat.floor t) : Nat) : Real) <= (Nat.floor t : Nat) by
    exact_mod_cast hPow).trans (Nat.floor_le (by linarith))

/-- The next integer power is strictly above the actual real cutoff. -/
theorem lt_pow_log_floor_succ {b : Nat} (hb : 1 < b) (t : Real) :
    t < ((b ^ (Nat.log b (Nat.floor t) + 1) : Nat) : Real) := by
  have hNat := Nat.lt_pow_succ_log_self hb (Nat.floor t)
  have hStep : Nat.floor t + 1 <= b ^ (Nat.log b (Nat.floor t) + 1) := by
    exact hNat
  have hCast : (Nat.floor t : Real) + 1 <=
      ((b ^ (Nat.log b (Nat.floor t) + 1) : Nat) : Real) := by
    exact_mod_cast hStep
  exact (Nat.lt_floor_add_one t).trans_le hCast

/-- Complete logarithmic cutoff gap with its exact sign and full width. -/
theorem log_sub_log_floor_mul_log_bounds
    {b : Nat} (hb : 1 < b) {t : Real} (ht : 1 <= t) :
    And (0 <= Real.log t - (Nat.log b (Nat.floor t) : Real) * Real.log b)
      (Real.log t - (Nat.log b (Nat.floor t) : Real) * Real.log b < Real.log b) := by
  have hbPos : (0 : Real) < b := by exact_mod_cast (show 0 < b by omega)
  have htPos : 0 < t := by linarith
  have hPowerPos : (0 : Real) < ((b ^ Nat.log b (Nat.floor t) : Nat) : Real) := by
    exact_mod_cast Nat.pow_pos (show 0 < b by omega)
  have hLower := Real.log_le_log hPowerPos (pow_log_floor_le (b := b) ht)
  have hUpper := Real.log_lt_log htPos (lt_pow_log_floor_succ hb t)
  rw [Nat.cast_pow, Real.log_pow] at hLower hUpper
  push_cast at hUpper
  constructor <;> nlinarith

end Nat
