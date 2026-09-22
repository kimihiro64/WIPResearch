/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
/-
# Sieve logarithmic cutoffs

This module defines the explicit cutoff functions used to control logarithmic
weights in the prime-sieve estimates.
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# SieveCutoff

Explicit finite interval estimates used in signed prime-candidate accounting.
All constants and endpoint conditions are retained; no prime-existence result
is claimed by a negative lower envelope.
-/

set_option autoImplicit false
namespace Real

noncomputable def squareSieveCutoff (x : Real) : Nat := Nat.floor (Real.sqrt x/Real.log x)

noncomputable def squareSieveDenominator (x : Real) : Real :=
  Real.log x-2*Real.log (Real.log x)

theorem squareSieveDenominator_pos {x : Real} (hx : 1 < x) :
    0 < squareSieveDenominator x := by
  have ht := Real.log_pos hx
  have hh := Real.log_le_sub_one_of_pos (_root_.div_pos ht (by norm_num : (0 : Real) < 2))
  rw [Real.log_div (ne_of_gt ht) (by norm_num : Not ((2 : Real) = 0))] at hh
  have htwo := Real.log_lt_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    (by norm_num : Not ((2 : Real) = 1))
  unfold squareSieveDenominator
  linarith

theorem log_square_sieve_scale {x : Real} (hx : 1 < x) :
    Real.log (Real.sqrt x/Real.log x) = squareSieveDenominator x/2 := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have ht := Real.log_pos hx
  rw [Real.log_div (ne_of_gt hs) (ne_of_gt ht), Real.log_sqrt (le_of_lt hx0)]
  unfold squareSieveDenominator
  ring

theorem one_lt_square_sieve_scale {x : Real} (hx : 1 < x) :
    1 < Real.sqrt x/Real.log x := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hz : 0 < Real.sqrt x/Real.log x :=
    _root_.div_pos (Real.sqrt_pos.mpr hx0) (Real.log_pos hx)
  apply (Real.log_pos_iff (le_of_lt hz)).mp
  rw [log_square_sieve_scale hx]
  exact _root_.div_pos (squareSieveDenominator_pos hx) (by norm_num)

theorem one_le_squareSieveCutoff {x : Real} (hx : 1 < x) :
    1 <= squareSieveCutoff x :=
  (Nat.one_le_floor_iff _).mpr (le_of_lt (one_lt_square_sieve_scale hx))

theorem squareSieveCutoff_log_lower {x : Real} (hx : 1 < x) :
    squareSieveDenominator x/2 <= Real.log ((squareSieveCutoff x : Real)+1) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hz : 0 < Real.sqrt x/Real.log x :=
    _root_.div_pos (Real.sqrt_pos.mpr hx0) (Real.log_pos hx)
  have hf := Nat.lt_floor_add_one (Real.sqrt x/Real.log x)
  have hl := Real.log_le_log hz (le_of_lt hf)
  rw [log_square_sieve_scale hx] at hl
  exact hl

theorem squareSieveCutoff_sq_bound {x : Real} (hx : 1 < x) :
    (squareSieveCutoff x : Real)^2 <= x/(Real.log x)^2 := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hz : 0 <= Real.sqrt x/Real.log x :=
    le_of_lt (_root_.div_pos (Real.sqrt_pos.mpr hx0) (Real.log_pos hx))
  have hf : (squareSieveCutoff x : Real) <= Real.sqrt x/Real.log x := Nat.floor_le hz
  have hmul := _root_.mul_le_mul hf hf
    (by positivity : (0 : Real) <= squareSieveCutoff x) hz
  calc
    (squareSieveCutoff x : Real)^2 <= (Real.sqrt x/Real.log x)^2 := by
      simpa only [pow_two] using hmul
    _ = x/(Real.log x)^2 := by rw [div_pow, Real.sq_sqrt (le_of_lt hx0)]

theorem one_le_log_of_four_le {x : Real} (hx : 4 <= x) : 1 <= Real.log x := by
  have hx0 : 0 < x := by linarith
  have hr2 : (2 : Real) <= Real.sqrt x := by
    have hsq := Real.sq_sqrt (le_of_lt hx0)
    have hnonneg := Real.sqrt_nonneg x
    nlinarith
  have hr0 : 0 < Real.sqrt x := by linarith
  have hi : Real.sqrt x*Inv.inv (Real.sqrt x) = 1 := by field_simp
  have hm := _root_.mul_le_mul_of_nonneg_right hr2 (inv_nonneg.mpr (le_of_lt hr0))
  rw [hi] at hm
  have hl := Real.one_sub_inv_le_log_of_pos hr0
  rw [Real.log_sqrt (le_of_lt hx0)] at hl
  linarith

theorem squareSieveCutoff_sq_le_self {x : Real} (hx : 4 <= x) :
    (squareSieveCutoff x : Real)^2 <= x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have ht := Real.log_pos hx1
  have ht1 := one_le_log_of_four_le hx
  have hz : 0 <= Real.sqrt x/Real.log x :=
    le_of_lt (_root_.div_pos (Real.sqrt_pos.mpr hx0) ht)
  have hf : (squareSieveCutoff x : Real) <= Real.sqrt x/Real.log x := Nat.floor_le hz
  have he : (Real.sqrt x/Real.log x)*Real.log x = Real.sqrt x := by field_simp
  have hscale : Real.sqrt x/Real.log x <= Real.sqrt x := by
    have h := _root_.mul_le_mul_of_nonneg_left ht1 hz
    simpa only [mul_one, he] using h
  have hroot := hf.trans hscale
  have hmul := _root_.mul_le_mul hroot hroot
    (by positivity : (0 : Real) <= squareSieveCutoff x) (Real.sqrt_nonneg x)
  have hsq := Real.sq_sqrt (le_of_lt hx0)
  nlinarith

end Real
