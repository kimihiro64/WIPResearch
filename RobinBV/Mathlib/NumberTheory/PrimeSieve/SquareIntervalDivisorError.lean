/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalCounts

/-!
# SquareIntervalDivisorError

Explicit finite interval estimates used in signed prime-candidate accounting.
All constants and endpoint conditions are retained; no prime-existence result
is claimed by a negative lower envelope.
-/

set_option autoImplicit false
namespace Nat.PrimeSieve

private theorem odd_endpoint_floor_bounds (X d : Nat) (hd : 0 < d) :
    2*d*((X/d+1)/2) <= X+d /\
      X+d < 2*d*(((X/d+1)/2)+1) := by
  have hq := Nat.mod_add_div X d
  have hr := Nat.mod_lt X hd
  have ha := Nat.mod_add_div (X/d+1) 2
  have hb := Nat.mod_lt (X/d+1) (by decide : 0 < 2)
  have hleft : 2*((X/d+1)/2) <= X/d+1 := by omega
  have hright : X/d+1 <= 2*((X/d+1)/2)+1 := by omega
  have hl := Nat.mul_le_mul_left d hleft
  have hu := Nat.mul_le_mul_left d hright
  constructor
  next => nlinarith only [hl, hq, Nat.zero_le (X%d)]
  next => nlinarith only [hu, hq, hr]

/-- The exact odd-divisor packet differs from n/d by strictly less thanone.
Both inequalities are integral; no finite range in n is substituted. -/
theorem odd_interval_scaled_unit_error (n : Nat) {d : Nat} (hd : d%2 = 1) :
    d*(oddMultiplesInSquare n d).card < n+d /\
      n < d*(oddMultiplesInSquare n d).card+d := by
  have hd0 : 0 < d := by omega
  have hlo := odd_endpoint_floor_bounds (n*n) d hd0
  have hhi := odd_endpoint_floor_bounds (n*n+2*n) d hd0
  have he := card_oddMultiplesInSquare n hd
  have he' := congrArg (fun v => d*v) he
  constructor <;> nlinarith only [hlo.1, hlo.2, hhi.1, hhi.2, he']

theorem odd_interval_abs_unit_error (n : Nat) {d : Nat} (hd : d%2 = 1) :
    abs ((oddMultiplesInSquare n d).card - (n : Real)/(d : Real)) < 1 := by
  have h := odd_interval_scaled_unit_error n hd
  have hd0 : (0 : Real) < d := by exact_mod_cast (show 0 < d by omega)
  have hu : (d : Real)*(oddMultiplesInSquare n d).card < (n : Real)+d := by
    exact_mod_cast h.1
  have hl : (n : Real) < (d : Real)*(oddMultiplesInSquare n d).card+d := by
    exact_mod_cast h.2
  have he : (d : Real)*((n : Real)/(d : Real)) = n := by
    field_simp
  apply abs_lt.mpr
  constructor
  next =>
    by_contra hh
    have hh' : (0 : Real) <= (n : Real)/(d : Real)-
        (oddMultiplesInSquare n d).card-1 := by linarith
    have hm := _root_.mul_nonneg (le_of_lt hd0) hh'
    nlinarith
  next =>
    by_contra hh
    have hh' : (0 : Real) <= (oddMultiplesInSquare n d).card-
        (n : Real)/(d : Real)-1 := by linarith
    have hm := _root_.mul_nonneg (le_of_lt hd0) hh'
    nlinarith

end Nat.PrimeSieve
