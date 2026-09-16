/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# IntervalDivisorError

Explicit finite interval estimates used in signed prime-candidate accounting.
All constants and endpoint conditions are retained; no prime-existence result
is claimed by a negative lower envelope.
-/

set_option autoImplicit false
namespace Nat

theorem Ioc_filter_dvd_card_add_prefix {L U : Nat} (hLU : L <= U) (d : Nat) :
    ((Finset.Ioc L U).filter (fun m => Dvd.dvd d m)).card+L/d = U/d := by
  let A := (Finset.Ioc 0 U).filter (fun m => Dvd.dvd d m)
  have hlo : A.filter (fun m => Not (L < m)) =
      (Finset.Ioc 0 L).filter (fun m => Dvd.dvd d m) := by
    ext m
    simp only [A, Finset.mem_filter, Finset.mem_Ioc]
    omega
  have hhi : A.filter (fun m => L < m) =
      (Finset.Ioc L U).filter (fun m => Dvd.dvd d m) := by
    ext m
    simp only [A, Finset.mem_filter, Finset.mem_Ioc]
    omega
  have h := Finset.card_filter_add_card_filter_not (s := A) (fun m => L < m)
  rw [hhi, hlo] at h
  dsimp only [A] at h
  simpa only [Nat.Ioc_filter_dvd_card_eq_div] using h

/-- Actual divisibility counts in every integer interval have strict unit
error, including every modulus used in the Selberg quadratic remainder. -/
theorem Ioc_filter_dvd_abs_unit_error {L U : Nat} (hLU : L <= U)
    {d : Nat} (hd : 0 < d) :
    abs ((((Finset.Ioc L U).filter (fun m => Dvd.dvd d m)).card : Real) -
      ((U : Real)-L)/(d : Real)) < 1 := by
  let C := ((Finset.Ioc L U).filter (fun m => Dvd.dvd d m)).card
  have hc := Ioc_filter_dvd_card_add_prefix hLU d
  have hs := congrArg (fun k => d*k) hc
  have hnat : d*C+L+U%d = U+L%d := by
    dsimp only [C]
    nlinarith only [hs, Nat.mod_add_div L d, Nat.mod_add_div U d]
  have he : (d : Real)*C+L+(U%d : Nat) = (U : Real)+(L%d : Nat) := by
    exact_mod_cast hnat
  have hdR : (0 : Real) < d := by exact_mod_cast hd
  have hLmod : ((L%d : Nat) : Real) < d := by exact_mod_cast Nat.mod_lt L hd
  have hUmod : ((U%d : Nat) : Real) < d := by exact_mod_cast Nat.mod_lt U hd
  have hL0 : (0 : Real) <= (L%d : Nat) := Nat.cast_nonneg _
  have hU0 : (0 : Real) <= (U%d : Nat) := Nat.cast_nonneg _
  have hlo : (U : Real)-L < (d : Real)*C+d := by
    nlinarith only [he, hUmod, hL0]
  have hhi : (d : Real)*C < (U : Real)-L+d := by
    nlinarith only [he, hLmod, hU0]
  have hdiv : (d : Real)*(((U : Real)-L)/(d : Real)) = (U : Real)-L := by field_simp
  change abs ((C : Real)-((U : Real)-L)/(d : Real)) < 1
  apply abs_lt.mpr
  constructor
  next =>
    by_contra hh
    have hb : (0 : Real) <= ((U : Real)-L)/(d : Real)-C-1 := by linarith
    have hm := _root_.mul_nonneg (le_of_lt hdR) hb
    nlinarith
  next =>
    by_contra hh
    have hb : (0 : Real) <= (C : Real)-((U : Real)-L)/(d : Real)-1 := by linarith
    have hm := _root_.mul_nonneg (le_of_lt hdR) hb
    nlinarith

end Nat
