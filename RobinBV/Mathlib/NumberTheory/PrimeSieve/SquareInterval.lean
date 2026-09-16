/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

/-!
# Multiplicative geometry between consecutive squares

These elementary bounds isolate the factor configurations needed for exact
least-prime-owner counts. No distribution estimate is assumed.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

/-- Two factors above the square-root cutoff have product above the interval index. -/
theorem index_lt_mul_of_sq_lt {n p q : Nat}
    (hp : n < p * p) (hq : n < q * q) : n < p * q := by
  rcases le_total p q with hpq | hqp
  next => exact lt_of_lt_of_le hp (Nat.mul_le_mul_left p hpq)
  next => exact lt_of_lt_of_le hq (by nlinarith)

/-- Four factors above the cutoff cannot fit below the next square. -/
theorem four_factor_lower_bound {n p q r s : Nat}
    (hp : n < p * p) (hq : n < q * q)
    (hr : n < r * r) (hs : n < s * s) :
    (n + 1) * (n + 1) <= (p * q) * (r * s) := by
  have hpq : n + 1 <= p * q := index_lt_mul_of_sq_lt hp hq
  have hrs : n + 1 <= r * s := index_lt_mul_of_sq_lt hr hs
  exact Nat.mul_le_mul hpq hrs

/-- An ordered two-factor representation straddles the square-interval index. -/
theorem semiprime_straddles {n p q : Nat} (hpq : p <= q)
    (hlo : n * n < p * q) (hhi : p * q < (n + 1) * (n + 1)) :
    p <= n /\ n < q := by
  constructor
  next =>
    by_contra h
    have hp : n + 1 <= p := by omega
    have hq : n + 1 <= q := le_trans hp hpq
    have h := Nat.mul_le_mul hp hq
    omega
  next =>
    by_contra h
    have hq : q <= n := by omega
    have hp : p <= n := le_trans hpq hq
    have h := Nat.mul_le_mul hp hq
    omega

/-- A cofactor of a product above the cutoff is at most the interval index. -/
theorem cofactor_le_index {n d r : Nat} (hd : n < d)
    (hhi : d * r < (n + 1) * (n + 1)) : r <= n := by
  by_contra h
  have hr : n + 1 <= r := by omega
  have hd' : n + 1 <= d := hd
  have hprod := Nat.mul_le_mul hd' hr
  omega

/-- A cell with coefficient greater than the index contains at most one odd cofactor. -/
theorem odd_cofactor_unique {n d r s : Nat} (hd : n < d)
    (hr : r % 2 = 1) (hs : s % 2 = 1)
    (hrlo : n * n < d * r) (hrhi : d * r < (n + 1) * (n + 1))
    (hslo : n * n < d * s) (hshi : d * s < (n + 1) * (n + 1)) :
    r = s := by
  rcases lt_trichotomy r s with hrs | hrs | hsr
  next =>
    have hgap : r + 2 <= s := by omega
    have hprod := Nat.mul_le_mul_left d hgap
    nlinarith
  next => exact hrs
  next =>
    have hgap : s + 2 <= r := by omega
    have hprod := Nat.mul_le_mul_left d hgap
    nlinarith

/-- The unique odd cofactor is explicitly the first odd integer above the lower quotient. -/
theorem odd_cofactor_eq_floor {n d r : Nat} (hd : n < d) (hr : r % 2 = 1)
    (hlo : n * n < d * r) (hhi : d * r < (n + 1) * (n + 1)) :
    r = 2 * ((n * n / d + 1) / 2) + 1 := by
  have hd0 : 0 < d := by omega
  have hloq : n * n / d < r := (Nat.div_lt_iff_lt_mul hd0).mpr
    (by simpa only [Nat.mul_comm] using hlo)
  have hfloor := Nat.lt_mul_div_succ (n * n) hd0
  have hhiq : r <= n * n / d + 2 := by
    by_contra hh
    have hgap : n * n / d + 3 <= r := by omega
    have hmul := Nat.mul_le_mul_left d hgap
    nlinarith
  omega

/-- Every cube above the lower square automatically meets the repeated-factor cutoff. -/
theorem index_lt_sq_of_cube_gt {n a : Nat} (hlo : n * n < a * a * a) :
    n < a * a := by
  by_contra hh
  have hsq : a * a <= n := by omega
  have ha : a <= n := le_trans (Nat.le_mul_self a) hsq
  have hmul := Nat.mul_le_mul hsq ha
  nlinarith

/-- There is at most one integer cube between consecutive squares. -/
theorem cube_in_square_interval_unique {n a b : Nat}
    (halo : n * n < a * a * a) (hahi : a * a * a < (n + 1) * (n + 1))
    (hblo : n * n < b * b * b) (hbhi : b * b * b < (n + 1) * (n + 1)) :
    a = b := by
  have ha := index_lt_sq_of_cube_gt halo
  have hb := index_lt_sq_of_cube_gt hblo
  rcases lt_trichotomy a b with hab | hab | hba
  next =>
    have hg : a + 1 <= b := by omega
    have hcube := Nat.mul_le_mul (Nat.mul_le_mul hg hg) hg
    nlinarith
  next => exact hab
  next =>
    have hg : b + 1 <= a := by omega
    have hcube := Nat.mul_le_mul (Nat.mul_le_mul hg hg) hg
    nlinarith

end Nat.PrimeSieve
