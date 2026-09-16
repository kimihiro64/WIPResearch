/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareInterval

/-!
# Odd factor-gap cells between consecutive squares

Fixed-gap uniqueness bounds all near-center odd factor pairs, without primality
assumptions. Integer-product images count represented integers only once.
These deterministic pruning bounds do not assert positive prime supply.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- A factorization above the lower square has factor sum greater than twice the index. -/
theorem factor_sum_gt_twice_index {n p g : Nat} (hlo : n * n < p * (p + g)) :
    2 * n < 2 * p + g := by
  by_contra h
  have hs : 2 * p + g <= 2 * n := by omega
  have hsq := Nat.mul_le_mul hs hs
  nlinarith

/-- For a fixed factor difference, at most one factor pair lies between consecutive squares. -/
theorem factor_left_unique_of_gap {n g p r : Nat}
    (hplo : n * n < p * (p + g)) (hphi : p * (p + g) < (n + 1) * (n + 1))
    (hrlo : n * n < r * (r + g)) (hrhi : r * (r + g) < (n + 1) * (n + 1)) :
    p = r := by
  have hpsum := factor_sum_gt_twice_index hplo
  have hrsum := factor_sum_gt_twice_index hrlo
  rcases lt_trichotomy p r with hpr | hpr | hrp
  next =>
    have hgap : p + 1 <= r := by omega
    have hprod := Nat.mul_le_mul hgap (Nat.add_le_add_right hgap g)
    nlinarith
  next => exact hpr
  next =>
    have hgap : r + 1 <= p := by omega
    have hprod := Nat.mul_le_mul hgap (Nat.add_le_add_right hgap g)
    nlinarith

/-- An odd factor pair in the open square interval, parametrized by its positive half-gap. -/
structure OddFactorGapCell (n p t : Nat) : Prop where
  odd_left : p % 2 = 1
  gap_pos : 0 < t
  interval_lower : n * n < p * (p + 2 * t)
  interval_upper : p * (p + 2 * t) < (n + 1) * (n + 1)

/-- All admissible odd factor pairs whose half-gap is at most the given cutoff. -/
noncomputable def oddFactorGapCells (n T : Nat) : Finset (Prod Nat Nat) :=
  ((Finset.range (n + 1)).product (Finset.Icc 1 T)).filter
    (fun x => OddFactorGapCell n x.1 x.2)

/-- The finite search domain contains every admissible cell under its half-gap cutoff. -/
theorem OddFactorGapCell.mem_cells {n p t T : Nat} (h : OddFactorGapCell n p t)
    (hT : t <= T) : Membership.mem (oddFactorGapCells n T) (Prod.mk p t) := by
  have hp := (semiprime_straddles (show p <= p + 2 * t by omega)
    h.interval_lower h.interval_upper).1
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_product.mpr (And.intro (Finset.mem_range.mpr (by omega))
      (Finset.mem_Icc.mpr (And.intro h.gap_pos hT)))) h)

/-- Distinct admissible cells have distinct half-gaps. -/
theorem oddFactorGapCells_snd_injOn (n T : Nat) :
    Set.InjOn (fun x : Prod Nat Nat => x.2) (oddFactorGapCells n T) := by
  intro x hx y hy hxy
  change x.2 = y.2 at hxy
  have hx' : OddFactorGapCell n x.1 x.2 := (Finset.mem_filter.mp hx).2
  have hy' : OddFactorGapCell n y.1 y.2 := (Finset.mem_filter.mp hy).2
  apply Prod.ext ?_ hxy
  have hylo : n * n < y.1 * (y.1 + 2 * x.2) := by rw [hxy]; exact hy'.interval_lower
  have hyhi : y.1 * (y.1 + 2 * x.2) < (n + 1) * (n + 1) := by
    rw [hxy]
    exact hy'.interval_upper
  exact factor_left_unique_of_gap hx'.interval_lower hx'.interval_upper hylo hyhi

/-- The number of odd factor pairs is at most the number of allowed half-gaps. -/
theorem card_oddFactorGapCells_le (n T : Nat) : (oddFactorGapCells n T).card <= T := by
  have hcard : (oddFactorGapCells n T).card <= (Finset.Icc 1 T).card := by
    apply Finset.card_le_card_of_injOn (fun x : Prod Nat Nat => x.2)
    next => intro x hx; exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).2
    next => exact oddFactorGapCells_snd_injOn n T
  simpa using hcard

/-- The integer center of an admissible pair lies strictly above the index. -/
theorem OddFactorGapCell.center_gt {n p t : Nat} (h : OddFactorGapCell n p t) :
    n < p + t := by
  have hs := factor_sum_gt_twice_index h.interval_lower
  omega

/-- A center cutoff gives a strict quadratic bound for the half-gap. -/
theorem OddFactorGapCell.halfGap_sq_lt {n p t J : Nat} (h : OddFactorGapCell n p t)
    (hcenter : p + t <= n + J) : t * t < 2 * n * J + J * J := by
  have hsq := Nat.mul_le_mul hcenter hcenter
  nlinarith [h.interval_lower]

/-- Odd factor pairs whose center is at most the index plus the specified width. -/
noncomputable def oddFactorCenterCells (n J : Nat) : Finset (Prod Nat Nat) :=
  (oddFactorGapCells n (n + J)).filter (fun x => x.1 + x.2 <= n + J)

/-- A square-root capacity bound for all near-center odd factor pairs. -/
theorem card_oddFactorCenterCells_le_sqrt (n J : Nat) :
    (oddFactorCenterCells n J).card <= Nat.sqrt (2 * n * J + J * J - 1) := by
  apply le_trans (Finset.card_le_card (t := oddFactorGapCells n
    (Nat.sqrt (2 * n * J + J * J - 1))) ?_) (card_oddFactorGapCells_le _ _)
  intro x hx
  have hxdata := Finset.mem_filter.mp hx
  have hcell : OddFactorGapCell n x.1 x.2 := (Finset.mem_filter.mp hxdata.1).2
  have hsq := hcell.halfGap_sq_lt hxdata.2
  have ht : x.2 <= Nat.sqrt (2 * n * J + J * J - 1) := Nat.le_sqrt.mpr (by omega)
  exact hcell.mem_cells ht

/-- A sufficiently short factor gap forces the first integer center. -/
theorem OddFactorGapCell.first_center {n p t : Nat} (h : OddFactorGapCell n p t)
    (ht : t * t <= 2 * n) : p + t = n + 1 := by
  have hlo := h.center_gt
  have hs : (p + t) * (p + t) < (n + 2) * (n + 2) := by
    nlinarith [h.interval_upper]
  by_contra hh
  have hge : n + 2 <= p + t := by omega
  have hsq := Nat.mul_le_mul hge hge
  omega

/-- At the first center the half-gap has the same parity as the interval index. -/
theorem OddFactorGapCell.first_center_parity {n p t : Nat} (h : OddFactorGapCell n p t)
    (ht : t * t <= 2 * n) : t % 2 = n % 2 := by
  have hc := h.first_center ht
  have ho := h.odd_left
  omega

/-- The first-center factorization has the exact top-coordinate defect t squared minus one. -/
theorem OddFactorGapCell.top_quadratic_identity {n p t : Nat} (h : OddFactorGapCell n p t)
    (ht : t * t <= 2 * n) : p * (p + 2 * t) + (t * t - 1) = n * n + 2 * n := by
  have hc := h.first_center ht
  have hsq := congrArg (fun x : Nat => x * x) hc
  have htpos : 1 <= t * t := by have := h.gap_pos; nlinarith
  have hsub := Nat.sub_add_cancel htpos
  nlinarith

/-- Distinct integers represented by the near-center odd factor pairs. -/
noncomputable def oddNearCenterProducts (n J : Nat) : Finset Nat :=
  (oddFactorCenterCells n J).image (fun x => x.1 * (x.1 + 2 * x.2))

/-- Count represented integers only once, even when their factorizations differ. -/
theorem card_oddNearCenterProducts_le_sqrt (n J : Nat) :
    (oddNearCenterProducts n J).card <= Nat.sqrt (2 * n * J + J * J - 1) := by
  exact le_trans Finset.card_image_le (card_oddFactorCenterCells_le_sqrt n J)

/-- Every ordered odd factor pair under the center cutoff is represented. -/
theorem mul_mem_oddNearCenterProducts {n p q J : Nat}
    (hp : p % 2 = 1) (hq : q % 2 = 1) (hpq : p <= q)
    (hlo : n * n < p * q) (hhi : p * q < (n + 1) * (n + 1))
    (hcenter : p + q <= 2 * (n + J)) :
    Membership.mem (oddNearCenterProducts n J) (p * q) := by
  have hstraddle := semiprime_straddles hpq hlo hhi
  let t := (q - p) / 2
  have hqeq : q = p + 2 * t := by dsimp [t]; omega
  have htpos : 0 < t := by omega
  have hc : p + t <= n + J := by omega
  have hcell : OddFactorGapCell n p t := by
    refine { odd_left := hp, gap_pos := htpos, interval_lower := ?_, interval_upper := ?_ }
    next => rw [<- hqeq]; exact hlo
    next => rw [<- hqeq]; exact hhi
  apply Finset.mem_image.mpr
  refine Exists.intro (Prod.mk p t) (And.intro ?_ ?_)
  next =>
    exact Finset.mem_filter.mpr (And.intro (hcell.mem_cells (by omega)) hc)
  next => change p * (p + 2 * t) = p * q; rw [<- hqeq]

/-- A fixed gap admits at most one odd factor pair across two adjacent square intervals. -/
theorem odd_factor_left_unique_two_intervals {n g p r : Nat}
    (hpodd : p % 2 = 1) (hrodd : r % 2 = 1)
    (hplo : n*n < p*(p+g)) (hphi : p*(p+g) < (n+2)*(n+2))
    (hrlo : n*n < r*(r+g)) (hrhi : r*(r+g) < (n+2)*(n+2)) : p = r := by
  have hpsum := factor_sum_gt_twice_index hplo
  have hrsum := factor_sum_gt_twice_index hrlo
  rcases lt_trichotomy p r with hpr | hpr | hrp
  next =>
    have hgap : p+2 <= r := by omega
    have hprod := Nat.mul_le_mul hgap (Nat.add_le_add_right hgap g)
    nlinarith
  next => exact hpr
  next =>
    have hgap : r+2 <= p := by omega
    have hprod := Nat.mul_le_mul hgap (Nat.add_le_add_right hgap g)
    nlinarith

end Nat.PrimeSieve
