/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalIncidence

/-!
# Two-sided uniqueness and hyperbola capacity for repeated-prime cells

Both prime projections are injective on the actual square-interval cell set.
Splitting the product p squared times q at a repeated-prime threshold thus
permits a two-sided prime-capacity bound. All repeated cells are retained.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- The pair product of a repeated-factor integer above the lower square exceeds the interval index. -/
theorem index_lt_product_of_repeated_square {n p q : Nat}
    (hq : 1 <= q) (hlo : n*n < p*p*q) : n < p*q := by
  by_contra h
  have hle : p*q <= n := by omega
  have hsq := Nat.mul_le_mul hle hle
  have hmul := Nat.mul_le_mul_left (p*p*q) hq
  nlinarith

/-- For any fixed positive cofactor at most one squared factor occurs between consecutive squares. -/
theorem repeated_cofactor_square_unique {n p r q : Nat} (hq : 1 <= q)
    (hplo : n*n < p*p*q) (hphi : p*p*q < (n+1)*(n+1))
    (hrlo : n*n < r*r*q) (hrhi : r*r*q < (n+1)*(n+1)) : p = r := by
  have hstep (a b : Nat) (hlo : n*n < a*a*q)
      (hhi : b*b*q < (n+1)*(n+1)) (hab : a < b) : False := by
    have hprod := index_lt_product_of_repeated_square hq hlo
    have hgap : a+1 <= b := by omega
    have hsq := Nat.mul_le_mul hgap hgap
    have hscale := Nat.mul_le_mul_right q hsq
    nlinarith
  by_cases he : p = r
  next => exact he
  next =>
    by_cases hpr : p < r
    next => exact False.elim (hstep p r hplo hrhi hpr)
    next => exact False.elim (hstep r p hrlo hphi (by omega))

/-- The actual repeated-prime cell set is injective in its complementary prime as well as its repeated prime. -/
theorem repeatedPrimeCells_snd_injOn (n s : Nat) :
    Set.InjOn (fun x : Prod Nat Nat => x.2) (repeatedPrimeCells n s) := by
  intro x hx y hy hxy
  change x.2 = y.2 at hxy
  have hx' : RepeatedPrimeCell n s x.1 x.2 := (Finset.mem_filter.mp hx).2
  have hy' : RepeatedPrimeCell n s y.1 y.2 := (Finset.mem_filter.mp hy).2
  apply Prod.ext ?_ hxy
  have hylo : n*n < y.1*y.1*x.2 := by rw [hxy]; exact hy'.interval_lower
  have hyhi : y.1*y.1*x.2 < (n+1)*(n+1) := by rw [hxy]; exact hy'.interval_upper
  exact repeated_cofactor_square_unique hx'.prime_right.one_lt.le
    hx'.interval_lower hx'.interval_upper hylo hyhi

/-- Odd primes in the closed integer interval from the lower cutoff through the upper cutoff. -/
def oddPrimesBetween (s T : Nat) : Finset Nat :=
  (Finset.range (T+1)).filter (fun p => Nat.Prime p /\ p % 2 = 1 /\ s <= p)

/-- A threshold split uses both injective projections to bound the complete cell set by two exact odd-prime capacities. -/
theorem card_repeatedPrimeCells_le_hyperbola_capacity (n s T : Nat) :
    (repeatedPrimeCells n s).card <= (oddPrimesBetween s T).card +
      (oddPrimesBetween s ((n*n+2*n)/((T+1)*(T+1)))).card := by
  let c := repeatedPrimeCells n s
  let lo := c.filter (fun x => x.1 <= T)
  let hi := c.filter (fun x => Not (x.1 <= T))
  have hlow : lo.card <= (oddPrimesBetween s T).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    next =>
      intro x hx
      have hm := Finset.mem_filter.mp hx
      have hcell : RepeatedPrimeCell n s x.1 x.2 := (Finset.mem_filter.mp hm.1).2
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
        (And.intro hcell.prime_left (And.intro hcell.odd_left hcell.lower_left)))
    next =>
      intro x hx y hy he
      exact repeatedPrimeCells_fst_injOn n s (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he
  have hhigh : hi.card <= (oddPrimesBetween s ((n*n+2*n)/((T+1)*(T+1)))).card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    next =>
      intro x hx
      have hm := Finset.mem_filter.mp hx
      have hcell : RepeatedPrimeCell n s x.1 x.2 := (Finset.mem_filter.mp hm.1).2
      have hp : T+1 <= x.1 := by omega
      have hsq := Nat.mul_le_mul hp hp
      have hscale := Nat.mul_le_mul_right x.2 hsq
      have hden : 0 < (T+1)*(T+1) := Nat.mul_pos (by omega) (by omega)
      have hq : x.2 <= (n*n+2*n)/((T+1)*(T+1)) :=
        (Nat.le_div_iff_mul_le hden).mpr (by nlinarith [hcell.interval_upper])
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
        (And.intro hcell.prime_right (And.intro hcell.odd_right hcell.lower_right)))
    next =>
      intro x hx y hy he
      exact repeatedPrimeCells_snd_injOn n s (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he
  have hsplit : lo.card + hi.card = c.card := by
    simpa [lo, hi] using
      Finset.sum_filter_add_sum_filter_not c (fun x => x.1 <= T) (fun _ => (1 : Nat))
  change c.card <= _
  omega

/-- A cubic cutoff yields a balanced two-sided odd-prime capacity for every repeated cell. -/
theorem card_repeatedPrimeCells_le_balanced_capacity {n s t : Nat}
    (hcut : (n+1)*(n+1) <= t*t*t) :
    (repeatedPrimeCells n s).card <= 2*(oddPrimesBetween s (t-1)).card := by
  have ht : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    rw [hz] at hcut
    nlinarith
  have he : t-1+1 = t := by omega
  have hcap := card_repeatedPrimeCells_le_hyperbola_capacity n s (t-1)
  rw [he] at hcap
  have hq : (n*n+2*n)/(t*t) <= t-1 := by
    by_contra h
    have hlarge : t <= (n*n+2*n)/(t*t) := by omega
    have hmul := Nat.mul_le_mul_right (t*t) hlarge
    have hdiv := Nat.div_mul_le_self (n*n+2*n) (t*t)
    nlinarith
  have hcard : (oddPrimesBetween s ((n*n+2*n)/(t*t))).card <= (oddPrimesBetween s (t-1)).card := by
    apply Finset.card_le_card
    intro p hp
    have hm := Finset.mem_filter.mp hp
    have hprange := Finset.mem_range.mp hm.1
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega)) hm.2)
  omega

/-- The actual negative incidence correction injects into products of the retained repeated-prime cells. -/
theorem card_twoDistinctSurvivors_le_repeatedCells (n : Nat) :
    (twoDistinctSurvivors n).card <= (repeatedPrimeCells n (Nat.sqrt n+1)).card := by
  let cells := repeatedPrimeCells n (Nat.sqrt n+1)
  let products := cells.image (fun x => x.1*x.1*x.2)
  have hsub : forall m, Membership.mem (twoDistinctSurvivors n) m -> Membership.mem products m := by
    intro m hm
    choose p q h using twoDistinctSurvivor_has_repeated_cell hm
    exact Finset.mem_image.mpr (Exists.intro (Prod.mk p q) (And.intro h.1.mem_cells h.2.symm))
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-- The full negative correction satisfies the balanced cubic-scale prime-capacity bound. -/
theorem card_twoDistinctSurvivors_le_balanced_capacity {n t : Nat}
    (hcut : (n+1)*(n+1) <= t*t*t) :
    (twoDistinctSurvivors n).card <= 2*(oddPrimesBetween (Nat.sqrt n+1) (t-1)).card :=
  le_trans (card_twoDistinctSurvivors_le_repeatedCells n) (card_repeatedPrimeCells_le_balanced_capacity hcut)

/-- The original prime-count identity retains the full signed incidence sum with the improved cubic-scale correction bound. -/
theorem prime_count_second_incidence_balanced_upper {n t : Nat}
    (hn : 2 <= n) (hcut : (n+1)*(n+1) <= t*t*t) :
    3*((squareIntervalPrimes n).card : Int) <=
      3*((squareRoughSurvivors n).card : Int) - 3*firstIncidence n + 2*secondIncidence n +
        2*((oddPrimesBetween (Nat.sqrt n+1) (t-1)).card : Int) := by
  rw [prime_count_second_incidence_identity hn]
  have hcap := card_twoDistinctSurvivors_le_balanced_capacity hcut
  omega

/-- Odd-prime capacity is at most the exact number of odd integer slots in its interval. -/
theorem oddPrimesBetween_card_le (s T : Nat) :
    (oddPrimesBetween s T).card <= (T+1)/2-s/2 := by
  have hcard : (oddPrimesBetween s T).card <= (Finset.Ico (s/2) ((T+1)/2)).card := by
    apply Finset.card_le_card_of_injOn (fun p : Nat => p/2)
    next =>
      intro p hp
      have hm := Finset.mem_filter.mp hp
      have hprange := Finset.mem_range.mp hm.1
      change Membership.mem (Finset.Ico (s/2) ((T+1)/2)) (p/2)
      exact Finset.mem_Ico.mpr (And.intro (by omega) (by omega))
    next =>
      intro p hp q hq he
      have hpodd := (Finset.mem_filter.mp hp).2.2.1
      have hqodd := (Finset.mem_filter.mp hq).2.2.1
      change p/2 = q/2 at he
      omega
  simpa using hcard

/-- The full negative incidence correction obeys an elementary pointwise cubic-cutoff bound. -/
theorem card_twoDistinctSurvivors_le_cubic_cutoff {n t : Nat}
    (hcut : (n+1)*(n+1) <= t*t*t) :
    (twoDistinctSurvivors n).card <= t-Nat.sqrt n := by
  have ht : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    rw [hz] at hcut
    nlinarith
  have he : t-1+1 = t := by omega
  have hcap := card_twoDistinctSurvivors_le_balanced_capacity hcut
  have hodd := oddPrimesBetween_card_le (Nat.sqrt n+1) (t-1)
  rw [he] at hodd
  omega

/-- The original signed prime-count identity has an explicit cubic-cutoff upper correction. -/
theorem prime_count_second_incidence_cubic_upper {n t : Nat}
    (hn : 2 <= n) (hcut : (n+1)*(n+1) <= t*t*t) :
    3*((squareIntervalPrimes n).card : Int) <=
      3*((squareRoughSurvivors n).card : Int) - 3*firstIncidence n + 2*secondIncidence n +
        ((t-Nat.sqrt n : Nat) : Int) := by
  rw [prime_count_second_incidence_identity hn]
  have hcap := card_twoDistinctSurvivors_le_cubic_cutoff hcut
  omega

/-- A prime-free square interval would force the complete joint sum into this narrow nonpositive window. -/
theorem no_prime_forces_cubic_joint_window {n t : Nat}
    (hn : 2 <= n) (hcut : (n+1)*(n+1) <= t*t*t)
    (hno : (squareIntervalPrimes n).card = 0) :
    let L := 3*((squareRoughSurvivors n).card : Int) - 3*firstIncidence n + 2*secondIncidence n;
    -((t-Nat.sqrt n : Nat) : Int) <= L /\ L <= 0 := by
  have he := prime_count_second_incidence_identity hn
  rw [hno] at he
  have hcap := card_twoDistinctSurvivors_le_cubic_cutoff hcut
  dsimp only
  constructor <;> omega

/-- The integer immediately above the cube root of the upper endpoint is an admissible cubic cutoff. -/
theorem square_cubic_cutoff (n : Nat) :
    (n+1)*(n+1) <= (Nat.nthRoot 3 (n*n+2*n)+1)*
      (Nat.nthRoot 3 (n*n+2*n)+1)*(Nat.nthRoot 3 (n*n+2*n)+1) := by
  have h := Nat.lt_pow_nthRoot_add_one (n := 3) (by decide) (n*n+2*n)
  nlinarith

/-- A parameter-free cubic-root bound on the actual repeated-prime correction. -/
theorem card_twoDistinctSurvivors_le_cubic_root (n : Nat) :
    (twoDistinctSurvivors n).card <= Nat.nthRoot 3 (n*n+2*n)+1-Nat.sqrt n :=
  card_twoDistinctSurvivors_le_cubic_cutoff (square_cubic_cutoff n)

/-- Any prime-free square interval forces the original signed sum into the explicit cubic-root window. -/
theorem no_prime_forces_cubic_root_joint_window {n : Nat} (hn : 2 <= n)
    (hno : (squareIntervalPrimes n).card = 0) :
    let L := 3*((squareRoughSurvivors n).card : Int) - 3*firstIncidence n + 2*secondIncidence n;
    -((Nat.nthRoot 3 (n*n+2*n)+1-Nat.sqrt n : Nat) : Int) <= L /\ L <= 0 :=
  no_prime_forces_cubic_joint_window hn (square_cubic_cutoff n) hno

end Nat.PrimeSieve
