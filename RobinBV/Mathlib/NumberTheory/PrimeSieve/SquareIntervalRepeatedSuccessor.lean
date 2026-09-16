/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalRepeatedHyperbola

/-!
# Shared repeated-prime capacity across adjacent square intervals

Odd squared factors with the same positive cofactor cannot both occur inside
the entire two-window range. Adjacent correction packets therefore have
disjoint complementary-prime resources; the two packets remain coupled.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- Across two consecutive square intervals a positive cofactor permits at most one odd squared factor. -/
theorem repeated_cofactor_two_square_unique {n p r q : Nat} (hq : 1 <= q)
    (hpodd : p%2 = 1) (hrodd : r%2 = 1)
    (hplo : n*n < p*p*q) (hphi : p*p*q < (n+2)*(n+2))
    (hrlo : n*n < r*r*q) (hrhi : r*r*q < (n+2)*(n+2)) : p = r := by
  have hstep (a b : Nat) (haodd : a%2 = 1) (hbodd : b%2 = 1)
      (hlo : n*n < a*a*q) (hhi : b*b*q < (n+2)*(n+2)) (hab : a < b) : False := by
    have hprod := index_lt_product_of_repeated_square hq hlo
    have hgap : a+2 <= b := by omega
    have hsq := Nat.mul_le_mul hgap hgap
    have hscale := Nat.mul_le_mul_right q hsq
    nlinarith
  by_cases he : p = r
  next => exact he
  next =>
    by_cases hpr : p < r
    next => exact False.elim (hstep p r hpodd hrodd hplo hrhi hpr)
    next => exact False.elim (hstep r p hrodd hpodd hrlo hphi (by omega))

/-- Adjacent repeated-prime packets cannot use the same complementary prime, even with different lower cutoffs. -/
theorem repeatedPrimeCells_snd_disjoint_successor (n s t : Nat) :
    Disjoint ((repeatedPrimeCells n s).image Prod.snd)
      ((repeatedPrimeCells (n+1) t).image Prod.snd) := by
  apply Finset.disjoint_left.mpr
  intro q hq0 hq1
  choose x hx using Finset.mem_image.mp hq0
  choose y hy using Finset.mem_image.mp hq1
  have hc0 : RepeatedPrimeCell n s x.1 x.2 := (Finset.mem_filter.mp hx.1).2
  have hc1 : RepeatedPrimeCell (n+1) t y.1 y.2 := (Finset.mem_filter.mp hy.1).2
  have heq : x.2 = y.2 := hx.2.trans hy.2.symm
  have hylo : n*n < y.1*y.1*x.2 := by rw [heq]; nlinarith [hc1.interval_lower]
  have hyhi : y.1*y.1*x.2 < (n+2)*(n+2) := by rw [heq]; nlinarith [hc1.interval_upper]
  have hxe : x.1 = y.1 := repeated_cofactor_two_square_unique hc0.prime_right.one_lt.le
    hc0.odd_left hc1.odd_left hc0.interval_lower (by nlinarith [hc0.interval_upper]) hylo hyhi
  have hhi := hc0.interval_upper
  rw [hxe, heq] at hhi
  nlinarith [hc1.interval_lower]

/-- A shared hyperbola split counts large-factor complementary primes only once across both intervals. -/
theorem card_repeatedPrimeCells_successor_hyperbola_capacity (n s T : Nat) :
    (repeatedPrimeCells n s).card + (repeatedPrimeCells (n+1) s).card <=
      2*(oddPrimesBetween s T).card +
      (oddPrimesBetween s (((n+1)*(n+3))/((T+1)*(T+1)))).card := by
  let lo (k : Nat) := (repeatedPrimeCells k s).filter (fun x => x.1 <= T)
  let hi (k : Nat) := (repeatedPrimeCells k s).filter (fun x => Not (x.1 <= T))
  let im (k : Nat) := (hi k).image Prod.snd
  let cap := oddPrimesBetween s (((n+1)*(n+3))/((T+1)*(T+1)))
  have hlow (k : Nat) : (lo k).card <= (oddPrimesBetween s T).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    next =>
      intro x hx
      have hm := Finset.mem_filter.mp hx
      have hc : RepeatedPrimeCell k s x.1 x.2 := (Finset.mem_filter.mp hm.1).2
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
        (And.intro hc.prime_left (And.intro hc.odd_left hc.lower_left)))
    next =>
      intro x hx y hy he
      exact repeatedPrimeCells_fst_injOn k s (Finset.mem_filter.mp hx).1
        (Finset.mem_filter.mp hy).1 he
  have himcard (k : Nat) : (im k).card = (hi k).card := by
    apply Finset.card_image_iff.mpr
    intro x hx y hy he
    exact repeatedPrimeCells_snd_injOn k s (Finset.mem_filter.mp hx).1
      (Finset.mem_filter.mp hy).1 he
  have himsub (k : Nat) : forall q, Membership.mem (im k) q ->
      Membership.mem ((repeatedPrimeCells k s).image Prod.snd) q := by
    intro q hq
    choose x hx using Finset.mem_image.mp hq
    exact Finset.mem_image.mpr (Exists.intro x (And.intro (Finset.mem_filter.mp hx.1).1 hx.2))
  have himcap (k : Nat) (hk : k <= n+1) : forall q,
      Membership.mem (im k) q -> Membership.mem cap q := by
    intro q hq
    choose x hx using Finset.mem_image.mp hq
    have hm := Finset.mem_filter.mp hx.1
    have hc : RepeatedPrimeCell k s x.1 x.2 := (Finset.mem_filter.mp hm.1).2
    have hp : T+1 <= x.1 := by omega
    have hsq := Nat.mul_le_mul hp hp
    have hscale := Nat.mul_le_mul_right x.2 hsq
    have hk' : k+1 <= n+2 := by omega
    have hksq := Nat.mul_le_mul hk' hk'
    have hden : 0 < (T+1)*(T+1) := Nat.mul_pos (by omega) (by omega)
    have hqbound : x.2 <= ((n+1)*(n+3))/((T+1)*(T+1)) :=
      (Nat.le_div_iff_mul_le hden).mpr (by nlinarith [hc.interval_upper])
    have hmem : Membership.mem cap x.2 := Finset.mem_filter.mpr
      (And.intro (Finset.mem_range.mpr (by omega))
        (And.intro hc.prime_right (And.intro hc.odd_right hc.lower_right)))
    rw [hx.2] at hmem
    exact hmem
  have hdis : Disjoint (im n) (im (n+1)) := by
    apply Finset.disjoint_left.mpr
    intro q hq0 hq1
    exact Finset.disjoint_left.mp (repeatedPrimeCells_snd_disjoint_successor n s s)
      (himsub n q hq0) (himsub (n+1) q hq1)
  have hucap : (Union.union (im n) (im (n+1))).card <= cap.card := by
    apply Finset.card_le_card
    intro q hq
    cases Finset.mem_union.mp hq with
    | inl h => exact himcap n (by omega) q h
    | inr h => exact himcap (n+1) (by omega) q h
  have hsum := Finset.card_union_of_disjoint hdis
  rw [himcard n, himcard (n+1)] at hsum
  have hsplit (k : Nat) : (lo k).card + (hi k).card = (repeatedPrimeCells k s).card := by
    simpa [lo, hi] using Finset.sum_filter_add_sum_filter_not
      (repeatedPrimeCells k s) (fun x => x.1 <= T) (fun _ => (1 : Nat))
  have hl0 := hlow n
  have hl1 := hlow (n+1)
  have hs0 := hsplit n
  have hs1 := hsplit (n+1)
  change _ <= 2*(oddPrimesBetween s T).card + cap.card
  omega

/-- At a common cubic cutoff the two complete cell packets have a threefold, not fourfold, odd-prime capacity. -/
theorem card_repeatedPrimeCells_successor_balanced_capacity {n s t : Nat}
    (hcut : (n+2)*(n+2) <= t*t*t) :
    (repeatedPrimeCells n s).card + (repeatedPrimeCells (n+1) s).card <=
      3*(oddPrimesBetween s (t-1)).card := by
  have ht : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    rw [hz] at hcut
    nlinarith
  have he : t-1+1 = t := by omega
  have hcap := card_repeatedPrimeCells_successor_hyperbola_capacity n s (t-1)
  rw [he] at hcap
  have hq : ((n+1)*(n+3))/(t*t) <= t-1 := by
    by_contra h
    have hlarge : t <= ((n+1)*(n+3))/(t*t) := by omega
    have hmul := Nat.mul_le_mul_right (t*t) hlarge
    have hdiv := Nat.div_mul_le_self ((n+1)*(n+3)) (t*t)
    nlinarith
  have hcard : (oddPrimesBetween s (((n+1)*(n+3))/(t*t))).card <=
      (oddPrimesBetween s (t-1)).card := by
    apply Finset.card_le_card
    intro p hp
    have hm := Finset.mem_filter.mp hp
    have hprange := Finset.mem_range.mp hm.1
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega)) hm.2)
  omega

/-- The actual adjacent negative corrections obey the shared cubic-scale capacity. -/
theorem card_twoDistinctSurvivors_successor_balanced_capacity {n t : Nat}
    (hcut : (n+2)*(n+2) <= t*t*t) :
    (twoDistinctSurvivors n).card + (twoDistinctSurvivors (n+1)).card <=
      3*(oddPrimesBetween (Nat.sqrt n+1) (t-1)).card := by
  have h0 := card_twoDistinctSurvivors_le_repeatedCells n
  have h1 := card_twoDistinctSurvivors_le_repeatedCells (n+1)
  have hmono : (repeatedPrimeCells (n+1) (Nat.sqrt (n+1)+1)).card <=
      (repeatedPrimeCells (n+1) (Nat.sqrt n+1)).card := by
    apply Finset.card_le_card
    intro x hx
    have hm := Finset.mem_filter.mp hx
    have hc : RepeatedPrimeCell (n+1) (Nat.sqrt (n+1)+1) x.1 x.2 := hm.2
    have hsqrt := Nat.sqrt_le_sqrt (show n <= n+1 by omega)
    have hleft := hc.lower_left
    have hright := hc.lower_right
    exact Finset.mem_filter.mpr (And.intro hm.1
      { hc with lower_left := by omega, lower_right := by omega })
  have hcap := card_repeatedPrimeCells_successor_balanced_capacity (s := Nat.sqrt n+1) hcut
  omega

/-- The shared quadratic capacity bounds the complete signed successor comparison with its prime supply and old correction retained. -/
theorem joint_incidence_successor_shared_correction_lower {n t : Nat}
    (hn : 2 <= n) (hcut : (n+2)*(n+2) <= t*t*t) :
    let L := fun k => 3*((squareRoughSurvivors k).card : Int) -
      3*firstIncidence k + 2*secondIncidence k;
    3*(2*((squareIntervalPrimes (n+1)).card : Int) +
      ((twoDistinctSurvivors n).card : Int) - ((squareIntervalPrimes n).card : Int)) -
      6*((oddPrimesBetween (Nat.sqrt n+1) (t-1)).card : Int) <= 2*L (n+1)-L n := by
  have h0 := prime_count_second_incidence_identity hn
  have h1 := prime_count_second_incidence_identity (show 2 <= n+1 by omega)
  have hcap := card_twoDistinctSurvivors_successor_balanced_capacity hcut
  dsimp only
  omega

end Nat.PrimeSieve
