/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Sqrt
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalCounts

/-!
# Exact first and second incidences in square intervals

At the roughness cutoff n < p squared, every survivor has at most three
medium prime divisors. A quadratic indicator identity eliminates the explicit
third incidence, leaving precisely the two-distinct-prime survivor count.
Its pointwise majorant retains the exact repeated-prime capacity. None of
these identities assumes or asserts positivity of the retained expression.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- Prime divisors at most the interval index; roughness is imposed on the survivor set. -/
def mediumPrimeDivisors (n m : Nat) : Finset Nat :=
  (Finset.range (n + 1)).filter (fun p => Nat.Prime p /\ Dvd.dvd p m)

/-- The number of distinct medium prime divisors, without multiplicities. -/
def mediumPrimeCount (n m : Nat) : Nat := (mediumPrimeDivisors n m).card

/-- A prime above the lower square has no medium prime divisor. -/
theorem mediumPrimeDivisors_prime {n m : Nat} (hm : Nat.Prime m) (hlo : n * n < m) :
    mediumPrimeDivisors n m = {} := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hd := Finset.mem_filter.mp hp
  have hpm : p = m := (hm.eq_one_or_self_of_dvd p hd.2.2).resolve_left hd.2.1.ne_one
  have hpn := Finset.mem_range.mp hd.1
  subst p
  nlinarith

/-- Exactly the smaller factor of a semiprime in the interval is a medium divisor. -/
theorem mediumPrimeDivisors_two {n p q : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p <= q) (hlo : n * n < p * q)
    (hhi : p * q < (n + 1) * (n + 1)) :
    mediumPrimeDivisors n (p * q) = {p} := by
  have hbounds := semiprime_straddles hpq hlo hhi
  ext t
  simp only [mediumPrimeDivisors, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  next =>
    intro ht
    rcases ht.2.1.dvd_mul.mp ht.2.2 with htp | htq
    next => exact (hp.eq_one_or_self_of_dvd t htp).resolve_left ht.2.1.ne_one
    next =>
      have htqeq := (hq.eq_one_or_self_of_dvd t htq).resolve_left ht.2.1.ne_one
      omega
  next =>
    intro ht
    subst t
    exact And.intro (by omega) (And.intro hp (dvd_mul_right p q))

/-- All distinct factors of a rough three-prime product are medium divisors. -/
theorem mediumPrimeDivisors_three {n p q r : Nat}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p <= q) (hqr : q <= r)
    (hhi : p * q * r < (n + 1) * (n + 1))
    (hcutp : n < p * p) (hcutq : n < q * q) :
    mediumPrimeDivisors n (p * q * r) = {p, q, r} := by
  have hrn := cofactor_le_index (index_lt_mul_of_sq_lt hcutp hcutq) hhi
  ext t
  simp only [mediumPrimeDivisors, Finset.mem_filter, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  next =>
    intro ht
    rcases ht.2.1.dvd_mul.mp ht.2.2 with htpq | htr
    next =>
      rcases ht.2.1.dvd_mul.mp htpq with htp | htq
      next => exact Or.inl ((hp.eq_one_or_self_of_dvd t htp).resolve_left ht.2.1.ne_one)
      next => exact Or.inr (Or.inl ((hq.eq_one_or_self_of_dvd t htq).resolve_left ht.2.1.ne_one))
    next => exact Or.inr (Or.inr ((hr.eq_one_or_self_of_dvd t htr).resolve_left ht.2.1.ne_one))
  next =>
    intro ht
    rcases ht with ht | ht | ht
    next =>
      subst t
      exact And.intro (by omega) (And.intro hp
        (Exists.intro (q * r) (by ac_rfl)))
    next =>
      subst t
      exact And.intro (by omega) (And.intro hq
        (Exists.intro (p * r) (by ac_rfl)))
    next =>
      subst t
      exact And.intro (by omega) (And.intro hr (dvd_mul_left r (p * q)))

/-- A rough survivor has at most three distinct medium prime divisors. -/
theorem mediumPrimeCount_le_three {n m : Nat}
    (hm : Membership.mem (squareRoughSurvivors n) m) : mediumPrimeCount n m <= 3 := by
  have hd := Finset.mem_filter.mp hm
  have hhi := Finset.mem_range.mp hd.1
  rcases rough_prime_or_two_or_three hd.2.1 hhi hd.2.2.2.2 with hprime | htwo | hthree
  next => simp [mediumPrimeCount, mediumPrimeDivisors_prime hprime hd.2.2.1]
  next =>
    choose p q h using htwo
    have hlo : n * n < p * q := by rw [<- h.2.2.2]; exact hd.2.2.1
    have hhi' : p * q < (n + 1) * (n + 1) := by rw [<- h.2.2.2]; exact hhi
    rw [h.2.2.2, mediumPrimeCount, mediumPrimeDivisors_two h.1 h.2.1 h.2.2.1 hlo hhi']
    simp
  next =>
    choose p q r h using hthree
    have hcutp : n < p * p := hd.2.2.2.2 p h.1
      (by rw [h.2.2.2.2.2]; exact Exists.intro (q * r) (by ac_rfl))
    have hcutq : n < q * q := hd.2.2.2.2 q h.2.1
      (by rw [h.2.2.2.2.2]; exact Exists.intro (p * r) (by ac_rfl))
    have hhi' : p * q * r < (n + 1) * (n + 1) := by rw [<- h.2.2.2.2.2]; exact hhi
    rw [h.2.2.2.2.2, mediumPrimeCount,
      mediumPrimeDivisors_three h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hhi' hcutp hcutq]
    exact le_trans (Finset.card_insert_le _ _) (by
      have hqr := Finset.card_insert_le q ({r} : Finset Nat)
      simp only [Finset.card_singleton] at hqr
      omega)

/-- Zero medium divisors characterizes primality on the actual rough survivor set. -/
theorem mediumPrimeCount_eq_zero_iff {n m : Nat}
    (hm : Membership.mem (squareRoughSurvivors n) m) :
    mediumPrimeCount n m = 0 <-> Nat.Prime m := by
  have hd := Finset.mem_filter.mp hm
  have hhi := Finset.mem_range.mp hd.1
  constructor
  next =>
    intro hzero
    rcases rough_prime_or_two_or_three hd.2.1 hhi hd.2.2.2.2 with hprime | htwo | hthree
    next => exact hprime
    next =>
      choose p q h using htwo
      have hlo : n * n < p * q := by rw [<- h.2.2.2]; exact hd.2.2.1
      have hhi' : p * q < (n + 1) * (n + 1) := by rw [<- h.2.2.2]; exact hhi
      rw [h.2.2.2, mediumPrimeCount,
        mediumPrimeDivisors_two h.1 h.2.1 h.2.2.1 hlo hhi'] at hzero
      simp at hzero
    next =>
      choose p q r h using hthree
      have hcutp : n < p * p := hd.2.2.2.2 p h.1
        (by rw [h.2.2.2.2.2]; exact Exists.intro (q * r) (by ac_rfl))
      have hcutq : n < q * q := hd.2.2.2.2 q h.2.1
        (by rw [h.2.2.2.2.2]; exact Exists.intro (p * r) (by ac_rfl))
      have hhi' : p * q * r < (n + 1) * (n + 1) := by rw [<- h.2.2.2.2.2]; exact hhi
      rw [h.2.2.2.2.2, mediumPrimeCount,
        mediumPrimeDivisors_three h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hhi' hcutp hcutq] at hzero
      have hempty := Finset.card_eq_zero.mp hzero
      have hmem : Membership.mem ({p, q, r} : Finset Nat) p := by simp
      rw [hempty] at hmem
      simp at hmem
  next =>
    intro hp
    simp [mediumPrimeCount, mediumPrimeDivisors_prime hp hd.2.2.1]

/-- Exact quadratic prime indicator with the two-distinct-divisor correction retained. -/
theorem mediumPrimeCount_indicator {n m : Nat}
    (hm : Membership.mem (squareRoughSurvivors n) m) :
    3 * (if Nat.Prime m then (1 : Int) else 0) =
      3 - 3 * (mediumPrimeCount n m : Int) +
        2 * (Nat.choose (mediumPrimeCount n m) 2 : Int) +
          (if mediumPrimeCount n m = 2 then 1 else 0) := by
  have hle := mediumPrimeCount_le_three hm
  have hiff := mediumPrimeCount_eq_zero_iff hm
  by_cases h0 : mediumPrimeCount n m = 0
  next => have hp := hiff.mp h0; simp [h0, hp]
  next =>
    have hnp : Not (Nat.Prime m) := fun hp => h0 (hiff.mpr hp)
    have hcases : mediumPrimeCount n m = 1 \/ mediumPrimeCount n m = 2 \/
        mediumPrimeCount n m = 3 := by omega
    rcases hcases with h1 | h2 | h3
    next => norm_num [h1, hnp]
    next => norm_num [h2, hnp]
    next => norm_num [h3, hnp]

/-- The first incidence of actual medium prime divisors over the survivor set. -/
noncomputable def firstIncidence (n : Nat) : Int :=
  (squareRoughSurvivors n).sum (fun m => (mediumPrimeCount n m : Int))

/-- The second, unordered distinct-prime incidence over the same survivor set. -/
noncomputable def secondIncidence (n : Nat) : Int :=
  (squareRoughSurvivors n).sum (fun m => (Nat.choose (mediumPrimeCount n m) 2 : Int))

/-- Actual survivors having precisely two distinct medium prime divisors. -/
noncomputable def twoDistinctSurvivors (n : Nat) : Finset Nat :=
  (squareRoughSurvivors n).filter (fun m => mediumPrimeCount n m = 2)

/-- Exact second-incidence cancellation over the entire rough survivor set. -/
theorem exact_second_incidence (n : Nat) :
    3 * (((squareRoughSurvivors n).filter Nat.Prime).card : Int) =
      3 * ((squareRoughSurvivors n).card : Int) - 3 * firstIncidence n +
        2 * secondIncidence n + ((twoDistinctSurvivors n).card : Int) := by
  have heq := Finset.sum_congr (show squareRoughSurvivors n = squareRoughSurvivors n from rfl)
    (fun m hm => mediumPrimeCount_indicator hm)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    <- Finset.mul_sum, Finset.sum_boole, Finset.sum_const, nsmul_eq_mul] at heq
  simpa only [firstIncidence, secondIncidence, twoDistinctSurvivors, mul_comm] using heq

/-- The second-incidence identity counts actual primes in the open square interval. -/
theorem prime_count_second_incidence_identity {n : Nat} (hn : 2 <= n) :
    3 * ((squareIntervalPrimes n).card : Int) =
      3 * ((squareRoughSurvivors n).card : Int) - 3 * firstIncidence n +
        2 * secondIncidence n + ((twoDistinctSurvivors n).card : Int) := by
  rw [<- squareRoughSurvivors_filter_prime hn]
  exact exact_second_incidence n

/-- Dropping the nonnegative repeated-factor correction gives a pointwise lower bound. -/
theorem prime_count_second_incidence_lower_bound {n : Nat} (hn : 2 <= n) :
    3 * ((squareRoughSurvivors n).card : Int) - 3 * firstIncidence n +
      2 * secondIncidence n <= 3 * ((squareIntervalPrimes n).card : Int) := by
  rw [prime_count_second_incidence_identity hn]
  omega

/-- Positivity of the retained joint incidence expression suffices for an interval prime. -/
theorem prime_exists_of_second_incidence_positive {n : Nat} (hn : 2 <= n)
    (hpos : 0 < 3 * ((squareRoughSurvivors n).card : Int) - 3 * firstIncidence n +
      2 * secondIncidence n) :
    exists m : Nat, n * n < m /\ m < (n + 1) * (n + 1) /\ Nat.Prime m := by
  have hbound := prime_count_second_incidence_lower_bound hn
  have hc : 0 < (squareIntervalPrimes n).card := by omega
  choose m hm using Finset.card_pos.mp hc
  have hd := Finset.mem_filter.mp hm
  exact Exists.intro m (And.intro hd.2.1 (And.intro (Finset.mem_range.mp hd.1) hd.2.2))

/-- Every repeated-prime survivor yields a cell with the exact integer roughness cutoff. -/
theorem repeatedPrimeCell_of_survivor {n m p r : Nat}
    (hm : Membership.mem (squareRoughSurvivors n) m)
    (hp : Nat.Prime p) (hr : Nat.Prime r) (heq : m = p * p * r) :
    RepeatedPrimeCell n (Nat.sqrt n + 1) p r := by
  have hd := Finset.mem_filter.mp hm
  have hpd : Dvd.dvd p m := by rw [heq]; exact Exists.intro (p * r) (by ac_rfl)
  have hrd : Dvd.dvd r m := by rw [heq]; exact dvd_mul_left r (p * p)
  have hcutp := hd.2.2.2.2 p hp hpd
  have hcutr := hd.2.2.2.2 r hr hrd
  have hodd : forall t : Nat, Nat.Prime t -> Dvd.dvd t m -> t % 2 = 1 := by
    intro t ht htd
    apply ht.eq_two_or_odd.resolve_left
    intro ht2
    rw [ht2] at htd
    have hz := Nat.mod_eq_zero_of_dvd htd
    omega
  refine RepeatedPrimeCell.mk hp hr (Nat.sqrt_lt.mpr hcutp) (Nat.sqrt_lt.mpr hcutr)
    hcutp (hodd p hp hpd) (hodd r hr hrd) ?_ ?_
  next => rw [<- heq]; exact hd.2.2.1
  next => rw [<- heq]; exact Finset.mem_range.mp hd.1

/-- Every two-distinct-divisor survivor is represented by a repeated-prime cell. -/
theorem twoDistinctSurvivor_has_repeated_cell {n m : Nat}
    (hm : Membership.mem (twoDistinctSurvivors n) m) :
    exists p r : Nat, RepeatedPrimeCell n (Nat.sqrt n + 1) p r /\ m = p * p * r := by
  have hmem := Finset.mem_filter.mp hm
  have hd := Finset.mem_filter.mp hmem.1
  have hhi := Finset.mem_range.mp hd.1
  rcases rough_prime_or_two_or_three hd.2.1 hhi hd.2.2.2.2 with hprime | htwo | hthree
  next =>
    have hz := (mediumPrimeCount_eq_zero_iff hmem.1).mpr hprime
    omega
  next =>
    choose p q h using htwo
    have hlo : n * n < p * q := by rw [<- h.2.2.2]; exact hd.2.2.1
    have hhi' : p * q < (n + 1) * (n + 1) := by rw [<- h.2.2.2]; exact hhi
    have hcount := hmem.2
    rw [h.2.2.2, mediumPrimeCount,
      mediumPrimeDivisors_two h.1 h.2.1 h.2.2.1 hlo hhi'] at hcount
    simp at hcount
  next =>
    choose p q r h using hthree
    have hcutp : n < p * p := hd.2.2.2.2 p h.1
      (by rw [h.2.2.2.2.2]; exact Exists.intro (q * r) (by ac_rfl))
    have hcutq : n < q * q := hd.2.2.2.2 q h.2.1
      (by rw [h.2.2.2.2.2]; exact Exists.intro (p * r) (by ac_rfl))
    have hhi' : p * q * r < (n + 1) * (n + 1) := by rw [<- h.2.2.2.2.2]; exact hhi
    by_cases hpq : p = q
    next =>
      have heq : m = p * p * r := by simpa only [hpq] using h.2.2.2.2.2
      exact Exists.intro p (Exists.intro r
        (And.intro (repeatedPrimeCell_of_survivor hmem.1 h.1 h.2.2.1 heq) heq))
    next =>
      by_cases hqr : q = r
      next =>
        have heq : m = q * q * p := by rw [h.2.2.2.2.2, <- hqr]; ac_rfl
        exact Exists.intro q (Exists.intro p
          (And.intro (repeatedPrimeCell_of_survivor hmem.1 h.2.1 h.1 heq) heq))
      next =>
        have hpr : Not (p = r) := by omega
        have hcount := hmem.2
        rw [h.2.2.2.2.2, mediumPrimeCount,
          mediumPrimeDivisors_three h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hhi' hcutp hcutq] at hcount
        simp [hpq, hqr, hpr] at hcount

/-- The complete incidence correction is bounded by the exact repeated-prime capacity. -/
theorem card_twoDistinctSurvivors_le_capacity (n : Nat) :
    (twoDistinctSurvivors n).card <= (repeatedPrimeCapacity n (Nat.sqrt n + 1)).card := by
  let cells := repeatedPrimeCells n (Nat.sqrt n + 1)
  let products := cells.image (fun x => x.1 * x.1 * x.2)
  have hsub : forall m : Nat, Membership.mem (twoDistinctSurvivors n) m ->
      Membership.mem products m := by
    intro m hm
    choose p r h using twoDistinctSurvivor_has_repeated_cell hm
    exact Finset.mem_image.mpr (Exists.intro (Prod.mk p r) (And.intro h.1.mem_cells h.2.symm))
  exact le_trans (Finset.card_le_card hsub)
    (le_trans Finset.card_image_le (card_repeatedPrimeCells_le_capacity n (Nat.sqrt n + 1)))

/-- The exact repeated-prime capacity bounds the full remainder in the lower estimate. -/
theorem prime_count_second_incidence_upper_bound {n : Nat} (hn : 2 <= n) :
    3 * ((squareIntervalPrimes n).card : Int) <=
      3 * ((squareRoughSurvivors n).card : Int) - 3 * firstIncidence n +
        2 * secondIncidence n + ((repeatedPrimeCapacity n (Nat.sqrt n + 1)).card : Int) := by
  rw [prime_count_second_incidence_identity hn]
  have hcap := card_twoDistinctSurvivors_le_capacity n
  omega

/-- The complete signed weight of the zeroth, first and second divisor incidences. -/
def jointIncidenceWeight (v : Nat) : Int :=
  3 - 3 * (v : Int) + 2 * (Nat.choose v 2 : Int)

/-- Adding one distinct divisor retains the exact joint first-and-second-incidence change. -/
theorem jointIncidenceWeight_succ (v : Nat) :
    jointIncidenceWeight (v + 1) = jointIncidenceWeight v + 2 * (v : Int) - 3 := by
  simp only [jointIncidenceWeight, Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add,
    Nat.cast_one]
  ring

/-- An inserted divisor changes the combined weight only on its actual multiples. -/
theorem jointIncidenceWeight_insert (b : Finset Nat) (p m : Nat)
    (hp : Not (Membership.mem b p)) :
    jointIncidenceWeight (((insert p b).filter (fun q => Dvd.dvd q m)).card) =
      jointIncidenceWeight ((b.filter (fun q => Dvd.dvd q m)).card) +
        (if Dvd.dvd p m then 2 * ((b.filter (fun q => Dvd.dvd q m)).card : Int) - 3 else 0) := by
  have hpf : Not (Membership.mem (b.filter (fun q => Dvd.dvd q m)) p) :=
    fun h => hp (Finset.mem_filter.mp h).1
  by_cases hd : Dvd.dvd p m
  next =>
    simp only [Finset.filter_insert, hd, if_true, Finset.card_insert_of_notMem hpf]
    rw [jointIncidenceWeight_succ]
    ring
  next => simp [Finset.filter_insert, hd]

/-- Exact combined incidence correction when a previously absent divisor is admitted. -/
theorem sum_jointIncidenceWeight_insert (s b : Finset Nat) (p : Nat)
    (hp : Not (Membership.mem b p)) :
    s.sum (fun m => jointIncidenceWeight (((insert p b).filter (fun q => Dvd.dvd q m)).card)) =
      s.sum (fun m => jointIncidenceWeight ((b.filter (fun q => Dvd.dvd q m)).card)) +
        2 * (s.filter (fun m => Dvd.dvd p m)).sum
          (fun m => ((b.filter (fun q => Dvd.dvd q m)).card : Int)) -
        3 * ((s.filter (fun m => Dvd.dvd p m)).card : Int) := by
  simp_rw [jointIncidenceWeight_insert b p _ hp]
  rw [Finset.sum_add_distrib, <- Finset.sum_filter]
  simp only [Finset.sum_sub_distrib, <- Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Admitting a divisor loses at most three times its exact number of occupied cells. -/
theorem sum_jointIncidenceWeight_insert_lower (s b : Finset Nat) (p : Nat)
    (hp : Not (Membership.mem b p)) :
    s.sum (fun m => jointIncidenceWeight ((b.filter (fun q => Dvd.dvd q m)).card)) -
        3 * ((s.filter (fun m => Dvd.dvd p m)).card : Int) <=
      s.sum (fun m => jointIncidenceWeight (((insert p b).filter (fun q => Dvd.dvd q m)).card)) := by
  rw [sum_jointIncidenceWeight_insert s b p hp]
  have hs : (0 : Int) <= (s.filter (fun m => Dvd.dvd p m)).sum
      (fun m => ((b.filter (fun q => Dvd.dvd q m)).card : Int)) :=
    Finset.sum_nonneg (fun m hm => Int.natCast_nonneg _)
  omega

/-- Four distinct prime divisors at least r cannot fit below the square following r squared. -/
theorem card_large_prime_divisors_le_three {r m : Nat} (hr : 3 <= r)
    (hm : 0 < m) (hhi : m < (r * r + 1) * (r * r + 1)) (b : Finset Nat)
    (hprime : forall p, Membership.mem b p -> Nat.Prime p)
    (hlow : forall p, Membership.mem b p -> r <= p)
    (hdiv : forall p, Membership.mem b p -> Dvd.dvd p m) : b.card <= 3 := by
  by_contra hcard
  have hfour : 4 <= b.card := by omega
  have hex : exists p : Nat, Membership.mem b p /\ r < p := by
    by_contra hnone
    have hsub : forall p, Membership.mem b p -> Membership.mem ({r} : Finset Nat) p := by
      intro p hp
      have hle : p <= r := by
        by_contra h
        exact hnone (Exists.intro p (And.intro hp (by omega)))
      have heq : p = r := by have h := hlow p hp; omega
      simpa only [Finset.mem_singleton] using heq
    have h := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at h
    omega
  choose p hp using hex
  have hrest : 3 <= (b.erase p).card := by
    rw [Finset.card_erase_of_mem hp.1]
    omega
  have hprod : r ^ (b.erase p).card <= (b.erase p).prod (fun q => q) := by
    calc
      r ^ (b.erase p).card = (b.erase p).prod (fun _ => r) := by simp
      _ <= (b.erase p).prod (fun q => q) := Finset.prod_le_prod
        (fun q hq => Nat.zero_le r) (fun q hq => hlow q (Finset.mem_of_mem_erase hq))
  have hpow : r ^ 3 <= r ^ (b.erase p).card := Nat.pow_le_pow_right (by omega) hrest
  have hbig : (r + 1) * r ^ 3 <= b.prod (fun q => q) := by
    rw [<- Finset.mul_prod_erase b (fun q => q) hp.1]
    exact Nat.mul_le_mul (by omega) (le_trans hpow hprod)
  have hd : Dvd.dvd (b.prod (fun q => q)) m := (prod_primes_dvd_iff hprime m).mpr hdiv
  have hle := Nat.le_of_dvd hm hd
  have harith : (r * r + 1) * (r * r + 1) <= (r + 1) * r ^ 3 := by
    nlinarith [Nat.mul_le_mul_right (r * r) hr]
  omega

/-- The complete joint weight is nonpositive for one through three distinct divisors. -/
theorem jointIncidenceWeight_nonpos {v : Nat} (hlo : 1 <= v) (hhi : v <= 3) :
    jointIncidenceWeight v <= 0 := by
  have hc : v = 1 \/ v = 2 \/ v = 3 := by omega
  rcases hc with h | h | h <;> norm_num [jointIncidenceWeight, h]

/-- Sieving a divisor and removing its incidence cannot decrease the combined weight. -/
theorem sum_jointIncidenceWeight_erase_sieve (s b : Finset Nat) (p : Nat)
    (hp : Membership.mem b p)
    (hcount : forall m, Membership.mem s m -> Dvd.dvd p m ->
      ((b.filter (fun q => Dvd.dvd q m)).card) <= 3) :
    s.sum (fun m => jointIncidenceWeight ((b.filter (fun q => Dvd.dvd q m)).card)) <=
      (s.filter (fun m => Not (Dvd.dvd p m))).sum (fun m =>
        jointIncidenceWeight (((b.erase p).filter (fun q => Dvd.dvd q m)).card)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro m hm
  by_cases hd : Dvd.dvd p m
  next =>
    simp only [hd, not_true_eq_false, if_false]
    have hpos : 0 < ((b.filter (fun q => Dvd.dvd q m)).card) :=
      Finset.card_pos.mpr (Exists.intro p (Finset.mem_filter.mpr (And.intro hp hd)))
    exact jointIncidenceWeight_nonpos (by omega) (hcount m hm hd)
  next =>
    simp only [hd, not_false_eq_true, if_true]
    have hpf : Not (Membership.mem (b.filter (fun q => Dvd.dvd q m)) p) :=
      fun h => hd (Finset.mem_filter.mp h).2
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem hpf]

/-- At a square cutoff the joint sieve comparison needs no unproved divisor-count bound. -/
theorem sum_jointIncidenceWeight_erase_sieve_square {r : Nat} (hr : 3 <= r)
    (s b : Finset Nat) (hs : forall m, Membership.mem s m ->
      0 < m /\ m < (r * r + 1) * (r * r + 1))
    (hprime : forall p, Membership.mem b p -> Nat.Prime p)
    (hlow : forall p, Membership.mem b p -> r <= p)
    (hrb : Membership.mem b r) :
    s.sum (fun m => jointIncidenceWeight ((b.filter (fun q => Dvd.dvd q m)).card)) <=
      (s.filter (fun m => Not (Dvd.dvd r m))).sum (fun m =>
        jointIncidenceWeight (((b.erase r).filter (fun q => Dvd.dvd q m)).card)) := by
  apply sum_jointIncidenceWeight_erase_sieve s b r hrb
  intro m hm hdm
  exact card_large_prime_divisors_le_three hr (hs m hm).1 (hs m hm).2
    (b.filter (fun q => Dvd.dvd q m))
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun p hp => hlow p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2)

end Nat.PrimeSieve
