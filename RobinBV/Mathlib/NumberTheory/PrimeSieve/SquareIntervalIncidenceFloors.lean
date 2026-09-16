/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Finset.Powerset
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalIncidence

/-!
# Complete signed incidence floors between consecutive squares

Every small-owner subset and each medium-prime incidence is retained. The
quadratic live-modulus cutoff is exact: cells beyond it contribute zero.
A prime-free interval must place the resulting signed packet between minus
the explicit repeated-prime capacity and zero. Excluding that window remains
an unproved research target, not a hypothesis hidden in these identities.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- Prime-divisor subsets of a specified size are exactly the dividing product moduli. -/
theorem filter_powersetCard_prod_dvd {b : Finset Nat}
    (hb : forall p, Membership.mem b p -> Nat.Prime p) (m k : Nat) :
    (b.powersetCard k).filter (fun u => Dvd.dvd (u.prod (fun p => p)) m) =
      (b.filter (fun p => Dvd.dvd p m)).powersetCard k := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  next =>
    intro h
    have hu := (prod_primes_dvd_iff (fun p hp => hb p (h.1.1 hp)) m).mp h.2
    exact And.intro (fun p hp => Finset.mem_filter.mpr (And.intro (h.1.1 hp) (hu p hp))) h.1.2
  next =>
    intro h
    have husub : forall p, Membership.mem u p -> Membership.mem b p :=
      fun p hp => (Finset.mem_filter.mp (h.1 hp)).1
    refine And.intro (And.intro husub h.2) ?_
    apply (prod_primes_dvd_iff (fun p hp => hb p (husub p hp)) m).mpr
    intro p hp
    exact (Finset.mem_filter.mp (h.1 hp)).2

/-- A binomial prime-divisor incidence is an exact sum of product-divisibility indicators. -/
theorem choose_divisor_count_eq_subset_sum {b : Finset Nat}
    (hb : forall p, Membership.mem b p -> Nat.Prime p) (m k : Nat) :
    (Nat.choose ((b.filter (fun p => Dvd.dvd p m)).card) k : Int) =
      (b.powersetCard k).sum
        (fun u => if Dvd.dvd (u.prod (fun p => p)) m then (1 : Int) else 0) := by
  rw [Finset.sum_boole, filter_powersetCard_prod_dvd hb, Finset.card_powersetCard]

/-- Double counting converts every prime-divisor incidence into actual divisor counts. -/
theorem sum_choose_divisor_count_eq_subset_counts {b : Finset Nat}
    (hb : forall p, Membership.mem b p -> Nat.Prime p) (domain : Finset Nat) (k : Nat) :
    domain.sum (fun m => (Nat.choose ((b.filter (fun p => Dvd.dvd p m)).card) k : Int)) =
      (b.powersetCard k).sum (fun u =>
        ((domain.filter (fun m => Dvd.dvd (u.prod (fun p => p)) m)).card : Int)) := by
  simp_rw [choose_divisor_count_eq_subset_sum hb]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact Finset.sum_boole _ _

/-- Union of prime sets combines divisibility conditions, including overlaps. -/
theorem prod_union_dvd_iff {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p) (m : Nat) :
    Dvd.dvd ((Union.union a b).prod (fun p => p)) m <->
      Dvd.dvd (a.prod (fun p => p)) m /\ Dvd.dvd (b.prod (fun p => p)) m := by
  have hab : forall p, Membership.mem (Union.union a b) p -> Nat.Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpa | hpb
    next => exact ha p hpa
    next => exact hb p hpb
  rw [prod_primes_dvd_iff hab, prod_primes_dvd_iff ha, prod_primes_dvd_iff hb]
  constructor
  next =>
    intro h
    exact And.intro (fun p hp => h p (Finset.mem_union_left b hp))
      (fun p hp => h p (Finset.mem_union_right a hp))
  next =>
    intro h p hp
    rcases Finset.mem_union.mp hp with hpa | hpb
    next => exact h.1 p hpa
    next => exact h.2 p hpb

/-- Complete signed small-prime exclusion for each retained incidence, with no subset truncated. -/
theorem sieved_incidence_eq_signed_subset_counts {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p)
    (domain : Finset Nat) (k : Nat) :
    (domain.filter (fun m => forall p, Membership.mem a p -> Not (Dvd.dvd p m))).sum
      (fun m => (Nat.choose ((b.filter (fun p => Dvd.dvd p m)).card) k : Int)) =
      a.powerset.sum (fun t => (-1 : Int) ^ t.card *
        (b.powersetCard k).sum (fun u =>
          ((domain.filter (fun m =>
            Dvd.dvd ((Union.union t u).prod (fun p => p)) m)).card : Int))) := by
  rw [sum_primeSieve_eq_powerset _ _ ha]
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  rw [sum_choose_divisor_count_eq_subset_counts hb]
  apply Finset.sum_congr rfl
  intro u hu
  have htprime := fun p hp => ha p ((Finset.mem_powerset.mp ht) hp)
  have huprime := fun p hp => hb p ((Finset.mem_powersetCard.mp hu).1 hp)
  congr 1
  apply congrArg Finset.card
  ext m
  simp only [Finset.mem_filter, prod_union_dvd_iff htprime huprime, and_assoc]

/-- All odd prime clocks whose square is at most the interval index. -/
def squareSmallOddPrimes (n : Nat) : Finset Nat :=
  (Finset.range (n + 1)).filter (fun p => Nat.Prime p /\ p % 2 = 1 /\ p * p <= n)

/-- All odd prime clocks at most the index and above the small-owner cutoff. -/
def squareMediumOddPrimes (n : Nat) : Finset Nat :=
  (Finset.range (n + 1)).filter (fun p => Nat.Prime p /\ p % 2 = 1 /\ n < p * p)

/-- The actual rough survivor set is exactly the odd interval with all small owners excluded. -/
theorem rough_survivors_eq_small_sieve {n : Nat} (hn : 2 <= n) :
    squareRoughSurvivors n =
      (oddMultiplesInSquare n 1).filter (fun m =>
        forall p, Membership.mem (squareSmallOddPrimes n) p -> Not (Dvd.dvd p m)) := by
  ext m
  simp only [squareRoughSurvivors, oddMultiplesInSquare, oddMultiplesUpTo,
    Finset.mem_filter, Finset.mem_range, one_dvd, and_true]
  constructor
  next =>
    intro h
    refine And.intro (And.intro (And.intro (by nlinarith [h.1]) h.2.2.2.1) h.2.2.1) ?_
    intro p hp hpd
    have hpdata := Finset.mem_filter.mp hp
    have hcut := h.2.2.2.2 p hpdata.2.1 hpd
    omega
  next =>
    intro h
    refine And.intro (by nlinarith [h.1.1.1]) (And.intro (by nlinarith [h.1.2])
      (And.intro h.1.2 (And.intro h.1.1.2 ?_)))
    intro p hp hpd
    by_contra hcut
    have hpsq : p * p <= n := by omega
    have hpodd : p % 2 = 1 := by
      apply hp.eq_two_or_odd.resolve_left
      intro hp2
      rw [hp2] at hpd
      have hz := Nat.mod_eq_zero_of_dvd hpd
      omega
    have hpmem : Membership.mem (squareSmallOddPrimes n) p :=
      Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by nlinarith [hp.two_le]))
        (And.intro hp (And.intro hpodd hpsq)))
    exact h.2 p hpmem hpd

/-- On rough survivors, the medium prime packet captures every divisor at most the index. -/
theorem mediumPrimeDivisors_eq_medium_filter {n m : Nat}
    (hm : Membership.mem (squareRoughSurvivors n) m) :
    mediumPrimeDivisors n m =
      (squareMediumOddPrimes n).filter (fun p => Dvd.dvd p m) := by
  have hmdata := Finset.mem_filter.mp hm
  ext p
  simp only [mediumPrimeDivisors, squareMediumOddPrimes, Finset.mem_filter]
  constructor
  next =>
    intro h
    have hpodd : p % 2 = 1 := by
      apply h.2.1.eq_two_or_odd.resolve_left
      intro hp2
      have hd := h.2.2
      rw [hp2] at hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      omega
    exact And.intro (And.intro h.1 (And.intro h.2.1
      (And.intro hpodd (hmdata.2.2.2.2 p h.2.1 h.2.2)))) h.2.2
  next =>
    intro h
    exact And.intro h.1.1 (And.intro h.1.2.1 h.2)

/-- Signed endpoint floor difference, with both divisions taken in the naturals. -/
def oddSquareFloor (n d : Nat) : Int :=
  ((((n * n + 2 * n) / d + 1) / 2 : Nat) : Int) -
    (((n * n / d + 1) / 2 : Nat) : Int)

/-- The full signed endpoint-floor expansion of the specified medium-divisor incidence. -/
noncomputable def squareIncidenceFloor (n k : Nat) : Int :=
  (squareSmallOddPrimes n).powerset.sum (fun t => (-1 : Int) ^ t.card *
    ((squareMediumOddPrimes n).powersetCard k).sum (fun u =>
      oddSquareFloor n ((Union.union t u).prod (fun p => p))))

/-- Every actual survivor incidence equals its complete signed endpoint-floor expansion. -/
theorem survivor_incidence_eq_signed_floors {n : Nat} (hn : 2 <= n) (k : Nat) :
    (squareRoughSurvivors n).sum (fun m => (Nat.choose (mediumPrimeCount n m) k : Int)) =
      squareIncidenceFloor n k := by
  have ha : forall p, Membership.mem (squareSmallOddPrimes n) p -> Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1
  have hb : forall p, Membership.mem (squareMediumOddPrimes n) p -> Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1
  calc
    (squareRoughSurvivors n).sum (fun m => (Nat.choose (mediumPrimeCount n m) k : Int)) =
        (squareRoughSurvivors n).sum (fun m =>
          (Nat.choose (((squareMediumOddPrimes n).filter (fun p => Dvd.dvd p m)).card) k : Int)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [mediumPrimeCount, mediumPrimeDivisors_eq_medium_filter hm]
    _ = squareIncidenceFloor n k := by
      rw [rough_survivors_eq_small_sieve hn, sieved_incidence_eq_signed_subset_counts ha hb]
      apply Finset.sum_congr rfl
      intro t ht
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      rw [oddMultiplesInSquare_one_filter]
      have hodd : ((Union.union t u).prod (fun p => p)) % 2 = 1 := by
        apply prod_odd_mod_two
        intro p hp
        rcases Finset.mem_union.mp hp with hpt | hpu
        next =>
          exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp ht) hpt)).2.2.1
        next =>
          exact (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hu).1 hpu)).2.2.1
      exact int_card_oddMultiplesInSquare n hodd

/-- The zero-incidence floor packet is exactly the survivor count. -/
theorem squareIncidenceFloor_zero {n : Nat} (hn : 2 <= n) :
    squareIncidenceFloor n 0 = ((squareRoughSurvivors n).card : Int) := by
  have h := survivor_incidence_eq_signed_floors hn 0
  simpa using h.symm

/-- The first-incidence floor packet is exactly the first medium-prime incidence. -/
theorem squareIncidenceFloor_one {n : Nat} (hn : 2 <= n) :
    squareIncidenceFloor n 1 = firstIncidence n := by
  have h := survivor_incidence_eq_signed_floors hn 1
  simpa [firstIncidence] using h.symm

/-- The second-incidence floor packet is exactly the paired medium-prime incidence. -/
theorem squareIncidenceFloor_two {n : Nat} (hn : 2 <= n) :
    squareIncidenceFloor n 2 = secondIncidence n := by
  exact (survivor_incidence_eq_signed_floors hn 2).symm

/-- Actual prime supply from complete signed floors, retaining the exact repeated correction. -/
theorem prime_count_exact_signed_floors {n : Nat} (hn : 2 <= n) :
    3 * ((squareIntervalPrimes n).card : Int) =
      3 * squareIncidenceFloor n 0 - 3 * squareIncidenceFloor n 1 +
        2 * squareIncidenceFloor n 2 + ((twoDistinctSurvivors n).card : Int) := by
  rw [squareIncidenceFloor_zero hn, squareIncidenceFloor_one hn, squareIncidenceFloor_two hn]
  exact prime_count_second_incidence_identity hn

/-- Moduli above the quadratic upper endpoint contribute exactly zero. -/
theorem oddSquareFloor_eq_zero_of_upper_lt {n d : Nat} (hd : n * n + 2 * n < d) :
    oddSquareFloor n d = 0 := by
  have hlow : n * n < d := by omega
  simp [oddSquareFloor, Nat.div_eq_of_lt hd, Nat.div_eq_of_lt hlow]

/-- The exact dynamic product cutoff removes only zero cells, preserving all remaining signs. -/
theorem squareIncidenceFloor_eq_live_cells (n k : Nat) :
    squareIncidenceFloor n k =
      (squareSmallOddPrimes n).powerset.sum (fun t => (-1 : Int) ^ t.card *
        (((squareMediumOddPrimes n).powersetCard k).filter
          (fun u => (Union.union t u).prod (fun p => p) <= n * n + 2 * n)).sum
            (fun u => oddSquareFloor n ((Union.union t u).prod (fun p => p)))) := by
  unfold squareIncidenceFloor
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hd : (Union.union t u).prod (fun p => p) <= n * n + 2 * n
  next => simp [hd]
  next =>
    have hz := oddSquareFloor_eq_zero_of_upper_lt (show
      n * n + 2 * n < (Union.union t u).prod (fun p => p) by omega)
    simp [hd, hz]

/-- A two-sided prime-count bound expressed entirely by signed floors and repeated-prime capacity. -/
theorem prime_count_signed_floors_bounds {n : Nat} (hn : 2 <= n) :
    (3 * squareIncidenceFloor n 0 - 3 * squareIncidenceFloor n 1 +
      2 * squareIncidenceFloor n 2 <= 3 * ((squareIntervalPrimes n).card : Int)) /\
    (3 * ((squareIntervalPrimes n).card : Int) <=
      3 * squareIncidenceFloor n 0 - 3 * squareIncidenceFloor n 1 +
        2 * squareIncidenceFloor n 2 +
          ((repeatedPrimeCapacity n (Nat.sqrt n + 1)).card : Int)) := by
  rw [squareIncidenceFloor_zero hn, squareIncidenceFloor_one hn, squareIncidenceFloor_two hn]
  exact And.intro (prime_count_second_incidence_lower_bound hn)
    (prime_count_second_incidence_upper_bound hn)

/-- Positivity of the complete retained floor packet forces an interval prime. -/
theorem prime_exists_of_signed_floors_positive {n : Nat} (hn : 2 <= n)
    (hpos : 0 < 3 * squareIncidenceFloor n 0 - 3 * squareIncidenceFloor n 1 +
      2 * squareIncidenceFloor n 2) :
    exists m : Nat, n * n < m /\ m < (n + 1) * (n + 1) /\ Nat.Prime m := by
  rw [squareIncidenceFloor_zero hn, squareIncidenceFloor_one hn, squareIncidenceFloor_two hn] at hpos
  exact prime_exists_of_second_incidence_positive hn hpos

/-- A prime-free interval forces the complete signed packet into an explicit narrow window. -/
theorem no_prime_forces_signed_floor_window {n : Nat} (hn : 2 <= n)
    (hno : forall m : Nat, n * n < m -> m < (n + 1) * (n + 1) -> Not (Nat.Prime m)) :
    (-((repeatedPrimeCapacity n (Nat.sqrt n + 1)).card : Int) <=
      3 * squareIncidenceFloor n 0 - 3 * squareIncidenceFloor n 1 +
        2 * squareIncidenceFloor n 2) /\
    (3 * squareIncidenceFloor n 0 - 3 * squareIncidenceFloor n 1 +
      2 * squareIncidenceFloor n 2 <= 0) := by
  have hzero : (squareIntervalPrimes n).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    have hd := Finset.mem_filter.mp hm
    exact hno m hd.2.1 (Finset.mem_range.mp hd.1) hd.2.2
  have hbounds := prime_count_signed_floors_bounds hn
  rw [hzero] at hbounds
  constructor <;> omega

end Nat.PrimeSieve
