/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalIncidence
/-!
# Geometrically disjoint high-medium-prime incidence

A rough candidate has at most one medium prime above the explicit three-factor
cutoff. Its incidence is therefore a disjoint composite count. The original
corrected composite ledger retains the full complementary composite class and
repeated-factor term; no upper bound for either composite class is assumed.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- A nontrivial divisor of a rough candidate is above the same integer cutoff. -/
theorem rough_nontrivial_divisor_lower {n m r : Nat}
    (hm : Membership.mem (squareRoughSurvivors n) m)
    (hr : 2 <= r) (hrd : Dvd.dvd r m) : Nat.sqrt n+1 <= r := by
  have hrough := (Finset.mem_filter.mp hm).2.2.2.2
  have hp := Nat.minFac_prime (show Not (r = 1) by omega)
  have hpd := dvd_trans (Nat.minFac_dvd r) hrd
  have hcut := Nat.sqrt_lt.mpr (hrough r.minFac hp hpd)
  have hle := Nat.minFac_le (show 0 < r by omega)
  omega

/-- Two distinct medium prime divisors cannot both exceed the three-factor geometric cutoff. -/
theorem high_medium_prime_unique {n T m p q : Nat}
    (hm : Membership.mem (squareRoughSurvivors n) m)
    (hcut : (n+1)*(n+1) <= (T+1)*(T+1)*(Nat.sqrt n+1))
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpn : p <= n) (hqn : q <= n) (hTp : T < p) (hTq : T < q)
    (hpd : Dvd.dvd p m) (hqd : Dvd.dvd q m) : p = q := by
  by_contra hne
  have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hne ((hq.eq_one_or_self_of_dvd p hd).resolve_left hp.ne_one))
  have hpqd := hcop.mul_dvd_of_dvd_of_dvd hpd hqd
  choose r hr using hpqd
  have hd := Finset.mem_filter.mp hm
  have hlo := hd.2.2.1
  have hhi := Finset.mem_range.mp hd.1
  have hpqle := Nat.mul_le_mul hpn hqn
  have hr2 : 2 <= r := by
    by_contra hh
    have hle : r <= 1 := by omega
    have hprod := Nat.mul_le_mul_left (p*q) hle
    rw [<- hr] at hprod
    nlinarith
  have hrd : Dvd.dvd r m := by
    rw [hr]
    exact dvd_mul_left r (p*q)
  have hrl := rough_nontrivial_divisor_lower hm hr2 hrd
  have hpqlo := Nat.mul_le_mul (show T+1 <= p by omega) (show T+1 <= q by omega)
  have hprod := Nat.mul_le_mul hpqlo hrl
  rw [<- hr] at hprod
  omega

/-- The high-medium-prime incidence has multiplicity at most one on every actual rough candidate. -/
theorem high_medium_prime_count_le_one {n T m : Nat}
    (hm : Membership.mem (squareRoughSurvivors n) m)
    (hcut : (n+1)*(n+1) <= (T+1)*(T+1)*(Nat.sqrt n+1)) :
    ((mediumPrimeDivisors n m).filter (fun p => T < p)).card <= 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have hpa := Finset.mem_filter.mp hp
  have hqa := Finset.mem_filter.mp hq
  have hpb := Finset.mem_filter.mp hpa.1
  have hqb := Finset.mem_filter.mp hqa.1
  exact high_medium_prime_unique hm hcut hpb.2.1 hqb.2.1
    (by have := Finset.mem_range.mp hpb.1; omega)
    (by have := Finset.mem_range.mp hqb.1; omega)
    hpa.2 hqa.2 hpb.2.2 hqb.2.2

/-- The actual high-medium-prime incidence, with the geometric cutoff kept visible. -/
noncomputable def highMediumIncidence (n T : Nat) : Nat :=
  (squareRoughSurvivors n).sum (fun m =>
    ((mediumPrimeDivisors n m).filter (fun p => T < p)).card)

/-- All rough composites outside the high-medium-prime class, with no omitted complement. -/
noncomputable def lowMediumComposites (n T : Nat) : Finset Nat :=
  (squareRoughSurvivors n).filter (fun m => Not (Nat.Prime m) /\
    ((mediumPrimeDivisors n m).filter (fun p => T < p)).card = 0)

/-- Under geometric uniqueness the high incidence is a disjoint count, not an overlapping composite allowance. -/
theorem highMediumIncidence_eq_card {n T : Nat}
    (hcut : (n+1)*(n+1) <= (T+1)*(T+1)*(Nat.sqrt n+1)) :
    highMediumIncidence n T = ((squareRoughSurvivors n).filter (fun m =>
      ((mediumPrimeDivisors n m).filter (fun p => T < p)).card = 1)).card := by
  unfold highMediumIncidence
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have hle := high_medium_prime_count_le_one hm hcut
  by_cases he : ((mediumPrimeDivisors n m).filter (fun p => T < p)).card = 1
  next => simp [he]
  next =>
    have hz : ((mediumPrimeDivisors n m).filter (fun p => T < p)).card = 0 := by omega
    simp [hz]

/-- Exact rough-survivor partition retaining every low composite and counting the high incidence once. -/
theorem squareRough_card_high_medium_partition {n T : Nat} (hn : 2 <= n)
    (hcut : (n+1)*(n+1) <= (T+1)*(T+1)*(Nat.sqrt n+1)) :
    (squareRoughSurvivors n).card = (squareIntervalPrimes n).card +
      highMediumIncidence n T + (lowMediumComposites n T).card := by
  let c := (squareRoughSurvivors n).filter (fun m => Not (Nat.Prime m))
  let k := fun m => ((mediumPrimeDivisors n m).filter (fun p => T < p)).card
  have hhigh : c.filter (fun m => k m = 1) =
      (squareRoughSurvivors n).filter (fun m => k m = 1) := by
    ext m
    simp only [c, Finset.mem_filter]
    constructor
    next => intro h; exact And.intro h.1.1 h.2
    next =>
      intro h
      refine And.intro (And.intro h.1 ?_) h.2
      intro hp
      have hlo := (Finset.mem_filter.mp h.1).2.2.1
      have hz : k m = 0 := by simp [k, mediumPrimeDivisors_prime hp hlo]
      omega
  have hlow : c.filter (fun m => Not (k m = 1)) = lowMediumComposites n T := by
    ext m
    simp only [c, lowMediumComposites, Finset.mem_filter]
    constructor
    next =>
      intro h
      have hle := high_medium_prime_count_le_one h.1.1 hcut
      have hk : k m <= 1 := hle
      have hz : k m = 0 := by omega
      exact And.intro h.1.1 (And.intro h.1.2 hz)
    next =>
      intro h
      have hz : k m = 0 := h.2.2
      exact And.intro (And.intro h.1 h.2.1) (by omega)
  have hsplit := Finset.card_filter_add_card_filter_not (s := c) (fun m => k m = 1)
  rw [hhigh, hlow, <- highMediumIncidence_eq_card hcut] at hsplit
  have hp := Finset.card_filter_add_card_filter_not (s := squareRoughSurvivors n) Nat.Prime
  rw [squareRoughSurvivors_filter_prime hn] at hp
  change _ + c.card = _ at hp
  omega

/-- The high-factor partition enters the original corrected composite ledger with its repeated term intact. -/
theorem corrected_composite_high_medium_identity {n T : Nat} (hn : 2 <= n)
    (hcut : (n+1)*(n+1) <= (T+1)*(T+1)*(Nat.sqrt n+1)) :
    3*(n : Int)-3*((squareRoughSurvivors n).card : Int)+
      3*firstIncidence n-2*secondIncidence n =
    3*(n : Int)-3*((squareRoughSurvivors n).card : Int)+
      3*(highMediumIncidence n T : Int)+3*((lowMediumComposites n T).card : Int)+
      ((twoDistinctSurvivors n).card : Int) := by
  have hp := squareRough_card_high_medium_partition hn hcut
  have he := prime_count_second_incidence_identity hn
  omega

/-- Integer factor cells surviving only the selected small-prime exclusions; no factor primality is imposed. -/
noncomputable def siftedHighFactorCells (n T : Nat) (S : Finset Nat) : Finset (Prod Nat Nat) :=
  ((Finset.range (n+1)).product (Finset.range ((n+1)*(n+1)))).filter (fun x =>
    T < x.1 /\ n*n < x.1*x.2 /\ x.1*x.2 < (n+1)*(n+1) /\
      x.1%2 = 1 /\ x.2%2 = 1 /\
        forall ell, Membership.mem S ell -> Not (Dvd.dvd ell x.1) /\ Not (Dvd.dvd ell x.2))

/-- Geometric high-incidence uniqueness converts the partial-sieve lattice into a composite upper bound. -/
theorem highMediumIncidence_le_siftedHyperbola {n T : Nat} (S : Finset Nat)
    (hcut : (n+1)*(n+1) <= (T+1)*(T+1)*(Nat.sqrt n+1))
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell /\ ell*ell <= n) :
    highMediumIncidence n T <= (siftedHighFactorCells n T S).card := by
  rw [highMediumIncidence_eq_card hcut]
  let cells := siftedHighFactorCells n T S
  have hsub : ((squareRoughSurvivors n).filter (fun m =>
      ((mediumPrimeDivisors n m).filter (fun p => T < p)).card = 1)) <=
      cells.image (fun x => x.1*x.2) := by
    intro m hm
    have hs := Finset.mem_filter.mp hm
    have hd := Finset.mem_filter.mp hs.1
    have hpos : 0 < ((mediumPrimeDivisors n m).filter (fun p => T < p)).card := by omega
    choose p hp using Finset.card_pos.mp hpos
    have hpa := Finset.mem_filter.mp hp
    have hpb := Finset.mem_filter.mp hpa.1
    have hpn := Finset.mem_range.mp hpb.1
    have hprime := hpb.2.1
    have hpm := hpb.2.2
    have hhi := Finset.mem_range.mp hd.1
    choose r hr using hpm
    have hpm : Dvd.dvd p m := Exists.intro r hr
    have hrd : Dvd.dvd r m := by rw [hr]; exact dvd_mul_left r p
    have hrle := Nat.le_of_dvd (show 0 < m by omega) hrd
    have hoddp : p%2 = 1 := hprime.eq_two_or_odd.resolve_left (by
      intro he
      rw [he] at hpm
      have hz := Nat.mod_eq_zero_of_dvd hpm
      omega)
    have hoddr : r%2 = 1 := by
      have ho := hd.2.2.2.1
      rw [hr, Nat.mul_mod, hoddp] at ho
      simpa using ho
    have hexclude : forall ell, Membership.mem S ell ->
        Not (Dvd.dvd ell p) /\ Not (Dvd.dvd ell r) := by
      intro ell hell
      have hl := hS ell hell
      constructor
      next =>
        intro hdiv
        have hbad := hd.2.2.2.2 ell hl.1 (dvd_trans hdiv hpm)
        omega
      next =>
        intro hdiv
        have hbad := hd.2.2.2.2 ell hl.1 (dvd_trans hdiv hrd)
        omega
    apply Finset.mem_image.mpr
    refine Exists.intro (Prod.mk p r) (And.intro ?_ hr.symm)
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_product.mpr (And.intro
      (Finset.mem_range.mpr hpn) (Finset.mem_range.mpr (by omega)))) ?_
    exact And.intro hpa.2 (And.intro (by rw [<- hr]; exact hd.2.2.1)
      (And.intro (by rw [<- hr]; exact hhi)
        (And.intro hoddp (And.intro hoddr hexclude))))
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Direct composite-ledger upper bound from integer lattice geometry and finitely many prime exclusions. -/
theorem corrected_composite_siftedHyperbola_upper {n T : Nat} (S : Finset Nat)
    (hn : 2 <= n)
    (hcut : (n+1)*(n+1) <= (T+1)*(T+1)*(Nat.sqrt n+1))
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell /\ ell*ell <= n) :
    3*(n : Int)-3*((squareRoughSurvivors n).card : Int)+
      3*firstIncidence n-2*secondIncidence n <=
    3*(n : Int)-3*((squareRoughSurvivors n).card : Int)+
      3*((siftedHighFactorCells n T S).card : Int)+
      3*((lowMediumComposites n T).card : Int)+((twoDistinctSurvivors n).card : Int) := by
  rw [corrected_composite_high_medium_identity hn hcut]
  have hcap := highMediumIncidence_le_siftedHyperbola S hcut hS
  omega

end Nat.PrimeSieve
