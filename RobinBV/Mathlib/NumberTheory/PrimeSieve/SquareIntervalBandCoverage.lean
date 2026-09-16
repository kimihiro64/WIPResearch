/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalBandOwner

/-!
# Balanced pair coverage in the corrected composite estimate

Quadratic uniqueness bounds actual covered composites by the existing pair
capacity. The direct three-times-composite estimate retains the full remaining
composite class and a proved repeated-factor allowance. No remaining count is
assumed small, and no positive prime lower bound is asserted.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- An odd divisor above the index owns at most one odd multiple in the open square interval. -/
theorem card_oddMultiplesInSquare_le_one {n d : Nat} (hd : n < d)
    (hodd : d%2 = 1) : (oddMultiplesInSquare n d).card <= 1 := by
  apply Finset.card_le_one.mpr
  intro m hm z hz
  have data (a : Nat) (ha : Membership.mem (oddMultiplesInSquare n d) a) :
      n*n < a /\ a < (n+1)*(n+1) /\ a%2 = 1 /\ Dvd.dvd d a := by
    have hh := Finset.mem_filter.mp ha
    have hu := Finset.mem_filter.mp hh.1
    have hi := Finset.mem_range.mp hu.1
    exact And.intro hh.2 (And.intro (by nlinarith) hu.2)
  have hmd := data m hm
  have hzd := data z hz
  choose r hr using hmd.2.2.2
  choose t ht using hzd.2.2.2
  have hro : r%2 = 1 := by
    have hh := hmd.2.2.1
    rw [hr, Nat.mul_mod, hodd] at hh
    simpa using hh
  have hto : t%2 = 1 := by
    have hh := hzd.2.2.1
    rw [ht, Nat.mul_mod, hodd] at hh
    simpa using hh
  have he := odd_cofactor_unique hd hro hto
    (by rw [<- hr]; exact hmd.1) (by rw [<- hr]; exact hmd.2.1)
    (by rw [<- ht]; exact hzd.1) (by rw [<- ht]; exact hzd.2.1)
  rw [hr, ht, he]

/-- Actual rough candidates divisible by an admissible balanced-pair modulus. -/
noncomputable def squareBandCoveredRough (n D : Nat) : Finset Nat :=
  (squareRoughSurvivors n).filter (fun m =>
    exists d, Membership.mem (squareBandPairModuli n D) d /\ Dvd.dvd d m)

/-- Every unremoved rough composite, retained explicitly in the estimate. -/
noncomputable def squareBandRemainingComposites (n D : Nat) : Finset Nat :=
  (squareRoughSurvivors n).filter (fun m => Not (Nat.Prime m) /\
    Not (Membership.mem (squareBandCoveredRough n D) m))

/-- Count covered rough composites at most once, even when several pair divisors cover them. -/
theorem card_squareBandCoveredRough_le_moduli (n D : Nat) :
    (squareBandCoveredRough n D).card <= (squareBandPairModuli n D).card := by
  have hsub : squareBandCoveredRough n D <=
      (squareBandPairModuli n D).biUnion (oddMultiplesInSquare n) := by
    intro m hm
    have hh := Finset.mem_filter.mp hm
    choose d hd using hh.2
    have hs := Finset.mem_filter.mp hh.1
    have hu := Finset.mem_range.mp hs.1
    apply Finset.mem_biUnion.mpr
    refine Exists.intro d (And.intro hd.1 ?_)
    apply Finset.mem_filter.mpr
    refine And.intro ?_ hs.2.2.1
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by nlinarith))
      (And.intro hs.2.2.2.1 hd.2))
  have hone : forall d, Membership.mem (squareBandPairModuli n D) d ->
      (oddMultiplesInSquare n d).card <= 1 := by
    intro d hd
    have hh := Finset.mem_filter.mp hd
    have ho := Finset.mem_filter.mp hh.1
    have hi := Finset.mem_Icc.mp ho.1
    exact card_oddMultiplesInSquare_le_one (by omega) ho.2
  calc
    _ <= ((squareBandPairModuli n D).biUnion (oddMultiplesInSquare n)).card :=
      Finset.card_le_card hsub
    _ <= (squareBandPairModuli n D).sum (fun d => (oddMultiplesInSquare n d).card) :=
      Finset.card_biUnion_le
    _ <= (squareBandPairModuli n D).sum (fun _ => 1) := Finset.sum_le_sum hone
    _ = _ := by simp

/-- Covered band candidates are actual composites, not additional prime exclusions. -/
theorem squareBandCoveredRough_not_prime {n D m : Nat} (hn : 3 <= n)
    (hD : D <= 2*n+1) (hm : Membership.mem (squareBandCoveredRough n D) m) :
    Not (Nat.Prime m) := by
  have hh := Finset.mem_filter.mp hm
  have hs := Finset.mem_filter.mp hh.1
  choose d hd using hh.2
  have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd.1).1).1
  intro hp
  have he := (hp.eq_one_or_self_of_dvd d hd.2).resolve_left (by omega)
  rw [he] at hi
  nlinarith [hs.2.2.1]

/-- Exact disjoint partition into primes, covered composites, and the full remaining composite class. -/
theorem squareRough_card_band_partition {n D : Nat} (hn : 3 <= n)
    (hD : D <= 2*n+1) :
    (squareRoughSurvivors n).card = (squareIntervalPrimes n).card +
      (squareBandCoveredRough n D).card + (squareBandRemainingComposites n D).card := by
  have he : ((squareRoughSurvivors n).filter (fun m => Not (Nat.Prime m))).filter
      (fun m => Membership.mem (squareBandCoveredRough n D) m) = squareBandCoveredRough n D := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    next => exact fun h => h.2
    next =>
      intro hm
      exact And.intro (And.intro (Finset.mem_filter.mp hm).1
        (squareBandCoveredRough_not_prime hn hD hm)) hm
  have hr : ((squareRoughSurvivors n).filter (fun m => Not (Nat.Prime m))).filter
      (fun m => Not (Membership.mem (squareBandCoveredRough n D) m)) =
      squareBandRemainingComposites n D := by
    rw [Finset.filter_filter]
    rfl
  have h1 := Finset.card_filter_add_card_filter_not (s := squareRoughSurvivors n) Nat.Prime
  rw [squareRoughSurvivors_filter_prime (by omega)] at h1
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (squareRoughSurvivors n).filter (fun m => Not (Nat.Prime m)))
    (fun m => Membership.mem (squareBandCoveredRough n D) m)
  rw [he, hr] at h2
  omega

/-- The geometric capacity enters the original corrected composite estimate, with a proved repeated-term allowance. -/
theorem corrected_composite_band_capacity_upper {n D : Nat} (hn : 3 <= n)
    (hD : D <= 2*n+1) :
    3*(n : Int)-3*((squareRoughSurvivors n).card : Int)+
      3*firstIncidence n-2*secondIncidence n <=
    3*(n : Int)-3*((squareRoughSurvivors n).card : Int)+
      3*(squareBandPairCapacity n D : Int)+
      3*((squareBandRemainingComposites n D).card : Int)+
      ((Nat.nthRoot 3 (n*n+2*n)+1-Nat.sqrt n : Nat) : Int) := by
  have he := prime_count_second_incidence_identity (show 2 <= n by omega)
  have hp := squareRough_card_band_partition hn hD
  have hc := (card_squareBandCoveredRough_le_moduli n D).trans
    (card_squareBandPairModuli_le_capacity hD)
  have hr := card_twoDistinctSurvivors_le_cubic_root n
  omega

/-- The same geometric estimate accepts any proved prime-count upper bound for the auxiliary factor window. -/
theorem card_squareBandPairModuli_le_prime_window {n D : Nat} (hD : D <= 2*n+1) :
    (squareBandPairModuli n D).card <=
      Nat.choose (oddPrimesBetween (Nat.sqrt n+1) (D/(Nat.sqrt n+1))).card 2 := by
  have hs := Finset.card_le_card (squareBandPairModuli_subset_pair_products hD)
  have hi := Finset.card_image_le (s :=
    (oddPrimesBetween (Nat.sqrt n+1) (D/(Nat.sqrt n+1))).powersetCard 2)
    (f := fun t : Finset Nat => t.prod (fun p => p))
  rw [Finset.card_powersetCard] at hi
  exact hs.trans hi

end Nat.PrimeSieve
