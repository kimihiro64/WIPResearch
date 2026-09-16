/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalCounts

/-!
# Exact exceptional-square cost in a discrete fourth moment

This is a finite consumer for the almost-all prime-interval strategy.
It proves no analytic upper bound on the moment and assumes no such bound.
All prime counts refer to the existing open square interval.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

noncomputable def squarePrimeLogWindow (x h : Nat) : Real :=
  ((Finset.Ioc x (x + h)).filter Nat.Prime).sum
    (fun p => Real.log (p : Real))

noncomputable def primeFreeSquareBlock (N : Nat) : Finset Nat :=
  (Finset.Ico N (2 * N)).filter
    (fun n => (squareIntervalPrimes n).card = 0)

noncomputable def primeFreeSquareStarts (N : Nat) : Finset Nat :=
  (primeFreeSquareBlock N).biUnion
    (fun n => Finset.Ico (n * n) (n * n + N))

noncomputable def squarePrimeFourthMoment (N : Nat) : Real :=
  (Finset.Ico (N * N) ((2 * N) * (2 * N))).sum
    (fun x => (squarePrimeLogWindow x N - (N : Real)) ^ 4)

theorem squarePrimeLogWindow_eq_zero_of_prime_free
    {N n x : Nat} (hN : N <= n)
    (hfree : (squareIntervalPrimes n).card = 0)
    (hx : Membership.mem (Finset.Ico (n * n) (n * n + N)) x) :
    squarePrimeLogWindow x N = 0 := by
  have hx' := Finset.mem_Ico.mp hx
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hi := Finset.mem_Ioc.mp hp'.1
  have hmem : Membership.mem (squareIntervalPrimes n) p := by
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_range.mpr ?_) (And.intro ?_ hp'.2)
    next => nlinarith only [hi.2, hx'.2, hN]
    next => omega
  have hpos : 0 < (squareIntervalPrimes n).card :=
    Finset.card_pos.mpr (Exists.intro p hmem)
  omega

theorem primeFreeSquareStarts_pairwise (N : Nat) :
    (primeFreeSquareBlock N : Set Nat).PairwiseDisjoint
      (fun n => Finset.Ico (n * n) (n * n + N)) := by
  intro n hn m hm hne
  have hn' := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
  have hm' := Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1
  apply Finset.disjoint_left.mpr
  intro x hxn hxm
  have hxn' := Finset.mem_Ico.mp hxn
  have hxm' := Finset.mem_Ico.mp hxm
  rcases lt_or_gt_of_ne hne with hnm | hmn
  next =>
    have hstep : n + 1 <= m := by omega
    have hs := Nat.mul_le_mul hstep hstep
    nlinarith only [hxn'.2, hxm'.1, hn'.1, hs]
  next =>
    have hstep : m + 1 <= n := by omega
    have hs := Nat.mul_le_mul hstep hstep
    nlinarith only [hxm'.2, hxn'.1, hm'.1, hs]

theorem card_primeFreeSquareStarts (N : Nat) :
    (primeFreeSquareStarts N).card = (primeFreeSquareBlock N).card * N := by
  unfold primeFreeSquareStarts
  rw [Finset.card_biUnion (primeFreeSquareStarts_pairwise N)]
  simp

theorem primeFreeSquareStarts_subset (N : Nat) :
    primeFreeSquareStarts N <= Finset.Ico (N * N) ((2 * N) * (2 * N)) := by
  intro x hx
  choose n hn using Finset.mem_biUnion.mp hx
  have hi := Finset.mem_Ico.mp (Finset.mem_filter.mp hn.1).1
  have hx' := Finset.mem_Ico.mp hn.2
  have hlo := Nat.mul_le_mul hi.1 hi.1
  have hstep : n + 1 <= 2 * N := by omega
  have hhi := Nat.mul_le_mul hstep hstep
  apply Finset.mem_Ico.mpr
  exact And.intro (by omega) (by nlinarith only [hx'.2, hi.1, hhi])

theorem primeFreeSquareStarts_fourth_power {N x : Nat}
    (hx : Membership.mem (primeFreeSquareStarts N) x) :
    (squarePrimeLogWindow x N - (N : Real)) ^ 4 = (N : Real) ^ 4 := by
  choose n hn using Finset.mem_biUnion.mp hx
  have hn' := Finset.mem_filter.mp hn.1
  have hi := Finset.mem_Ico.mp hn'.1
  rw [squarePrimeLogWindow_eq_zero_of_prime_free hi.1 hn'.2 hn.2]
  ring

/-- Every prime-free square interval consumes exactly N^5 units of
the disjoint starting-point portion of the full fourth moment. -/
theorem prime_free_square_card_mul_pow_five_le_moment (N : Nat) :
    ((primeFreeSquareBlock N).card : Real) * (N : Real) ^ 5 <=
      squarePrimeFourthMoment N := by
  have heq :
      (primeFreeSquareStarts N).sum
        (fun x => (squarePrimeLogWindow x N - (N : Real)) ^ 4) =
        ((primeFreeSquareBlock N).card : Real) * (N : Real) ^ 5 := by
    calc
      _ = (primeFreeSquareStarts N).sum (fun _ => (N : Real) ^ 4) :=
        Finset.sum_congr rfl (fun x hx => primeFreeSquareStarts_fourth_power hx)
      _ = ((primeFreeSquareBlock N).card : Real) * (N : Real) ^ 5 := by
        simp only [Finset.sum_const, nsmul_eq_mul, card_primeFreeSquareStarts,
          Nat.cast_mul]
        ring
  rw [<- heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (primeFreeSquareStarts_subset N)
    (fun x _ _ => by positivity)

/-- A strict moment bound eliminates every exception in the entire block.
This is a conditional consumer, not a proved analytic moment estimate. -/
theorem square_interval_prime_exists_of_fourth_moment
    {N n : Nat} (hN : 1 <= N) (hn : N <= n) (hn2 : n < 2 * N)
    (hmoment : squarePrimeFourthMoment N < (N : Real) ^ 5) :
    0 < (squareIntervalPrimes n).card := by
  by_contra h
  have hzero : (squareIntervalPrimes n).card = 0 := by omega
  have hmem : Membership.mem (primeFreeSquareBlock N) n :=
    Finset.mem_filter.mpr (And.intro (Finset.mem_Ico.mpr (And.intro hn hn2)) hzero)
  have hcard : 1 <= (primeFreeSquareBlock N).card :=
    Finset.card_pos.mpr (Exists.intro n hmem)
  have hcardR : (1 : Real) <= ((primeFreeSquareBlock N).card : Real) := by
    exact_mod_cast hcard
  have hmul := _root_.mul_le_mul_of_nonneg_right hcardR
    (show 0 <= (N : Real) ^ 5 by positivity)
  have hbound := prime_free_square_card_mul_pow_five_le_moment N
  nlinarith only [hmul, hbound, hmoment]

end Nat.PrimeSieve
