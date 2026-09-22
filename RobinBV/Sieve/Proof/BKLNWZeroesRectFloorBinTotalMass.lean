/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.BKLNWZeroesRectFloorBinMass

/-!
# Total-mass consumer for reciprocal floor bins

The per-bin reciprocal transfer can use one total multiplicity envelope.  The
filtered floor bin is a subset of the full finite rectangle, and zero orders
are nonnegative, so the existing rectangle mass bound supplies every bin.
-/

set_option autoImplicit false

open scoped BigOperators

namespace RobinBV.Sieve

theorem rob_bv_zeroes_rect_floor_bin_reciprocal_sum_le_of_total_mass
    (a b c d : Real) {n m : Nat} (hn : 1 <= n)
    [Fintype (riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d))]
    (hlo : forall z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d),
      n < Nat.floor (z : Complex).im)
    (hhi : forall z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d),
      Nat.floor (z : Complex).im <= m)
    (M : Real)
    (hmass : Finset.sum (Finset.univ : Finset (riemannZeta.zeroes_rect
      (Set.Icc a b) (Set.Ioo c d)))
      (fun z => ((riemannZeta.order (z : Complex) : Int) : Real)) <= M) :
    riemannZeta.zeroes_sum (Set.Icc a b) (Set.Ioo c d)
        (fun z => 1 / (z : Complex).im) <=
      Finset.sum (Finset.Ioc n m) (fun k => (1 / (k : Real)) * M) := by
  apply rob_bv_zeroes_rect_floor_bin_reciprocal_sum_le_of_mass
    a b c d hn hlo hhi (fun _ => M)
  intro k hk
  have hsubset := Finset.filter_subset
    (fun z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d) =>
      Nat.floor (z : Complex).im = k)
    (Finset.univ : Finset (riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d)))
  have hnonneg : forall z,
      Membership.mem (Finset.univ : Finset
        (riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d))) z ->
      Not (Membership.mem
        ((Finset.univ : Finset (riemannZeta.zeroes_rect
          (Set.Icc a b) (Set.Ioo c d))).filter
          (fun z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d) =>
            Nat.floor (z : Complex).im = k)) z) ->
      0 <= ((riemannZeta.order (z : Complex) : Int) : Real) := by
    intro z _ _
    have horder : 0 <= riemannZeta.order (z : Complex) := by
      apply rob_bv_order_nonneg
      intro hEq
      have hz : riemannZeta (z : Complex) = 0 := z.property.2.2
      rw [hEq] at hz
      exact (riemannZeta_ne_zero_of_one_le_re (by norm_num)) hz
    exact_mod_cast horder
  have hfilter := Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  exact hfilter.trans hmass

end RobinBV.Sieve
