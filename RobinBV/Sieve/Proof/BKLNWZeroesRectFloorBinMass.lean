/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.BKLNWZeroesRectFloorBins

/-!
# Floor-bin mass consumer

This theorem consumes an explicit upper envelope for every actual-zero
multiplicity bin and propagates it through the reciprocal floor-bin transfer.
-/

set_option autoImplicit false

open scoped BigOperators

namespace RobinBV.Sieve

theorem rob_bv_zeroes_rect_floor_bin_reciprocal_sum_le_of_mass
    (a b c d : Real) {n m : Nat} (hn : 1 <= n)
    [Fintype (riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d))]
    (hlo : forall z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d),
      n < Nat.floor (z : Complex).im)
    (hhi : forall z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d),
      Nat.floor (z : Complex).im <= m)
    (mass : Nat -> Real)
    (hmass : forall k, Membership.mem (Finset.Ioc n m : Finset Nat) k ->
      Finset.sum
        ((Finset.univ : Finset (riemannZeta.zeroes_rect
          (Set.Icc a b) (Set.Ioo c d))).filter
          (fun z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d) =>
            Nat.floor (z : Complex).im = k))
        (fun z => ((riemannZeta.order (z : Complex) : Int) : Real)) <= mass k) :
    riemannZeta.zeroes_sum (Set.Icc a b) (Set.Ioo c d)
        (fun z => 1 / (z : Complex).im) <=
      Finset.sum (Finset.Ioc n m) (fun k => (1 / (k : Real)) * mass k) := by
  have hbin := rob_bv_zeroes_rect_floor_bin_reciprocal_sum_le
    a b c d hn hlo hhi
  calc
    riemannZeta.zeroes_sum (Set.Icc a b) (Set.Ioo c d)
        (fun z => 1 / (z : Complex).im) <=
        Finset.sum (Finset.Ioc n m) (fun k =>
          (1 / (k : Real)) *
            Finset.sum
              ((Finset.univ : Finset (riemannZeta.zeroes_rect
                (Set.Icc a b) (Set.Ioo c d))).filter
                (fun z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d) =>
                  Nat.floor (z : Complex).im = k))
              (fun z => ((riemannZeta.order (z : Complex) : Int) : Real))) := hbin
    _ <= Finset.sum (Finset.Ioc n m) (fun k => (1 / (k : Real)) * mass k) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left (hmass k hk)
      have h1k : 1 <= k := le_of_lt (lt_of_le_of_lt hn (Finset.mem_Ioc.mp hk).1)
      have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one h1k
      positivity

end RobinBV.Sieve
