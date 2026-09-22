/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.BKLNWFloorBinAggregation
import RobinBV.Sieve.Proof.BKLNWZeroesRect

/-!
# Actual zero rectangle floor-bin transfer

The generic floor-bin estimate is instantiated on a finite zeta-zero
rectangle. The natural zeta order is retained as the bin weight, so all
multiplicities survive the transfer.
-/

set_option autoImplicit false

open scoped BigOperators

namespace RobinBV.Sieve

theorem rob_bv_zeroes_rect_floor_bin_reciprocal_sum_le
    (a b c d : Real) {n m : Nat} (hn : 1 <= n)
    [Fintype (riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d))]
    (hlo : forall z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d),
      n < Nat.floor (z : Complex).im)
    (hhi : forall z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d),
      Nat.floor (z : Complex).im <= m) :
    riemannZeta.zeroes_sum (Set.Icc a b) (Set.Ioo c d)
        (fun z => 1 / (z : Complex).im) <=
      Finset.sum (Finset.Ioc n m) (fun k =>
        (1 / (k : Real)) *
          Finset.sum
            ((Finset.univ : Finset (riemannZeta.zeroes_rect
              (Set.Icc a b) (Set.Ioo c d))).filter
               (fun z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d) =>
                 Nat.floor (z : Complex).im = k))
            (fun z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d) =>
              ((riemannZeta.order (z : Complex) : Int) : Real))) := by
  let S := riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d)
  unfold riemannZeta.zeroes_sum
  simp only [tsum_fintype]
  have hweight : forall z : S, Membership.mem (Finset.univ : Finset S) z ->
      0 <= ((riemannZeta.order (z : Complex) : Int) : Real) := by
    intro z hz
    have horder : 0 <= riemannZeta.order (z : Complex) := by
      apply rob_bv_order_nonneg
      intro hEq
      have hzeta : riemannZeta (z : Complex) = 0 := z.property.2.2
      rw [hEq] at hzeta
      exact (riemannZeta_ne_zero_of_one_le_re (by norm_num)) hzeta
    exact_mod_cast horder
  have hbound := rob_bv_floor_bin_reciprocal_sum_le
    (S := (Finset.univ : Finset S))
    (height := fun z : S => (z : Complex).im)
    (weight := fun z : S => ((riemannZeta.order (z : Complex) : Int) : Real))
    (m := m) hn
    (by
      intro z hz
      exact hlo z)
    (by
      intro z hz
      exact hhi z)
    hweight
  simpa [div_eq_mul_inv, mul_comm] using hbound

end RobinBV.Sieve
