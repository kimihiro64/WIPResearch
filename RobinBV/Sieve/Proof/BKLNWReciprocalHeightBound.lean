/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.BKLNWZeroesRect

/-!
# Reciprocal-height zero bound

This module proves the elementary finite reciprocal-height bound obtained by
replacing each reciprocal height by the reciprocal of the lower endpoint.
Multiplicity orders are retained. It is not the sharper FKS B1 estimate.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem rob_bv_zeroes_rect_reciprocal_height_le
    (a b c d : Real) (hc : 0 < c) (hcd : c < d) :
    riemannZeta.zeroes_sum (Set.Icc a b) (Set.Ioo c d)
        (fun z => 1 / (z : Complex).im) <=
      (1 / c) * riemannZeta.zeroes_sum (Set.Icc a b) (Set.Ioo c d)
        (fun _ => (1 : Real)) := by
  let S := riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d)
  have hfin : S.Finite := rob_bv_zeroes_rect_Icc_finite a b c d
  letI : Fintype S := hfin.fintype
  unfold riemannZeta.zeroes_sum
  simp only [tsum_fintype]
  change (Finset.univ.sum (fun z : S =>
      (1 / (z : Complex).im) *
        ((riemannZeta.order (z : Complex) : Int) : Real))) <=
    (1 / c) * Finset.univ.sum (fun z : S =>
      (1 : Real) * ((riemannZeta.order (z : Complex) : Int) : Real))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have him : c < (z : Complex).im :=
    (Set.mem_Ioo.mp z.property.2.1).1
  have himpos : 0 < (z : Complex).im := lt_trans hc him
  have hrec : 1 / (z : Complex).im <= 1 / c := by
    exact (div_le_div_iff_of_pos_left one_pos himpos hc).2 (le_of_lt him)
  have horder : 0 <= ((riemannZeta.order (z : Complex) : Int) : Real) := by
    have horderZ : 0 <= riemannZeta.order (z : Complex) := by
      apply rob_bv_order_nonneg
      intro hEq
      have hzeta : riemannZeta (z : Complex) = 0 := z.property.2.2
      rw [hEq] at hzeta
      exact (riemannZeta_ne_zero_of_one_le_re (by norm_num)) hzeta
    exact_mod_cast horderZ
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hrec horder)

end RobinBV.Sieve
