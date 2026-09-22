/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Elementary aggregation consumers for almost-all bounds
-/

set_option autoImplicit false

open Filter

theorem almost_all_finite_geometric_sum_le
    {r : Real} (hr0 : 0 <= r) (hr1 : r < 1) (m : Nat) :
    Finset.sum (Finset.range m) (fun k => r ^ k) <= 1 / (1 - r) := by
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  have hpow : r ^ m <= 1 := by
    induction m with
    | zero => norm_num
    | succ m ih =>
        rw [pow_succ]
        have hmul := mul_le_mul_of_nonneg_left (le_of_lt hr1) (pow_nonneg hr0 m)
        nlinarith
  have hsum := geom_sum_mul_neg r m
  have hmul : (Finset.sum (Finset.range m) (fun k => r ^ k)) * (1 - r) <= 1 := by
    calc
      (Finset.sum (Finset.range m) (fun k => r ^ k)) * (1 - r)
          = 1 - r ^ m := hsum
      _ <= 1 := sub_le_self 1 (pow_nonneg hr0 m)
  have htarget : (1 / (1 - r)) * (1 - r) = 1 := by
    field_simp
  have hmul' : (Finset.sum (Finset.range m) (fun k => r ^ k)) * (1 - r)
      <= (1 / (1 - r)) * (1 - r) := by
    rw [htarget]
    exact hmul
  exact (le_of_mul_le_mul_right hmul' hden)

theorem almost_all_dyadic_block_aggregation
    {r A : Real} (hr0 : 0 <= r) (hr1 : r < 1) (hA : 0 <= A)
    (m : Nat) (block : Nat -> Real)
    (hblock : forall k, k < m -> 0 <= block k /\ block k <= A * r ^ k) :
    Finset.sum (Finset.range m) block <= A / (1 - r) := by
  have hsum : Finset.sum (Finset.range m) block
      <= Finset.sum (Finset.range m) (fun k => A * r ^ k) := by
    exact Finset.sum_le_sum (fun k hk => (hblock k (Finset.mem_range.mp hk)).2)
  calc
    Finset.sum (Finset.range m) block
        <= Finset.sum (Finset.range m) (fun k => A * r ^ k) := hsum
    _ = A * Finset.sum (Finset.range m) (fun k => r ^ k) := by
      rw [Finset.mul_sum]
    _ <= A * (1 / (1 - r)) := by
      exact mul_le_mul_of_nonneg_left
        (almost_all_finite_geometric_sum_le hr0 hr1 m) hA
    _ = A / (1 - r) := by ring

theorem almost_all_bad_count_from_low_cost_explicit
    {b delta N M : Real} (hd : 0 < delta) (hN : 0 < N)
    (hcost : b * (delta ^ 5 * N ^ 5 / 8192) <= M) :
    b <= 8192 * M / (delta ^ 5 * N ^ 5) := by
  have hq : 0 < delta ^ 5 * N ^ 5 / 8192 := by positivity
  have hbase : b <= M / (delta ^ 5 * N ^ 5 / 8192) := by
    have htarget : (M / (delta ^ 5 * N ^ 5 / 8192))
        * (delta ^ 5 * N ^ 5 / 8192) = M := by
      field_simp
    have hmul : b * (delta ^ 5 * N ^ 5 / 8192)
        <= (M / (delta ^ 5 * N ^ 5 / 8192))
          * (delta ^ 5 * N ^ 5 / 8192) := by
      rw [htarget]
      exact hcost
    exact (le_of_mul_le_mul_right hmul hq)
  have hden : 0 < delta ^ 5 * N ^ 5 := by positivity
  calc
    b <= M / (delta ^ 5 * N ^ 5 / 8192) := hbase
    _ = 8192 * M / (delta ^ 5 * N ^ 5) := by field_simp

theorem almost_all_bad_count_from_low_moment
    {b C delta N epsilon : Real}
    (hd : 0 < delta) (hN : 0 < N) (hC : 0 <= C)
    (hcost : b * (delta ^ 5 * N ^ 5 / 8192) <=
      C * N ^ ((11 / 2 : Real) + epsilon)) :
    b <= (8192 * C / delta ^ 5) * N ^ ((1 / 2 : Real) + epsilon) := by
  have hraw := almost_all_bad_count_from_low_cost_explicit
    (b := b) (delta := delta) (N := N)
    (M := C * N ^ ((11 / 2 : Real) + epsilon)) hd hN hcost
  have hpow : N ^ ((11 / 2 : Real) + epsilon) =
      N ^ ((1 / 2 : Real) + epsilon) * N ^ (5 : Nat) := by
    rw [show (11 / 2 : Real) + epsilon = (1 / 2 : Real) + epsilon + 5 by ring]
    rw [Real.rpow_add hN]
    norm_num [Real.rpow_natCast]
  have hden : 0 < delta ^ 5 * N ^ 5 := by positivity
  calc
    b <= 8192 * (C * N ^ ((11 / 2 : Real) + epsilon)) /
        (delta ^ 5 * N ^ 5) := hraw
    _ = (8192 * C / delta ^ 5) * N ^ ((1 / 2 : Real) + epsilon) := by
      rw [hpow]
      field_simp

theorem almost_all_dyadic_geometric_decay
    {r : Real} (hr0 : 0 <= r) (hr1 : r < 1) :
    Tendsto (fun k : Nat => (k : Real) * r ^ k) atTop (nhds 0) := by
  exact tendsto_self_mul_const_pow_of_lt_one hr0 hr1

theorem almost_all_dyadic_density_consequence
    {A r : Real} (hr0 : 0 <= r) (hr1 : r < 1) :
    Tendsto (fun k : Nat => A * ((k : Real) * r ^ k)) atTop (nhds 0) := by
  have hdecay := almost_all_dyadic_geometric_decay hr0 hr1
  have hscale : Tendsto (fun _ : Nat => A) atTop (nhds A) := tendsto_const_nhds
  have hmul := hscale.mul hdecay
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
