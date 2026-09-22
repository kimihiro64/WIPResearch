/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.Floor.Semiring
import RobinBV.Sieve.Proof.BKLNWFloorReciprocalWeight

/-!
# Finite floor-bin aggregation

This module partitions a finite weighted family by integer floor height and
retains multiplicities in every bin. The resulting reciprocal estimate is the
finite combinatorial transfer used before the cumulative zero-count bound.
-/

set_option autoImplicit false

open scoped BigOperators

namespace RobinBV.Sieve

theorem rob_bv_floor_bin_reciprocal_sum_le
    {alpha : Type*} [DecidableEq alpha]
    (S : Finset alpha) (height weight : alpha -> Real)
    {n m : Nat} (hn : 1 <= n)
    (hlo : forall a, Membership.mem S a -> n < Nat.floor (height a))
    (hhi : forall a, Membership.mem S a -> Nat.floor (height a) <= m)
    (hw : forall a, Membership.mem S a -> 0 <= weight a) :
    (Finset.sum S (fun a => weight a / height a)) <=
      Finset.sum (Finset.Ioc n m) (fun k =>
        (1 / (k : Real)) *
          Finset.sum (S.filter (fun a => Nat.floor (height a) = k)) weight) := by
  have hmap : (S : Set alpha).MapsTo (fun a => Nat.floor (height a))
      (Finset.Ioc n m : Set Nat) := by
    intro a ha
    exact Finset.mem_Ioc.mpr (And.intro (hlo a ha) (hhi a ha))
  have hpoint : forall a, Membership.mem S a ->
      weight a / height a <=
        (1 / (Nat.floor (height a) : Real)) * weight a := by
    intro a ha
    have hfloorpos : 0 < Nat.floor (height a) := by
      have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
      exact lt_trans hnpos (hlo a ha)
    have hheightpos : 0 < height a :=
      Nat.pos_of_floor_pos hfloorpos
    have hheightone : 1 <= height a := by
      have hfloorone : 1 <= Nat.floor (height a) :=
        Nat.succ_le_iff.mpr hfloorpos
      have hfloorle : (Nat.floor (height a) : Real) <= height a :=
        Nat.floor_le hheightpos.le
      exact le_trans (by exact_mod_cast hfloorone) hfloorle
    exact rob_bv_floor_reciprocal_weight_le hheightone (hw a ha)
  calc
    Finset.sum S (fun a => weight a / height a) <=
        Finset.sum S (fun a =>
          (1 / (Nat.floor (height a) : Real)) * weight a) := by
      exact Finset.sum_le_sum (fun a ha => hpoint a ha)
    _ = Finset.sum (Finset.Ioc n m) (fun k =>
        Finset.sum (S.filter (fun a => Nat.floor (height a) = k))
          (fun a => (1 / (Nat.floor (height a) : Real)) * weight a)) := by
      exact (Finset.sum_fiberwise_of_maps_to hmap
        (f := fun a =>
          (1 / (Nat.floor (height a) : Real)) * weight a)).symm
    _ = Finset.sum (Finset.Ioc n m) (fun k =>
        (1 / (k : Real)) *
          Finset.sum (S.filter (fun a => Nat.floor (height a) = k)) weight) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have hak := (Finset.mem_filter.mp ha).2
      rw [hak]

end RobinBV.Sieve
