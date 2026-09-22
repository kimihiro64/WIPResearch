/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Finite band sum consumers

This module records the finite-subtype and finite-band norm bounds used to
turn pointwise zero estimates into explicit finite sums.
-/

set_option autoImplicit false

theorem rob_bv_finite_subtype_count_consumer
    {S : Type} [Fintype S] (f : S -> Complex) (w : Real)
    (hpoint : forall z, norm (f z) <= w) :
    norm (Finset.univ.sum f) <= (Fintype.card S : Real) * w := by
  calc
    norm (Finset.univ.sum f) <= Finset.univ.sum (fun z => norm (f z)) := by
      exact norm_sum_le Finset.univ f
    _ <= Finset.univ.sum (fun _ => w) := by
      exact Finset.sum_le_sum (fun z hz => hpoint z)
    _ = (Fintype.card S : Real) * w := by
      simp [Finset.sum_const, mul_comm]

theorem rob_bv_zero_band_count_consumer
    {A : Finset Complex} (f : Complex -> Complex) (w : Real)
    (hpoint : forall z, Membership.mem A z -> norm (f z) <= w) :
    norm (Finset.sum A f) <= (A.card : Real) * w := by
  calc
    norm (Finset.sum A f) <= Finset.sum A (fun z => norm (f z)) := by
      exact norm_sum_le A f
    _ <= Finset.sum A (fun _ => w) := by
      exact Finset.sum_le_sum (fun z hz => hpoint z hz)
    _ = (A.card : Real) * w := by
      simp [Finset.sum_const, mul_comm]
