/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import RobinBV.Mathlib.Analysis.Complex.ReciprocalSum

/-!
# Finite uniform-correlation van der Corput consumer

This module converts explicit uniform diagonal and off-diagonal correlation
bounds into a finite shifted-sum estimate.  The Gram energy, square-root step,
and exact endpoint cost are all retained.  No prime-count or zeta estimate is
assumed here.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Complex

theorem norm_sum_mul_shift_le_of_uniform_correlation
    (b : Nat -> Complex) (a : Nat -> Nat -> Complex)
    (N H : Nat) (B C : Real)
    (ha : forall j, norm (b j) <= 1)
    (ha_shift : forall j h, a j h = b (j+h))
    (hdiag : forall h, Membership.mem (Finset.range H) h ->
      ((Finset.range N).sum (fun j => a j h * star (a j h))).re <= B)
    (hoff : forall h, Membership.mem (Finset.range H) h ->
      forall k, Membership.mem (Finset.range H) k -> Not (h = k) ->
        ((Finset.range N).sum (fun j => a j h * star (a j k))).re <= C)
    (hE : 0 <= (N : Real) *
      ((H : Real) * B + ((H : Real)^2 - H) * C)) :
    (H : Real) * norm ((Finset.range N).sum b) <=
      Real.sqrt ((N : Real) *
        ((H : Real) * B + ((H : Real)^2 - H) * C)) +
        (H : Real) * (H - 1) := by
  have henergy := norm_sum_sq_le_uniform_gram
    (Finset.range N) (Finset.range H) a B C hdiag hoff
  have henergy' : norm ((Finset.range N).sum (fun j =>
      (Finset.range H).sum (fun h => a j h)))^2 <=
      (N : Real) * ((H : Real) * B + ((H : Real)^2 - H) * C) := by
    simpa only [Finset.card_range] using henergy
  have hroot : norm ((Finset.range N).sum (fun j =>
      (Finset.range H).sum (fun h => a j h))) <=
      Real.sqrt ((N : Real) *
        ((H : Real) * B + ((H : Real)^2 - H) * C)) := by
    have hsqrt := Real.sq_sqrt hE
    nlinarith [henergy', Real.sqrt_nonneg
      ((N : Real) * ((H : Real) * B + ((H : Real)^2 - H) * C)),
      norm_nonneg ((Finset.range N).sum (fun j =>
        (Finset.range H).sum (fun h => a j h)))]
  have hboundary := norm_sum_le_shift_average_boundary b N H 1 ha
  have hboundary' : (H : Real) * norm ((Finset.range N).sum b) <=
      norm ((Finset.range N).sum (fun j =>
        (Finset.range H).sum (fun h => a j h))) + (H : Real) * (H - 1) := by
    simpa [Nat.mul_one, ha_shift] using hboundary
  linarith [hroot, hboundary']

theorem norm_sum_mul_step_shift_le_of_uniform_correlation
    (b : Nat -> Complex) (a : Nat -> Nat -> Complex)
    (N H D : Nat) (B C : Real)
    (ha : forall j, norm (b j) <= 1)
    (ha_shift : forall j h, a j h = b (j+h*D))
    (hdiag : forall h, Membership.mem (Finset.range H) h ->
      ((Finset.range N).sum (fun j => a j h * star (a j h))).re <= B)
    (hoff : forall h, Membership.mem (Finset.range H) h ->
      forall k, Membership.mem (Finset.range H) k -> Not (h = k) ->
        ((Finset.range N).sum (fun j => a j h * star (a j k))).re <= C)
    (hE : 0 <= (N : Real) *
      ((H : Real) * B + ((H : Real)^2 - H) * C)) :
    (H : Real) * norm ((Finset.range N).sum b) <=
      Real.sqrt ((N : Real) *
        ((H : Real) * B + ((H : Real)^2 - H) * C)) +
        (D : Real) * H * (H - 1) := by
  have henergy := norm_sum_sq_le_uniform_gram
    (Finset.range N) (Finset.range H) a B C hdiag hoff
  have henergy' : norm ((Finset.range N).sum (fun j =>
      (Finset.range H).sum (fun h => a j h)))^2 <=
      (N : Real) * ((H : Real) * B + ((H : Real)^2 - H) * C) := by
    simpa only [Finset.card_range] using henergy
  have hroot : norm ((Finset.range N).sum (fun j =>
      (Finset.range H).sum (fun h => a j h))) <=
      Real.sqrt ((N : Real) *
        ((H : Real) * B + ((H : Real)^2 - H) * C)) := by
    have hsqrt := Real.sq_sqrt hE
    nlinarith [henergy', Real.sqrt_nonneg
      ((N : Real) * ((H : Real) * B + ((H : Real)^2 - H) * C)),
      norm_nonneg ((Finset.range N).sum (fun j =>
        (Finset.range H).sum (fun h => a j h)))]
  have hboundary := norm_sum_le_shift_average_boundary b N H D ha
  have hboundary' : (H : Real) * norm ((Finset.range N).sum b) <=
      norm ((Finset.range N).sum (fun j =>
        (Finset.range H).sum (fun h => a j h))) +
        (D : Real) * H * (H - 1) := by
    simpa [ha_shift] using hboundary
  linarith [hroot, hboundary']

end Complex
