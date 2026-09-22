/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Natural-index arithmetic for stepped logarithmic phases

These exact identities isolate the finite index transport and step-window
containment needed by the D-spaced logarithmic correlation consumer.
-/

set_option autoImplicit false

theorem step_index_identity (j h k D : Nat) (hkh : k <= h) :
    j + h * D = k * D + j + (h-k) * D := by
  have hsum : k + (h-k) = h := Nat.add_sub_of_le hkh
  calc
    j + h * D = j + (k + (h-k))*D := by rw [hsum]
    _ = j + (k*D + (h-k)*D) := by rw [Nat.add_mul]
    _ = k*D + j + (h-k)*D := by omega

theorem step_window_identity (k h D : Nat) (hkh : k <= h) :
    k * D + (h-k) * D = h * D := by
  calc
    k * D + (h-k) * D = (k + (h-k)) * D := by rw [Nat.add_mul]
    _ = h * D := by rw [Nat.add_sub_of_le hkh]

theorem step_window_le (h H D : Nat) (hh : h < H) :
    h * D <= H * D := by
  exact Nat.mul_le_mul_right D (Nat.le_of_lt hh)

theorem step_difference_le (h k D : Nat) (hkh : k < h) :
    D <= (h-k) * D := by
  have hsub : 1 <= h-k := Nat.succ_le_iff.mp (Nat.sub_pos_of_lt hkh)
  simpa using Nat.mul_le_mul_right D hsub
