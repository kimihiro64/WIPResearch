/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Second-order remainder of a finite product

The full remainder after linearizing a finite product is bounded by the
corresponding product of nonnegative norms, with its constant and linear
terms removed. A quadratic bound retains the off-diagonal norm mass, so it
vanishes identically for a singleton rather than paying for a diagonal term.

No smallness assumption or truncation of the finite index set is used.
-/

namespace Finset

variable {i R : Type*}

/-- The nonlinear part of a finite product is bounded by its complete scalar
majorant, with exactly the constant and linear terms removed. -/
theorem norm_one_sub_prod_one_sub_sub_sum_le
    [SeminormedCommRing R] [NormOneClass R] (s : Finset i) (u : i -> R) :
    norm (1 - s.prod (fun j => 1 - u j) - s.sum u) <=
      s.prod (fun j => 1 + norm (u j)) - 1 - s.sum (fun j => norm (u j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj, sum_insert hj]
    have hfactor : norm (1 - u j) <= 1 + norm (u j) := by
      simpa only [norm_one] using norm_sub_le (1 : R) (u j)
    have hrec :
        1 - (1 - u j) * s.prod (fun k => 1 - u k) - (u j + s.sum u) =
          (1 - u j) * (1 - s.prod (fun k => 1 - u k) - s.sum u) -
            u j * s.sum u := by ring
    rw [hrec]
    calc
      _ <= norm ((1 - u j) *
            (1 - s.prod (fun k => 1 - u k) - s.sum u)) +
          norm (u j * s.sum u) := norm_sub_le _ _
      _ <= norm (1 - u j) *
            norm (1 - s.prod (fun k => 1 - u k) - s.sum u) +
          norm (u j) * norm (s.sum u) :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ <= (1 + norm (u j)) *
            (s.prod (fun k => 1 + norm (u k)) - 1 - s.sum (fun k => norm (u k))) +
          norm (u j) * s.sum (fun k => norm (u k)) :=
        add_le_add
          (mul_le_mul hfactor ih (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left (norm_sum_le s u) (norm_nonneg _))
      _ = _ := by ring

/-- The scalar product remainder is bounded by the off-diagonal quadratic
mass times the complete product. -/
theorem prod_one_add_sub_one_sub_sum_le_quadratic (s : Finset i) (a : i -> Real)
    (ha : forall j, Membership.mem s j -> 0 <= a j) :
    s.prod (fun j => 1 + a j) - 1 - s.sum a <=
      (((s.sum a) ^ 2 - s.sum (fun j => (a j) ^ 2)) / 2) *
        s.prod (fun j => 1 + a j) := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty => intro ha; simp
  | @insert j s hj ih =>
    intro ha
    have hj0 := ha j (mem_insert_self j s)
    have hs0 : forall k, Membership.mem s k -> 0 <= a k :=
      fun k hk => ha k (mem_insert_of_mem hk)
    have hsum := sum_nonneg hs0
    have hprod : 1 <= s.prod (fun k => 1 + a k) :=
      one_le_prod (fun k hk => by linarith [hs0 k hk])
    have hfactor : 0 <= 1 + a j := by linarith
    have hind := mul_le_mul_of_nonneg_left (ih hs0) hfactor
    have hlinear :
        a j * s.sum a <=
          a j * s.sum a * ((1 + a j) * s.prod (fun k => 1 + a k)) := by
      have hfull : 1 <= (1 + a j) * s.prod (fun k => 1 + a k) := by
        nlinarith [mul_nonneg hj0 (le_trans zero_le_one hprod)]
      nlinarith [mul_nonneg (mul_nonneg hj0 hsum) (sub_nonneg.mpr hfull)]
    rw [prod_insert hj, sum_insert hj, sum_insert hj]
    nlinarith [hind, hlinear]

/-- Uniform second-order control of a finite product, without diagonal loss. -/
theorem norm_one_sub_prod_one_sub_sub_sum_le_quadratic
    [SeminormedCommRing R] [NormOneClass R] (s : Finset i) (u : i -> R) :
    norm (1 - s.prod (fun j => 1 - u j) - s.sum u) <=
      (((s.sum (fun j => norm (u j))) ^ 2 -
        s.sum (fun j => norm (u j) ^ 2)) / 2) *
          s.prod (fun j => 1 + norm (u j)) :=
  (norm_one_sub_prod_one_sub_sub_sum_le s u).trans
    (prod_one_add_sub_one_sub_sum_le_quadratic s _ (fun _ _ => norm_nonneg _))

end Finset
