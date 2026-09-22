/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Finite complex sums with explicit integer multiplicities

This consumer preserves multiplicity weights instead of replacing a weighted
zero sum by an unweighted cardinality bound.
-/

set_option autoImplicit false

namespace Complex

theorem norm_finite_sum_int_multiplicity_le
    {S : Type} [Fintype S] (f : S -> Complex) (m : S -> Int) (w : Real)
    (hpoint : forall z, norm (f z) <= w)
    (hm : forall z, 0 <= (m z : Real)) :
    norm (Finset.univ.sum (fun z => f z * (m z : Complex))) <=
      w * Finset.univ.sum (fun z => (m z : Real)) := by
  calc
    norm (Finset.univ.sum (fun z => f z * (m z : Complex))) <=
        Finset.univ.sum (fun z => norm (f z * (m z : Complex))) := by
      exact norm_sum_le Finset.univ (fun z => f z * (m z : Complex))
    _ = Finset.univ.sum (fun z => norm (f z) * (m z : Real)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [norm_mul]
      simp [abs_of_nonneg (hm z)]
    _ <= Finset.univ.sum (fun z => w * (m z : Real)) := by
      exact Finset.sum_le_sum (fun z hz =>
        mul_le_mul_of_nonneg_right (hpoint z) (hm z))
    _ = w * Finset.univ.sum (fun z => (m z : Real)) := by
      rw [Finset.mul_sum]

end Complex
