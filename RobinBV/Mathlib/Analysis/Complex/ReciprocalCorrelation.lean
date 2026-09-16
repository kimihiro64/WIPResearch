/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.KusminLandau
import RobinBV.Mathlib.Analysis.Complex.ReciprocalDifference

/-!
# Reciprocal-phase correlations

An explicit pointwise correlation estimate in the stated small-increment range.
These finite estimates do not assume a prime-distribution theorem.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Complex

/-- A pointwise correlation estimate for the actual reciprocal phase, with explicit range. -/
theorem norm_sum_exp_reciprocal_difference_le (Y P : Real) (N h : Nat)
    (hY : 0 < Y) (hP : 0 < P) (hh : 0 < h)
    (hsmall : 2*Y*h <= Real.pi*P^3) :
    norm ((Finset.range N).sum (fun j =>
      exp (I*((Y/(P+j+h)-Y/(P+j) : Real) : Complex)))) <=
        3*Real.pi*(P+N+h)^3/(2*Y*h) := by
  have hhR : 0 < (h : Real) := by exact_mod_cast hh
  let f : Nat -> Real := fun j => Real.reciprocalPhaseDifference Y (P+j) h
  let spacing : Real := 2*Y*h/(P+N+h)^3
  have hspacing : 0 < spacing := by dsimp [spacing]; positivity
  have hf (j : Nat) : f (j+1)-f j =
      Real.reciprocalPhaseDifference Y (P+j+1) h-
        Real.reciprocalPhaseDifference Y (P+j) h := by
    simp only [f, Nat.cast_add, Nat.cast_one, add_assoc]
  have bounds (j : Nat) (Q : Real) (hQ : P+j+h+1 <= Q) :=
    Real.reciprocalPhaseDifference_increment_bounds Y hY.le h hP
      (show P <= P+(j : Real) from le_add_of_nonneg_right (Nat.cast_nonneg j)) hQ
  have hcost : 2*Y*h/P^3 <= Real.pi := by
    have hc := div_le_div_of_nonneg_right hsmall (show 0 <= P^3 by positivity)
    have he : (Real.pi*P^3)/P^3 = Real.pi := by field_simp [ne_of_gt hP]
    rwa [he] at hc
  have hpos (j : Nat) : 0 < f (j+1)-f j := by
    rw [hf]
    have hpositive : 0 < 2*Y*(h : Real)/(P+j+h+1)^3 := by positivity
    exact lt_of_lt_of_le hpositive (bounds j (P+j+h+1) le_rfl).1
  have hpi (j : Nat) : f (j+1)-f j <= Real.pi := by
    rw [hf]
    exact (bounds j (P+j+h+1) le_rfl).2.trans hcost
  have hanti : Antitone (fun j => f (j+1)-f j) := by
    intro i j hij
    change f (j+1)-f j <= f (i+1)-f i
    rw [hf i, hf j]
    have hijR : (i : Real) <= j := by exact_mod_cast hij
    exact Real.reciprocalPhaseDifference_increment_antitone Y hY.le h
      (by positivity) (by linarith)
  have hlower (j : Nat) (hj : j < N) : spacing <= f (j+1)-f j := by
    rw [hf]
    have hjR : (j : Real)+1 <= N := by exact_mod_cast (show j+1 <= N by omega)
    exact (bounds j (P+N+h) (by linarith)).1
  have he := norm_sum_exp_le_of_antitone_increment f N hspacing hpos hpi hanti hlower
  have hscale : 3*Real.pi/spacing = 3*Real.pi*(P+N+h)^3/(2*Y*h) := by
    dsimp [spacing]
    field_simp
  rw [hscale] at he
  simpa only [f, Real.reciprocalPhaseDifference] using he

end Complex
