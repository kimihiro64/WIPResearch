/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite reciprocal-phase denominator shifts

Finite summation by parts controls a monotone phase perturbation without
changing its coefficient sequence. In particular, a bound on all unshifted
reciprocal exponential prefixes transfers to every bounded positive denominator
shift with an explicit variation factor. No prime-distribution estimate is
asserted by these coefficient-independent statements.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Complex

/-- The unit-circle exponential changes by at most the angular displacement. -/
theorem norm_exp_I_mul_sub_le (x y : Real) :
    norm (exp (I * (x : Complex)) - exp (I * (y : Complex))) <= abs (x-y) := by
  have he : exp (I * (x : Complex)) - exp (I * (y : Complex)) =
      exp (I * (y : Complex)) * (exp (I * ((x-y : Real) : Complex)) - 1) := by
    rw [mul_sub, <- exp_add, mul_one]
    congr 1
    push_cast
    ring
  rw [he, norm_mul, norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x-y))

/-- A finite prefix bound is preserved up to the endpoint norm and total variation. -/
theorem norm_sum_mul_le_partial_variation (a b : Nat -> Complex) (N : Nat)
    {E : Real} (_hE : 0 <= E)
    (hpartial : forall j, j <= N -> norm ((Finset.range j).sum a) <= E) :
    norm ((Finset.range N).sum (fun j => b j * a j)) <=
      E * (norm (b (N-1)) +
        (Finset.range (N-1)).sum (fun j => norm (b (j+1)-b j))) := by
  have he := Finset.sum_range_by_parts b a N
  simp only [smul_eq_mul] at he
  rw [he]
  calc
    _ <= norm (b (N-1) * (Finset.range N).sum a) +
        norm ((Finset.range (N-1)).sum
          (fun j => (b (j+1)-b j) * (Finset.range (j+1)).sum a)) := norm_sub_le _ _
    _ <= norm (b (N-1)) * E +
        (Finset.range (N-1)).sum (fun j => norm (b (j+1)-b j) * E) := by
      apply add_le_add
      next =>
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpartial N le_rfl) (norm_nonneg _)
      next =>
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (hpartial (j+1) (by have := Finset.mem_range.mp hj; omega)) (norm_nonneg _)
    _ = _ := by rw [<- Finset.sum_mul]; ring

/-- A nonnegative decreasing phase costs at most one plus its initial value. -/
theorem norm_sum_mul_exp_neg_antitone_le (a : Nat -> Complex) (g : Nat -> Real)
    (N : Nat) {E : Real} (hE : 0 <= E)
    (hpartial : forall j, j <= N -> norm ((Finset.range j).sum a) <= E)
    (hg : Antitone g) (hg0 : forall j, 0 <= g j) :
    norm ((Finset.range N).sum
      (fun j => exp (I * ((-g j : Real) : Complex)) * a j)) <= E * (1 + g 0) := by
  have h := norm_sum_mul_le_partial_variation a
    (fun j => exp (I * ((-g j : Real) : Complex))) N hE hpartial
  have hv : (Finset.range (N-1)).sum (fun j =>
      norm (exp (I * ((-g (j+1) : Real) : Complex)) -
        exp (I * ((-g j : Real) : Complex)))) <= g 0 := by
    calc
      _ <= (Finset.range (N-1)).sum (fun j => g j - g (j+1)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjg := hg (show j <= j+1 by omega)
        have hb := norm_exp_I_mul_sub_le (-g (j+1)) (-g j)
        rw [show -g (j+1) - -g j = g j - g (j+1) by ring,
          abs_of_nonneg (sub_nonneg.mpr hjg)] at hb
        exact hb
      _ = g 0 - g (N-1) := by
        induction (N-1) with
        | zero => simp
        | succ k ih => rw [Finset.sum_range_succ, ih]; ring
      _ <= g 0 := sub_le_self _ (hg0 _)
  simp only [norm_exp_I_mul_ofReal] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hv) hE)

/-- A positive reciprocal denominator shift preserves arbitrary coefficients and costs
at most one plus the initial exact phase displacement. -/
theorem norm_sum_reciprocal_shift_le (a : Nat -> Complex) (N : Nat)
    {X P c E : Real} (hX : 0 <= X) (hP : 0 < P) (hc : 0 <= c) (hE : 0 <= E)
    (hpartial : forall j, j <= N ->
      norm ((Finset.range j).sum (fun i =>
        a i * exp (I * ((X / (P+i) : Real) : Complex)))) <= E) :
    norm ((Finset.range N).sum (fun i =>
      a i * exp (I * ((X / (P+i+c) : Real) : Complex)))) <=
      E * (1 + X*c/(P*(P+c))) := by
  let g : Nat -> Real := fun i => X*c/((P+i)*(P+i+c))
  have hg0 : forall i, 0 <= g i := by
    intro i
    dsimp [g]
    positivity
  have hg : Antitone g := by
    intro i j hij
    have hijR : (i : Real) <= j := by exact_mod_cast hij
    have hi : 0 < P+i := by positivity
    have hj : 0 < P+j := by positivity
    have hic : 0 < P+i+c := by positivity
    have hjc : 0 < P+j+c := by positivity
    have hd : (P+i)*(P+i+c) <= (P+j)*(P+j+c) :=
      mul_le_mul (by linarith) (by linarith) hic.le hj.le
    exact div_le_div_of_nonneg_left (mul_nonneg hX hc) (mul_pos hi hic) hd
  have h := norm_sum_mul_exp_neg_antitone_le
    (fun i => a i * exp (I * ((X/(P+i) : Real) : Complex))) g N hE hpartial hg hg0
  have he (i : Nat) :
      exp (I * ((-g i : Real) : Complex)) *
        (a i * exp (I * ((X/(P+i) : Real) : Complex))) =
      a i * exp (I * ((X/(P+i+c) : Real) : Complex)) := by
    have hi : Not (P+(i : Real) = 0) := ne_of_gt (by positivity)
    have hic : Not (P+(i : Real)+c = 0) := ne_of_gt (by positivity)
    have hr : -g i + X/(P+i) = X/(P+i+c) := by
      dsimp [g]
      field_simp
      <;> ring
    calc
      _ = a i * (exp (I * ((-g i : Real) : Complex)) *
          exp (I * ((X/(P+i) : Real) : Complex))) := by ring
      _ = a i * exp (I * ((-g i + X/(P+i) : Real) : Complex)) := by
        rw [<- exp_add, Complex.ofReal_add, mul_add]
      _ = _ := by rw [hr]
  simp only [he] at h
  simpa only [g, Nat.cast_zero, add_zero] using h

end Complex
