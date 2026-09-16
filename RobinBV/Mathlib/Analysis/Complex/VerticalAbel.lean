/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.ReciprocalShift

/-!
# Vertical monotone summation by parts

Finite Abel bounds for bounded primitives and weights on a vertical line.
These finite estimates do not assume a prime-distribution theorem.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Complex

theorem norm_sub_eq_abs_im_sub_of_re_eq (a b : Complex) (hre : a.re = b.re) :
    norm (b-a) = abs (b.im-a.im) := by
  have he : b-a = ((b.im-a.im : Real) : Complex)*I := by
    apply Complex.ext <;> simp [hre]
  rw [he, norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]

/-- Vertical monotone Abel weights give a uniform cancellation bound for bounded primitives. -/
theorem norm_sum_mul_diff_le_vertical (u b : Nat -> Complex) (N : Nat)
    {B : Real} (hB : 0 <= B)
    (hu : forall j, j <= N -> norm (u j) <= 1)
    (hb : forall j, j < N -> norm (b j) <= B)
    (hre : forall j, (b j).re = (b 0).re)
    (him : Antitone (fun j => (b j).im)) :
    norm ((Finset.range N).sum (fun j => b j*(u (j+1)-u j))) <= 6*B := by
  by_cases hN : N = 0
  next => simp [hN]; positivity
  have htel (j : Nat) : (Finset.range j).sum (fun i => u (i+1)-u i) = u j-u 0 := by
    induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, ih]; ring
  have hpartial : forall j, j <= N ->
      norm ((Finset.range j).sum (fun i => u (i+1)-u i)) <= (2 : Real) := by
    intro j hj
    rw [htel]
    calc
      _ <= norm (u j)+norm (u 0) := norm_sub_le _ _
      _ <= 1+1 := add_le_add (hu j hj) (hu 0 (by omega))
      _ = 2 := by norm_num
  have hstep (j : Nat) : norm (b (j+1)-b j) = (b j).im-(b (j+1)).im := by
    rw [norm_sub_eq_abs_im_sub_of_re_eq (b j) (b (j+1)) (by rw [hre j, hre (j+1)])]
    have hh := him (show j <= j+1 by omega)
    rw [abs_of_nonpos (sub_nonpos.mpr hh)]
    ring
  have hv : (Finset.range (N-1)).sum (fun j => norm (b (j+1)-b j)) <= 2*B := by
    simp_rw [hstep]
    have he : (Finset.range (N-1)).sum (fun j => (b j).im-(b (j+1)).im) =
        (b 0).im-(b (N-1)).im := by
      induction (N-1) with
      | zero => simp
      | succ j ih => rw [Finset.sum_range_succ, ih]; ring
    rw [he]
    have hzero := (abs_le.mp (abs_im_le_norm (b 0))).2
    have hlast := (abs_le.mp (abs_im_le_norm (b (N-1)))).1
    have hbzero := hb 0 (by omega)
    have hblast := hb (N-1) (by omega)
    linarith
  have h := norm_sum_mul_le_partial_variation (fun j => u (j+1)-u j) b N
    (E := 2) (by norm_num) hpartial
  have hblast := hb (N-1) (by omega)
  nlinarith

end Complex
