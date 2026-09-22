/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RobinBV.Mathlib.Analysis.Complex.KusminLandau

/-!
# Explicit logarithmic-phase correlation bound

This module proves the finite logarithmic Type-II correlation estimate used
by the planned differencing step for the almost-all Legendre argument.  It is
an unconditional Kusmin-Landau estimate with explicit spacing, endpoint, and
small-increment hypotheses; it is not by itself the full Korobov-Vinogradov
saving.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Complex

theorem norm_sum_exp_log_difference_le (Y P : Real) (N h : Nat)
    (hY : 0 < Y) (hP : 0 < P) (hh : 0 < h)
    (hsmall : Y * (h : Real) <= Real.pi * P^2) :
    norm ((Finset.range N).sum (fun j =>
      exp (I * ((-Y * (Real.log (P + j + h) - Real.log (P + j)) : Real) : Complex)))) <=
        3 * Real.pi * (P + N + h + 1)^2 / (Y * h) := by
  have hhR : 0 < (h : Real) := by exact_mod_cast hh
  let f : Nat -> Real := fun j =>
    -Y * (Real.log (P + (j : Real) + h) - Real.log (P + (j : Real)))
  let spacing : Real := Y * (h : Real) / (P + (N : Real) + h + 1)^2
  have hspacing : 0 < spacing := by
    dsimp [spacing]
    positivity
  have hpos (j : Nat) : 0 < f (j+1)-f j := by
    dsimp [f]
    have hPj : 0 < P + (j : Real) := by positivity
    have hPjh : 0 < P + (j : Real) + h := by positivity
    have hPj1 : 0 < P + (j : Real) + 1 := by positivity
    have hPjh1 : 0 < P + (j : Real) + h + 1 := by positivity
    have hformula :
        (Real.log (P + (j : Real) + h) - Real.log (P + (j : Real))) -
            (Real.log (P + (j : Real) + h + 1) -
              Real.log (P + (j : Real) + 1)) =
          Real.log (1 + h / ((P + (j : Real)) *
            (P + (j : Real) + h + 1))) := by
      calc
        _ = Real.log ((P + (j : Real) + h) / (P + (j : Real))) -
            Real.log ((P + (j : Real) + h + 1) /
              (P + (j : Real) + 1)) := by
          rw [Real.log_div (ne_of_gt hPjh) (ne_of_gt hPj),
            Real.log_div (ne_of_gt hPjh1) (ne_of_gt hPj1)]
        _ = Real.log (((P + (j : Real) + h) / (P + (j : Real))) /
            ((P + (j : Real) + h + 1) /
              (P + (j : Real) + 1))) := by
          symm
          exact Real.log_div (by positivity) (by positivity)
        _ = Real.log (1 + h / ((P + (j : Real)) *
            (P + (j : Real) + h + 1))) := by
          congr 1
          field_simp
          ring
    have hdiff : f (j+1)-f j = Y * Real.log (1 + h / ((P + (j : Real)) *
        (P + (j : Real) + h + 1))) := by
      have hj1 : ((j + 1 : Nat) : Real) = (j : Real) + 1 := by
        norm_num
      calc
        f (j+1)-f j = Y * ((Real.log (P + (j : Real) + h) -
            Real.log (P + (j : Real))) -
            (Real.log (P + (j : Real) + h + 1) -
              Real.log (P + (j : Real) + 1))) := by
          dsimp [f]
          rw [hj1]
          ring
        _ = Y * Real.log (1 + h / ((P + (j : Real)) *
            (P + (j : Real) + h + 1))) := by rw [hformula]
    rw [hdiff]
    have hu : 0 <= h / ((P + (j : Real)) *
        (P + (j : Real) + h + 1)) := by positivity
    have hlog : h / ((P + (j : Real)) *
        (P + (j : Real) + h + 1)) /
          (1 + h / ((P + (j : Real)) *
            (P + (j : Real) + h + 1))) <=
        Real.log (1 + h / ((P + (j : Real)) *
            (P + (j : Real) + h + 1))) := by
      have hinv : 0 < 1 / (1 + h / ((P + (j : Real)) *
          (P + (j : Real) + h + 1))) := by positivity
      have hloginv := Real.log_le_sub_one_of_pos hinv
      have hrewrite : Real.log (1 / (1 + h / ((P + (j : Real)) *
          (P + (j : Real) + h + 1)))) =
          -Real.log (1 + h / ((P + (j : Real)) *
            (P + (j : Real) + h + 1))) := by
        rw [one_div, Real.log_inv]
      rw [hrewrite] at hloginv
      have hden : 0 < 1 + h / ((P + (j : Real)) *
          (P + (j : Real) + h + 1)) := by positivity
      have hfrac : 1 / (1 + h / ((P + (j : Real)) *
          (P + (j : Real) + h + 1))) - 1 =
          -(h / ((P + (j : Real)) *
            (P + (j : Real) + h + 1))) /
              (1 + h / ((P + (j : Real)) *
                (P + (j : Real) + h + 1))) := by
        field_simp
        ring
      rw [hfrac] at hloginv
      have hneg := neg_le_neg hloginv
      simpa only [neg_div, neg_neg] using hneg
    have hlogpos : 0 < Real.log (1 + h / ((P + (j : Real)) *
        (P + (j : Real) + h + 1))) :=
      lt_of_lt_of_le (by positivity) hlog
    exact mul_pos hY hlogpos
  have hdiff0 (j : Nat) : f (j+1)-f j = Y * Real.log (1 + h / ((P + (j : Real)) *
      (P + (j : Real) + h + 1))) := by
    have hj1 : ((j + 1 : Nat) : Real) = (j : Real) + 1 := by norm_num
    have hPj : 0 < P + (j : Real) := by positivity
    have hPjh : 0 < P + (j : Real) + h := by positivity
    have hPj1 : 0 < P + (j : Real) + 1 := by positivity
    have hPjh1 : 0 < P + (j : Real) + h + 1 := by positivity
    have hformula :
        (Real.log (P + (j : Real) + h) - Real.log (P + (j : Real))) -
            (Real.log (P + (j : Real) + h + 1) -
              Real.log (P + (j : Real) + 1)) =
          Real.log (1 + h / ((P + (j : Real)) *
            (P + (j : Real) + h + 1))) := by
      calc
        _ = Real.log ((P + (j : Real) + h) / (P + (j : Real))) -
            Real.log ((P + (j : Real) + h + 1) /
              (P + (j : Real) + 1)) := by
          rw [Real.log_div (ne_of_gt hPjh) (ne_of_gt hPj),
            Real.log_div (ne_of_gt hPjh1) (ne_of_gt hPj1)]
        _ = Real.log (((P + (j : Real) + h) / (P + (j : Real))) /
            ((P + (j : Real) + h + 1) /
              (P + (j : Real) + 1))) := by
          symm
          exact Real.log_div (by positivity) (by positivity)
        _ = Real.log (1 + h / ((P + (j : Real)) *
            (P + (j : Real) + h + 1))) := by
          congr 1
          field_simp
          ring
    calc
      f (j+1)-f j = Y * ((Real.log (P + (j : Real) + h) -
          Real.log (P + (j : Real))) -
          (Real.log (P + (j : Real) + h + 1) -
            Real.log (P + (j : Real) + 1))) := by
        dsimp [f]
        rw [hj1]
        ring
      _ = Y * Real.log (1 + h / ((P + (j : Real)) *
          (P + (j : Real) + h + 1))) := by rw [hformula]
  have hpi (j : Nat) : f (j+1)-f j <= Real.pi := by
    rw [hdiff0]
    let u : Real := h / ((P + (j : Real)) * (P + (j : Real) + h + 1))
    have hu : 0 <= u := by dsimp [u]; positivity
    have hlog : Real.log (1 + u) <= u := by
      have htmp := Real.log_le_sub_one_of_pos (show 0 < 1 + u by linarith)
      linarith
    have hden : P^2 <= (P + (j : Real)) * (P + (j : Real) + h + 1) := by
      nlinarith [sq_nonneg P, sq_nonneg (j : Real), sq_nonneg h]
    have hu' : u <= h / P^2 := by
      dsimp [u]
      exact div_le_div_of_nonneg_left hhR.le (by positivity) hden
    dsimp [u] at hlog hu'
    have hmul := mul_le_mul_of_nonneg_left hlog hY.le
    have hmul' := mul_le_mul_of_nonneg_left hu' hY.le
    have hsmall' : Y * (h : Real) / P^2 <= Real.pi := by
      have hP2 : 0 < P^2 := by positivity
      apply le_of_mul_le_mul_right _ hP2
      calc
        (Y * (h : Real) / P^2) * P^2 = Y * (h : Real) := by field_simp
        _ <= Real.pi * P^2 := hsmall
    have hsmall'' : Y * ((h : Real) / P^2) <= Real.pi := by
      convert hsmall' using 1 <;> ring
    exact (hmul.trans hmul').trans hsmall''
  have hanti : Antitone (fun j => f (j+1)-f j) := by
    intro i j hij
    change f (j+1)-f j <= f (i+1)-f i
    rw [hdiff0, hdiff0]
    let ui : Real := h / ((P + (i : Real)) * (P + (i : Real) + h + 1))
    let uj : Real := h / ((P + (j : Real)) * (P + (j : Real) + h + 1))
    have hijR : (i : Real) <= (j : Real) := by exact_mod_cast hij
    have hden : (P + (i : Real)) * (P + (i : Real) + h + 1) <=
        (P + (j : Real)) * (P + (j : Real) + h + 1) := by
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have hu : uj <= ui := by
      dsimp [ui, uj]
      exact div_le_div_of_nonneg_left hhR.le (by positivity) hden
    have hlog : Real.log (1 + uj) <= Real.log (1 + ui) := by
      exact Real.strictMonoOn_log.monotoneOn
        (by change 0 < 1 + uj; positivity)
        (by change 0 < 1 + ui; positivity)
        (by linarith)
    dsimp [ui, uj] at hu hlog
    exact mul_le_mul_of_nonneg_left hlog hY.le
  have hlower (j : Nat) (hj : j < N) : spacing <= f (j+1)-f j := by
    rw [hdiff0]
    let u : Real := h / ((P + (j : Real)) * (P + (j : Real) + h + 1))
    have hu : 0 <= u := by dsimp [u]; positivity
    have hlog : u / (1 + u) <= Real.log (1 + u) := by
      have htmp := Real.log_le_sub_one_of_pos (show 0 < 1 / (1 + u) by positivity)
      have hrewrite : Real.log (1 / (1 + u)) = -Real.log (1 + u) := by
        rw [one_div, Real.log_inv]
      rw [hrewrite] at htmp
      have hfrac : 1 / (1 + u) - 1 = -u / (1 + u) := by field_simp; ring
      rw [hfrac] at htmp
      have hneg := neg_le_neg htmp
      simpa only [neg_div, neg_neg] using hneg
    have hjN : (j : Real) <= (N : Real) := by
      exact_mod_cast (Nat.le_of_lt hj)
    have hden : (P + (j : Real)) * (P + (j : Real) + h + 1) + h <=
        (P + (N : Real) + h + 1)^2 := by
      nlinarith [sq_nonneg (P + (N : Real) + h + 1), sq_nonneg (P + (j : Real)),
        sq_nonneg h]
    have hfrac : (h : Real) /
        (P + (N : Real) + h + 1)^2 <=
        (h : Real) /
          ((P + (j : Real)) * (P + (j : Real) + h + 1) + h) := by
      exact div_le_div_of_nonneg_left hhR.le (by positivity) hden
    have hfracY := mul_le_mul_of_nonneg_left hfrac hY.le
    have hmul := mul_le_mul_of_nonneg_left hlog hY.le
    have hu_eq : u / (1 + u) = (h : Real) /
        ((P + (j : Real)) * (P + (j : Real) + h + 1) + h) := by
      dsimp [u]
      field_simp
    rw [hu_eq] at hmul
    dsimp [spacing, u]
    calc
      Y * (h : Real) / (P + (N : Real) + h + 1)^2 <=
          Y * ((h : Real) /
            ((P + (j : Real)) * (P + (j : Real) + h + 1) + h)) := by
        calc
          _ = Y * ((h : Real) / (P + (N : Real) + h + 1)^2) := by ring
          _ <= _ := hfracY
      _ <= Y * Real.log (1 + h / ((P + (j : Real)) *
          (P + (j : Real) + h + 1))) := by
        exact hmul
  have hmain := norm_sum_exp_le_of_antitone_increment f N hspacing hpos hpi hanti hlower
  have hscale : 3 * Real.pi / spacing =
      3 * Real.pi * (P + (N : Real) + h + 1)^2 / (Y * (h : Real)) := by
    dsimp [spacing]
    field_simp
  rw [hscale] at hmain
  simpa [f] using hmain

end Complex
