/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dyadic harmonic sums

Integral comparison bounds the dyadic reciprocal sum, including an exact
one-row-short endpoint, with absolute error at most the reciprocal base.
-/

set_option autoImplicit false

namespace Real

theorem dyadic_harmonic_full_bounds {P : Nat} (hP : 1 <= P) :
    Real.log 2 <= (Finset.range P).sum (fun i => 1 / ((P:Real)+i)) /\
    (Finset.range P).sum (fun i => 1 / ((P:Real)+i)) <=
      Real.log 2 + 1/(P:Real) := by
  have hp : (0:Real) < P := by exact_mod_cast (show 0<P by omega)
  have hf : AntitoneOn (fun x : Real => 1/x)
      (Set.Icc (P:Real) ((P:Real)+P)) := by
    intro x hx y hy hxy
    exact div_le_div_of_nonneg_left (by norm_num) (lt_of_lt_of_le hp hx.1) hxy
  have hint : intervalIntegral (fun x : Real => 1/x) (P:Real)
      ((P:Real)+P) MeasureTheory.volume = Real.log 2 := by
    rw [integral_one_div_of_pos hp (by positivity)]
    congr 1
    field_simp
    <;> ring
  have hlo := hf.integral_le_sum
  have hhi := hf.sum_le_integral
  rw [hint] at hlo hhi
  have hshift :
      (Finset.range P).sum (fun i => 1/((P:Real)+i)) + 1/((P:Real)+P) =
      (Finset.range P).sum (fun i => 1/((P:Real)+(i+1:Nat))) + 1/(P:Real) := by
    rw [<- Finset.sum_range_succ, Finset.sum_range_succ']
    simp
  have hz : (0:Real) <= 1/((P:Real)+P) := by positivity
  exact And.intro hlo (by linarith)

theorem dyadic_harmonic_abs_error {P N : Nat} (hP : 1<=P)
    (hNP : N<=P) (hPN : P<=N+1) :
    abs ((Finset.range N).sum (fun i => 1/((P:Real)+i)) - Real.log 2)
      <= 1/(P:Real) := by
  have hh := dyadic_harmonic_full_bounds hP
  have hp : (0:Real)<P := by exact_mod_cast (show 0<P by omega)
  have hz : (0:Real)<=1/(P:Real) := by positivity
  have hc : N=P \/ N+1=P := by omega
  rcases hc with he | he
  case inl =>
    subst N
    exact abs_le.mpr (And.intro (by linarith [hh.1]) (by linarith [hh.2]))
  case inr =>
    have hsum : (Finset.range P).sum (fun i => 1/((P:Real)+i)) =
        (Finset.range N).sum (fun i => 1/((P:Real)+i)) + 1/((P:Real)+N) := by
      simpa only [he] using
        (Finset.sum_range_succ (fun i : Nat => 1/((P:Real)+i)) N)
    have ht : (0:Real)<=1/((P:Real)+N) := by positivity
    have hu : 1/((P:Real)+N) <= 1/(P:Real) := by
      apply div_le_div_of_nonneg_left (by norm_num) hp
      exact le_add_of_nonneg_right (Nat.cast_nonneg N)
    rw [hsum] at hh
    exact abs_le.mpr (And.intro (by linarith [hh.1]) (by linarith [hh.2]))

end Real
