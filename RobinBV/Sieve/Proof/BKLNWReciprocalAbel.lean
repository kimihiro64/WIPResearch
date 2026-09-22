/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.NumberTheory.AbelSummation

/-!
# Reciprocal Abel summation on natural height bins

This module specializes Abel summation to the reciprocal weight. The identity
retains the cumulative coefficient sum and its integral correction.
-/

set_option autoImplicit false

open scoped BigOperators

namespace RobinBV.Sieve

theorem rob_bv_nat_reciprocal_abel_identity
    {n m : Nat} (hn : 1 <= n) (hnm : n <= m) (c : Nat -> Real) :
    (Finset.sum (Finset.Ioc n m) (fun k =>
      (1 / (k : Real)) * c k)) =
      (1 / (m : Real)) * Finset.sum (Finset.Icc 0 m) c -
        (1 / (n : Real)) * Finset.sum (Finset.Icc 0 n) c -
        (MeasureTheory.integral (MeasureTheory.volume.restrict
          (Set.Ioc (n : Real) (m : Real))) (fun t =>
            (-(1 / (t ^ 2))) * Finset.sum (Finset.Icc 0 (Nat.floor t)) c)) := by
  have hnreal : (0 : Real) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hf_diff : forall t : Real, Membership.mem (Set.Icc (n : Real) m) t ->
      DifferentiableAt Real (fun x : Real => 1 / x) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hnreal (Set.mem_Icc.mp ht).1
    simpa [one_div] using (hasDerivAt_inv htpos.ne').differentiableAt
  have hf_int : MeasureTheory.IntegrableOn (fun t : Real =>
      -(1 / (t ^ 2))) (Set.Icc (n : Real) m) := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.neg
    apply ContinuousOn.div
    next =>
      fun_prop
    next =>
      fun_prop
    next =>
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hnreal (Set.mem_Icc.mp ht).1
      positivity
  have hderiv : deriv (fun t : Real => 1 / t) =
      (fun t : Real => -(1 / (t ^ 2))) := by
    funext t
    by_cases ht : t = 0
    next => simp [ht]
    next =>
      simpa [one_div] using (hasDerivAt_inv ht).deriv
  have hf_int' : MeasureTheory.IntegrableOn
      (deriv (fun t : Real => 1 / t)) (Set.Icc (n : Real) m) := by
    rw [hderiv]
    exact hf_int
  have habel := sum_mul_eq_sub_sub_integral_mul'
    (c := c) (f := fun t : Real => 1 / t) hnm hf_diff hf_int'
  simpa [one_div] using habel

end RobinBV.Sieve
