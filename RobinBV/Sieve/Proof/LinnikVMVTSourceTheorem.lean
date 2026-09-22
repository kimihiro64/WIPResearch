/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMVTCoefficientBound

/-!
# Unconditional source-form Linnik VMVT estimate

This module combines the sharp global recurrence with its exponential
coefficient bound. The final statement has one positive absolute constant and
no auxiliary cutoff, recursive coefficient, unevaluated sum, or product.
-/

theorem exists_linnikVMVT_source_bound :
    exists C : Real, And (0 < C) (forall r k X : Nat,
      0 < r -> 2 <= k -> 0 < X ->
      (Finset.vinogradovMeanValue k (k * r) X : Real) <=
        Real.exp (C * (r : Real) * (k : Real) ^ 2 * Real.log k) *
          (X : Real) ^ linnikVMVTExponent k r) := by
  choose Y0 hglobal using exists_linnikVMVT_sharp_global_coefficient
  refine Exists.intro ((max 13 Y0 : Real) + 8) (And.intro (by positivity) ?_)
  intro r k X hr hk hX
  have hbase := hglobal r k X hr hk hX
  have hcoeff := linnikVMVTSharpCoefficient_le_exp Y0 k (r - 1) hk
  have hindex : r - 1 + 1 = r := by omega
  have hcoeff' : linnikVMVTSharpCoefficient Y0 k (r - 1) <=
      Real.exp (((max 13 Y0 : Real) + 8) * (r : Real) *
        (k : Real) ^ 2 * Real.log k) := by
    simpa only [hindex] using hcoeff
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoeff' (by positivity))
