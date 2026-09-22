/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMTechAsymptotic
import RobinBV.Sieve.Proof.LinnikVMTechSharp

/-!
# VMVT source consumer for the sharp technical estimate

This module substitutes the unconditional VMVT source theorem into the sharp
powered estimate and then takes its full `4 * (k * r) ^ 2` root. Each of the
two VMVT factors occurs once before that root, matching the source proof order.
-/

noncomputable def linnikVMTechSharpSourcePowerRHS
    {k : Nat} (C : Real) (r X L : Nat) (q : Fin k -> Nat) : Real :=
  ((L : Real) ^ (2 * (k * r) - 1)) ^ (2 * (k * r)) *
    (((X : Real) ^ (2 * (k * r))) ^ (2 * (k * r) - 1) *
      ((Real.exp (C * (r : Real) * (k : Real) ^ 2 * Real.log k) *
          (X : Real) ^ linnikVMVTExponent k r) *
        ((Real.exp (C * (r : Real) * (k : Real) ^ 2 * Real.log k) *
            (L : Real) ^ linnikVMVTExponent k r) *
          ((2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
            48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
                (k * r * L ^ (j.val + 1) + 1) +
                (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j))))))

theorem exists_linnik_vmtech_sharp_double_sum_power_source_bound :
    exists C : Real, And (0 < C) (forall
      (k r X L : Nat) (alpha theta : Fin k -> Real)
      (a q : Fin k -> Nat),
      2 <= k -> 0 < r -> 0 < X -> 0 < L ->
      (forall j, 0 < q j) ->
      (forall j, Nat.Coprime (a j) (q j)) ->
      (forall j, abs (theta j) <= 1) ->
      (forall j,
        alpha j = (a j : Real) / q j + theta j / (q j : Real) ^ 2) ->
      norm (linnikVMTechDoubleSum alpha L X) ^
          ((2 * (k * r)) * (2 * (k * r))) <=
        linnikVMTechSharpSourcePowerRHS C r X L q) := by
  choose C hC hvmvt using exists_linnikVMVT_source_bound
  refine Exists.intro C (And.intro hC ?_)
  intro k r X L alpha theta a q hk hr hX hL hq hcop htheta halpha
  have hkr : 0 < k * r := Nat.mul_pos (by omega) hr
  have hbase := linnik_vmtech_double_sum_power_le_sharp_explicit
    k r X L alpha theta a q hkr hq hcop htheta halpha
  have hvmvtX := hvmvt r k X hr hk hX
  have hvmvtL := hvmvt r k L hr hk hL
  simpa only [linnikVMTechSharpSourcePowerRHS] using hbase.trans (by gcongr)

theorem exists_linnik_vmtech_sharp_double_sum_source_root_bound :
    exists C : Real, And (0 < C) (forall
      (k r X L : Nat) (alpha theta : Fin k -> Real)
      (a q : Fin k -> Nat),
      2 <= k -> 0 < r -> 0 < X -> 0 < L ->
      (forall j, 0 < q j) ->
      (forall j, Nat.Coprime (a j) (q j)) ->
      (forall j, abs (theta j) <= 1) ->
      (forall j,
        alpha j = (a j : Real) / q j + theta j / (q j : Real) ^ 2) ->
      norm (linnikVMTechDoubleSum alpha L X) <=
        (linnikVMTechSharpSourcePowerRHS C r X L q) ^
          (1 / (((2 * (k * r)) * (2 * (k * r)) : Nat) : Real))) := by
  choose C hC hsource using
    exists_linnik_vmtech_sharp_double_sum_power_source_bound
  refine Exists.intro C (And.intro hC ?_)
  intro k r X L alpha theta a q hk hr hX hL hq hcop htheta halpha
  have hpower := hsource k r X L alpha theta a q
    hk hr hX hL hq hcop htheta halpha
  have hkr : 0 < k * r := Nat.mul_pos (by omega) hr
  have htwokr : 0 < 2 * (k * r) := Nat.mul_pos (by norm_num) hkr
  have hn : 0 < (2 * (k * r)) * (2 * (k * r)) :=
    Nat.mul_pos htwokr htwokr
  apply linnik_vmtech_le_root_of_pow_le
    (norm (linnikVMTechDoubleSum alpha L X))
    (linnikVMTechSharpSourcePowerRHS C r X L q)
    ((2 * (k * r)) * (2 * (k * r))) (norm_nonneg _) hn
  exact hpower
