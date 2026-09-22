/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.AlmostAllActualPrimeClosure
import RobinBV.Sieve.Proof.AlmostAllAggregation

/-!
# Dyadic density consumer for exceptional square intervals

This module turns a uniform geometric exceptional-block estimate into the
vanishing cumulative dyadic density.  The specialization below keeps the
exceptional set as the actual square-interval prime-count set; no auxiliary
prime-existence predicate is substituted.
-/

set_option autoImplicit false

open Filter
open scoped BigOperators Classical

namespace RobinBV.Sieve

theorem almost_all_cumulative_geometric_density
    {A q b : Real} (hA : 0 <= A) (hq : 1 < q) (hqb : q < b)
    (block : Nat -> Real)
    (hblock : forall k, 0 <= block k /\ block k <= A * q ^ k) :
    Tendsto (fun m : Nat =>
      (Finset.sum (Finset.range m) block) / b ^ m) atTop (nhds 0) := by
  have hb : 0 < b := lt_trans (lt_trans zero_lt_one hq) hqb
  have hq0 : 0 <= q := by linarith
  have hgeom : forall m : Nat,
      Finset.sum (Finset.range m) (fun k => q ^ k) <= q ^ m / (q - 1) := by
    intro m
    have hden : 0 < q - 1 := sub_pos.mpr hq
    have hsum := geom_sum_mul_neg q m
    have hrewrite :
        (Finset.sum (Finset.range m) (fun k => q ^ k)) * (q - 1) = q ^ m - 1 := by
      linarith
    have hpow : 0 <= q ^ m := pow_nonneg hq0 m
    have hmul :
        (Finset.sum (Finset.range m) (fun k => q ^ k)) * (q - 1) <= q ^ m := by
      rw [hrewrite]
      linarith
    have htarget : (q ^ m / (q - 1)) * (q - 1) = q ^ m := by
      field_simp
    apply (le_of_mul_le_mul_right ?_ hden)
    rw [htarget]
    exact hmul
  have hsum : forall m : Nat,
      Finset.sum (Finset.range m) block <= A * q ^ m / (q - 1) := by
    intro m
    have hsum' : Finset.sum (Finset.range m) block <=
        Finset.sum (Finset.range m) (fun k => A * q ^ k) := by
      exact Finset.sum_le_sum (fun k hk =>
        (hblock k).2)
    calc
      Finset.sum (Finset.range m) block <=
          Finset.sum (Finset.range m) (fun k => A * q ^ k) := hsum'
      _ = A * Finset.sum (Finset.range m) (fun k => q ^ k) := by
        rw [Finset.mul_sum]
      _ <= A * (q ^ m / (q - 1)) := by
        exact mul_le_mul_of_nonneg_left (hgeom m) hA
      _ = A * q ^ m / (q - 1) := by ring
  have hratio : 0 <= q / b := div_nonneg hq0 hb.le
  have hratio1 : q / b < 1 := (div_lt_one hb).mpr hqb
  have hpowlim : Tendsto (fun m : Nat => (q / b) ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio hratio1
  have hscale : Tendsto (fun _ : Nat => A / (q - 1)) atTop
      (nhds (A / (q - 1))) := tendsto_const_nhds
  have hright : Tendsto (fun m : Nat =>
      (A / (q - 1)) * (q / b) ^ m) atTop (nhds 0) := by
    simpa using hscale.mul hpowlim
  have hnonneg : forall m : Nat, 0 <=
      (Finset.sum (Finset.range m) block) / b ^ m := by
    intro m
    exact div_nonneg (Finset.sum_nonneg (fun k hk => (hblock k).1))
      (pow_nonneg hb.le m)
  have hupper : forall m : Nat,
      (Finset.sum (Finset.range m) block) / b ^ m <=
        (A / (q - 1)) * (q / b) ^ m := by
    intro m
    have hbound := hsum m
    have hden : 0 < b ^ m := pow_pos hb m
    calc
      (Finset.sum (Finset.range m) block) / b ^ m <=
          (A * q ^ m / (q - 1)) / b ^ m := by
            exact div_le_div_of_nonneg_right hbound (le_of_lt hden)
      _ = (A / (q - 1)) * (q / b) ^ m := by
        rw [div_pow]
        field_simp [ne_of_gt hden, ne_of_gt hb]
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg)
    (Filter.Eventually.of_forall hupper) hright

theorem prime_count_dyadic_density_consequence
    {delta A q b : Real} (hA : 0 <= A) (hq : 1 < q) (hqb : q < b)
    (hblock : forall k : Nat,
      ((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real) <= A * q ^ k) :
    Tendsto (fun m : Nat =>
      (Finset.sum (Finset.range m) (fun k =>
        ((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real))) /
        b ^ m) atTop (nhds 0) := by
  apply almost_all_cumulative_geometric_density hA hq hqb
  intro k
  exact And.intro (by positivity) (hblock k)

theorem prime_count_dyadic_density_from_power_bound
    {delta A alpha : Real} (hA : 0 <= A) (ha0 : 0 < alpha)
    (ha1 : alpha < 1)
    (hblock : forall k : Nat,
      ((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real) <=
        A * (((2 ^ k : Nat) : Real) ^ alpha)) :
    Tendsto (fun m : Nat =>
      (Finset.sum (Finset.range m) (fun k =>
        ((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real))) /
        (2 : Real) ^ m) atTop (nhds 0) := by
  let q : Real := (2 : Real) ^ alpha
  have hq : 1 < q := by
    dsimp [q]
    exact Real.one_lt_rpow (by norm_num) ha0
  have hqb : q < (2 : Real) := by
    dsimp [q]
    simpa only [Real.rpow_one] using
      (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : Real) < 2) ha1)
  apply prime_count_dyadic_density_consequence hA hq hqb
  intro k
  have hpow : (((2 ^ k : Nat) : Real) ^ alpha) = q ^ k := by
    dsimp [q]
    calc
      (((2 ^ k : Nat) : Real) ^ alpha) = (((2 : Real) ^ k) ^ alpha) := by
        norm_num [Nat.cast_pow]
      _ = (2 : Real) ^ ((k : Real) * alpha) := by
        exact (Real.rpow_natCast_mul (by norm_num : 0 <= (2 : Real)) k alpha).symm
      _ = (2 : Real) ^ (alpha * (k : Real)) := by rw [mul_comm]
      _ = ((2 : Real) ^ alpha) ^ (k : Real) := by
        exact Real.rpow_mul (by norm_num : 0 <= (2 : Real)) alpha (k : Real)
      _ = ((2 : Real) ^ alpha) ^ k := by rw [Real.rpow_natCast]
  calc
    ((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real) <=
        A * (((2 ^ k : Nat) : Real) ^ alpha) := hblock k
    _ = A * q ^ k := by rw [hpow]

theorem prime_count_dyadic_density_from_actual_power_bound
    {delta C epsilon : Real} (hd : 0 < delta) (hC : 0 <= C)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hblock : forall k : Nat,
      ((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real) <=
        (8192 * C / delta ^ 5) *
          (((2 ^ k : Nat) : Real) ^ ((1 / 2 : Real) + epsilon))) :
    Tendsto (fun m : Nat =>
      (Finset.sum (Finset.range m) (fun k =>
        ((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real))) /
        (2 : Real) ^ m) atTop (nhds 0) := by
  have hA : 0 <= 8192 * C / delta ^ 5 := by positivity
  have ha0 : 0 < (1 / 2 : Real) + epsilon := by linarith
  have ha1 : (1 / 2 : Real) + epsilon < 1 := by linarith
  exact prime_count_dyadic_density_from_power_bound
    (A := 8192 * C / delta ^ 5) (alpha := (1 / 2 : Real) + epsilon)
    hA ha0 ha1 hblock

theorem prime_count_dyadic_density_from_actual_moment_bounds
    {delta C epsilon : Real} (hd : 0 < delta) (hC : 0 <= C)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hbounds : forall k : Nat, exists M : ENNReal,
      ENNReal.ofReal
          (((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real) *
            delta ^ 5 * ((2 ^ k : Nat) : Real) ^ 5 / 8192) <= M /\
      M <= ENNReal.ofReal
        (C * ((2 ^ k : Nat) : Real)^((11 / 2 : Real) + epsilon))) :
    Tendsto (fun m : Nat =>
      (Finset.sum (Finset.range m) (fun k =>
        ((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real))) /
        (2 : Real) ^ m) atTop (nhds 0) := by
  apply prime_count_dyadic_density_from_actual_power_bound hd hC he0 he1
  intro k
  have hex := hbounds k
  choose M hcost hmoment using hex
  exact prime_count_actual_exceptional_block_bound
    (N := 2 ^ k) (delta := delta) (C := C) (epsilon := epsilon)
    (M := M) (by positivity) hd hC hcost hmoment

theorem prime_count_dyadic_density_from_actual_moment_bounds_after
    {delta C epsilon : Real} (k0 : Nat)
    (hd : 0 < delta) (hC : 0 <= C)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hsmall : forall k : Nat, k < k0 -> exists M : ENNReal,
      ENNReal.ofReal
          (((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real) *
            delta ^ 5 * ((2 ^ k : Nat) : Real) ^ 5 / 8192) <= M /\
      M <= ENNReal.ofReal
        (C * ((2 ^ k : Nat) : Real)^((11 / 2 : Real) + epsilon)))
    (hlarge : forall k : Nat, k0 <= k -> exists M : ENNReal,
      ENNReal.ofReal
          (((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real) *
            delta ^ 5 * ((2 ^ k : Nat) : Real) ^ 5 / 8192) <= M /\
      M <= ENNReal.ofReal
        (C * ((2 ^ k : Nat) : Real)^((11 / 2 : Real) + epsilon))) :
    Tendsto (fun m : Nat =>
      (Finset.sum (Finset.range m) (fun k =>
        ((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real))) /
        (2 : Real) ^ m) atTop (nhds 0) := by
  apply prime_count_dyadic_density_from_actual_moment_bounds
    hd hC he0 he1
  intro k
  rcases lt_or_ge k k0 with hlt | hge
  next => exact hsmall k hlt
  next => exact hlarge k hge

end RobinBV.Sieve
