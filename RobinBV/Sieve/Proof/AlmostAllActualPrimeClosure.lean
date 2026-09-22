/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.AlmostAllAggregation
import RobinBV.Sieve.Proof.AlmostAllCardAssembly
import RobinBV.Sieve.Proof.AlmostAllLowCorridorCost

/-!
# Actual-prime exceptional-block consumer

This module performs the exact final algebra from a proved low-zero fourth
moment upper bound to the actual square-interval prime-count exceptional
cardinality.  The analytic moment upper bound remains an explicit input; no
high-zero estimate is hidden in this consumer.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Classical

namespace RobinBV.Sieve

theorem prime_count_bad_block_bound_from_low_moment
    {N : Nat} {delta C epsilon : Real} {B : Finset Nat} {M : ENNReal}
    (hN : 0 < N) (hd : 0 < delta) (hC : 0 <= C)
    (hcost : ENNReal.ofReal
      (((B.card : Real)*delta^5*(N : Real)^5)/8192) <= M)
    (hmoment : M <= ENNReal.ofReal
      (C * (N : Real)^((11 / 2 : Real) + epsilon))) :
    (B.card : Real) <=
      (8192 * C / delta^5) * (N : Real)^((1 / 2 : Real) + epsilon) := by
  have hk : 0 < delta^5 * (N : Real)^5 / 8192 := by positivity
  have hcost' : ENNReal.ofReal
      ((B.card : Real) * (delta^5 * (N : Real)^5 / 8192)) <= M := by
    convert hcost using 1 <;> ring
  have hB : 0 <= C * (N : Real)^((11 / 2 : Real) + epsilon) := by
    positivity
  have hcard := almost_all_card_from_ennreal_cost
    (m := B.card) (k := delta^5 * (N : Real)^5 / 8192)
    (B := C * (N : Real)^((11 / 2 : Real) + epsilon)) (M := M)
    hk hB hcost' hmoment
  have hpow : (N : Real)^((11 / 2 : Real) + epsilon) =
      (N : Real)^((1 / 2 : Real) + epsilon) * (N : Real)^5 := by
    rw [show (11 / 2 : Real) + epsilon =
      (1 / 2 : Real) + epsilon + 5 by ring]
    rw [Real.rpow_add (by positivity : 0 < (N : Real))]
    norm_num [Real.rpow_natCast]
  calc
    (B.card : Real) <=
        (C * (N : Real)^((11 / 2 : Real) + epsilon)) /
          (delta^5 * (N : Real)^5 / 8192) := hcard
    _ = (8192 * C / delta^5) *
        (N : Real)^((1 / 2 : Real) + epsilon) := by
      rw [hpow]
      field_simp

noncomputable def actualPrimeExceptionalBlock (N : Nat) (delta : Real) : Finset Nat :=
  (Finset.Ico N (2*N)).filter (fun n : Nat =>
    Or (((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) <
      (1-delta)*(n : Real)/Real.log n)
      ((1+delta)*(n : Real)/Real.log n <
        ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real)))

theorem prime_count_actual_exceptional_block_bound
    {N : Nat} {delta C epsilon : Real} {M : ENNReal}
    (hN : 0 < N) (hd : 0 < delta) (hC : 0 <= C)
    (hcost : ENNReal.ofReal
      (((actualPrimeExceptionalBlock N delta).card : Real) * delta^5 *
        (N : Real)^5 / 8192) <= M)
    (hmoment : M <= ENNReal.ofReal
      (C * (N : Real)^((11 / 2 : Real) + epsilon))) :
    ((actualPrimeExceptionalBlock N delta).card : Real) <=
      (8192 * C / delta^5) * (N : Real)^((1 / 2 : Real) + epsilon) := by
  exact prime_count_bad_block_bound_from_low_moment hN hd hC hcost hmoment

end RobinBV.Sieve
