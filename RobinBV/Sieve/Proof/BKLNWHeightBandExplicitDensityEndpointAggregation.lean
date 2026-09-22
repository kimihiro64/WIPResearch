/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.BKLNWHeightBandDensityExplicit
import RobinBV.Sieve.Proof.BKLNWHeightBandExplicitEndpointAggregation

/-!
# Explicit density endpoint aggregation

This module replaces the remaining density count in the endpoint-closed
finite aggregation by the explicit density expression supplied by the
zero-density theorem.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem rob_bv_zeroes_rect_explicit_density_endpoint_finite_aggregation
    {K : Nat} (a b T lambda x R sigma d : Real)
    (ZDB : zero_density_bound)
    (hT : 1 < T) (hlambda : 1 < lambda) (hx : 1 < x) (hR : 0 < R)
    (hsigma : sigma < a) (hb : b < 1)
    (hT0 : rob_bv_density_T0 ZDB <= d)
    (hrange : Membership.mem (rob_bv_density_range ZDB) sigma)
    (hbandLower : forall k, k < K -> 1 < T / lambda ^ (k + 1))
    (hbandUpper : forall k, k < K -> T / lambda ^ k < d)
    (hre : forall k, k < K ->
      forall z : riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k)),
      (z : Complex).re <=
        1 - 1 / (R * Real.log (T / lambda ^ (k + 1))))
    (hreEnd : forall k, k < K ->
      forall z : riemannZeta.zeroes_rect (Set.Icc a b)
        ({T / lambda ^ k} : Set Real),
      (z : Complex).re <= 1 - 1 / (R * Real.log (T / lambda ^ k))) :
    norm (Finset.sum (Finset.range K) (fun k =>
      riemannZeta.zeroes_sum (Set.Icc a b)
        (Set.Ioc (T / lambda ^ (k + 1)) (T / lambda ^ k))
        (fun z => (x : Complex) ^ (z - 1) / z))) <=
      Finset.sum (Finset.range K) (fun k =>
        (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
          (T / lambda ^ (k + 1))) *
            ((rob_bv_density_c1 ZDB sigma) * d ^
              (rob_bv_density_p ZDB sigma) *
                (Real.log d) ^ (rob_bv_density_q ZDB sigma) +
              (rob_bv_density_c2 ZDB sigma) * (Real.log d) ^ 2) +
        (x ^ (-(1 / (R * Real.log (T / lambda ^ k)))) /
          (T / lambda ^ k) *
            ((rob_bv_density_c1 ZDB sigma) * d ^
              (rob_bv_density_p ZDB sigma) *
                (Real.log d) ^ (rob_bv_density_q ZDB sigma) +
              (rob_bv_density_c2 ZDB sigma) * (Real.log d) ^ 2))) := by
  let E : Real :=
    (rob_bv_density_c1 ZDB sigma) * d ^ (rob_bv_density_p ZDB sigma) *
        (Real.log d) ^ (rob_bv_density_q ZDB sigma) +
      (rob_bv_density_c2 ZDB sigma) * (Real.log d) ^ 2
  have hN : ZDB.N sigma d <= E := by
    have h := ZDB.bound d hT0 sigma hrange
    simpa [E, zero_density_bound.N, rob_bv_density_c1,
      rob_bv_density_c2, rob_bv_density_p, rob_bv_density_q] using h
  have hbase := rob_bv_zeroes_rect_explicit_endpoint_finite_aggregation
    a b T lambda x R sigma d ZDB hT hlambda hx hR hsigma hb hT0 hrange
    hbandLower hbandUpper hre hreEnd
  calc
    norm (Finset.sum (Finset.range K) (fun k =>
      riemannZeta.zeroes_sum (Set.Icc a b)
        (Set.Ioc (T / lambda ^ (k + 1)) (T / lambda ^ k))
        (fun z => (x : Complex) ^ (z - 1) / z))) <=
        Finset.sum (Finset.range K) (fun k =>
          (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
            (T / lambda ^ (k + 1))) * ZDB.N sigma d +
          (x ^ (-(1 / (R * Real.log (T / lambda ^ k)))) /
            (T / lambda ^ k) * ZDB.N sigma d)) := hbase
    _ <= Finset.sum (Finset.range K) (fun k =>
        (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
          (T / lambda ^ (k + 1))) * E +
        (x ^ (-(1 / (R * Real.log (T / lambda ^ k)))) /
          (T / lambda ^ k) * E)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply add_le_add
      next =>
        exact mul_le_mul_of_nonneg_left hN (by positivity)
      next =>
        exact mul_le_mul_of_nonneg_left hN (by positivity)
    _ = Finset.sum (Finset.range K) (fun k =>
        (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
          (T / lambda ^ (k + 1))) *
            ((rob_bv_density_c1 ZDB sigma) * d ^
              (rob_bv_density_p ZDB sigma) *
                (Real.log d) ^ (rob_bv_density_q ZDB sigma) +
              (rob_bv_density_c2 ZDB sigma) * (Real.log d) ^ 2) +
        (x ^ (-(1 / (R * Real.log (T / lambda ^ k)))) /
          (T / lambda ^ k) *
            ((rob_bv_density_c1 ZDB sigma) * d ^
              (rob_bv_density_p ZDB sigma) *
                (Real.log d) ^ (rob_bv_density_q ZDB sigma) +
              (rob_bv_density_c2 ZDB sigma) * (Real.log d) ^ 2))) := by
      rfl

end RobinBV.Sieve
