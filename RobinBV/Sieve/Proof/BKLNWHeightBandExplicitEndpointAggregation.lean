/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.BKLNWHeightBandEndpointClosedAggregation

/-!
# Explicit endpoint finite aggregation

This module fixes the endpoint envelope to the exact zero-free weight and
fixes the endpoint mass envelope to the density count.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem rob_bv_zeroes_rect_explicit_endpoint_finite_aggregation
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
          (T / lambda ^ (k + 1))) * ZDB.N sigma d +
        (x ^ (-(1 / (R * Real.log (T / lambda ^ k)))) /
          (T / lambda ^ k) * ZDB.N sigma d)) := by
  apply rob_bv_zeroes_rect_endpoint_closed_finite_aggregation
    a b T lambda x R sigma d ZDB
    (fun k => x ^ (-(1 / (R * Real.log (T / lambda ^ k)))) /
      (T / lambda ^ k))
    (fun _ => ZDB.N sigma d)
    hT hlambda hx hR hsigma hb hT0 hrange hbandLower hbandUpper hre hreEnd
  next =>
    intro k hk
    positivity
  next =>
    intro k hk
    exact le_rfl
  next =>
    intro k hk
    exact le_rfl

end RobinBV.Sieve
