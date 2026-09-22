/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.BKLNWHeightBandEndpointIoc

/-!
# Endpoint-closed finite height-band aggregation

This module consumes the endpoint-closed single-band estimate for every band
in a finite geometric partition.  The endpoint pointwise and endpoint mass
obligations are therefore discharged from the explicit zero-free and density
hypotheses rather than passed as opaque assumptions to the aggregator.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem rob_bv_zeroes_rect_endpoint_closed_finite_aggregation
    {K : Nat} (a b T lambda x R sigma d : Real)
    (ZDB : zero_density_bound) (wend Mend : Nat -> Real)
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
      (z : Complex).re <= 1 - 1 / (R * Real.log (T / lambda ^ k)))
    (hwend : forall k, k < K -> 0 <= wend k)
    (hwendLower : forall k, k < K ->
      x ^ (-(1 / (R * Real.log (T / lambda ^ k)))) /
        (T / lambda ^ k) <= wend k)
    (hmassUpper : forall k, k < K -> ZDB.N sigma d <= Mend k) :
    norm (Finset.sum (Finset.range K) (fun k =>
      riemannZeta.zeroes_sum (Set.Icc a b)
        (Set.Ioc (T / lambda ^ (k + 1)) (T / lambda ^ k))
        (fun z => (x : Complex) ^ (z - 1) / z))) <=
      Finset.sum (Finset.range K) (fun k =>
        (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
          (T / lambda ^ (k + 1))) * ZDB.N sigma d +
          wend k * Mend k) := by
  apply rob_bv_zeroes_rect_zero_free_height_band_finite_aggregation
    a b T lambda x R (fun k =>
      (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
        (T / lambda ^ (k + 1))) * ZDB.N sigma d +
        wend k * Mend k)
  intro k hk
  exact rob_bv_zeroes_rect_endpoint_closed_Ioc_bound
    a b T lambda x R sigma d (wend k) (Mend k) k ZDB hT hlambda
    (hbandLower k hk) hx hR (hbandUpper k hk) hsigma hb hT0 hrange
    (hre k hk) (hreEnd k hk) (hwend k hk) (hwendLower k hk)
    (hmassUpper k hk)

end RobinBV.Sieve
