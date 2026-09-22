/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.BKLNWEndpointConsumers

/-!
# Endpoint-closed Ioc height-band bound

This module combines the interior density mass, singleton endpoint consumers,
and explicit endpoint envelopes into one Ioc band estimate.  It is the
single-band consumer required before finite A.12 aggregation.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem rob_bv_zeroes_rect_endpoint_closed_Ioc_bound
    (a b T lambda x R sigma d wend Mend : Real) (k : Nat)
    (ZDB : zero_density_bound)
    (hT : 1 < T) (hlambda : 1 < lambda) (hyband : 1 < T / lambda ^ (k + 1))
    (hx : 1 < x) (hR : 0 < R) (hupper : T / lambda ^ k < d)
    (hsigma : sigma < a) (hb : b < 1)
    (hT0 : rob_bv_density_T0 ZDB <= d)
    (hrange : Membership.mem (rob_bv_density_range ZDB) sigma)
    (hre : forall z : riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k)),
      (z : Complex).re <=
        1 - 1 / (R * Real.log (T / lambda ^ (k + 1))))
    (hreEnd : forall z : riemannZeta.zeroes_rect (Set.Icc a b)
        ({T / lambda ^ k} : Set Real),
      (z : Complex).re <= 1 - 1 / (R * Real.log (T / lambda ^ k)))
    (hwend : 0 <= wend)
    (hwendLower : x ^ (-(1 / (R * Real.log (T / lambda ^ k)))) /
      (T / lambda ^ k) <= wend)
    (hmassUpper : ZDB.N sigma d <= Mend) :
    norm (riemannZeta.zeroes_sum (Set.Icc a b)
      (Set.Ioc (T / lambda ^ (k + 1)) (T / lambda ^ k))
      (fun z => (x : Complex) ^ (z - 1) / z)) <=
      (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
      (T / lambda ^ (k + 1))) * ZDB.N sigma d + wend * Mend := by
  let S := riemannZeta.zeroes_rect (Set.Icc a b)
    (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
  have hfin : S.Finite := rob_bv_zeroes_rect_Icc_finite a b
    (T / lambda ^ (k + 1)) (T / lambda ^ k)
  have hmass :
      letI : Fintype S := hfin.fintype
      Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) <= ZDB.N sigma d := by
    letI : Fintype S := hfin.fintype
    refine rob_bv_zeroes_rect_mass_le_density_bound sigma d S hfin ?_ ?_ ?_ ?_ ?_
      ZDB hT0 hrange
    next =>
      intro z
      exact z.property.2.2
    next =>
      intro z
      exact lt_of_lt_of_le hsigma (Set.mem_Icc.mp z.property.1).1
    next =>
      intro z
      exact lt_of_le_of_lt (Set.mem_Icc.mp z.property.1).2 hb
    next =>
      intro z
      exact lt_trans (by positivity) (Set.mem_Ioo.mp z.property.2.1).1
    next =>
      intro z
      exact lt_trans (Set.mem_Ioo.mp z.property.2.1).2 hupper
  have hpointEnd := rob_bv_zeroes_rect_endpoint_pointwise_zero_free
    a b x (T / lambda ^ k) R hx (by
      have hTpos : 0 < T := lt_trans zero_lt_one hT
      have hpow : lambda ^ k < lambda ^ (k + 1) := by
        rw [pow_succ]
        have hpk : 0 < lambda ^ k := by positivity
        nlinarith
      have hcdk : T / lambda ^ (k + 1) < T / lambda ^ k := by
        exact (div_lt_div_iff_of_pos_left hTpos (by positivity) (by positivity)).2 hpow
      exact lt_trans hyband hcdk) hR hreEnd
  have hmassEnd := rob_bv_zeroes_rect_endpoint_mass_le_density
    a b (T / lambda ^ k) sigma d ZDB hsigma hb (by positivity) hupper hT0 hrange
  have hpointEnd' : forall z : riemannZeta.zeroes_rect (Set.Icc a b)
      ({T / lambda ^ k} : Set Real),
      norm ((x : Complex) ^ ((z : Complex) - 1) / (z : Complex)) <= wend := by
    intro z
    exact (hpointEnd z).trans hwendLower
  have hmassEnd' := hmassEnd.trans hmassUpper
  exact rob_bv_zeroes_rect_zero_free_height_band_Ioc_sum
    a b T lambda x R (ZDB.N sigma d) wend Mend k hT hlambda hyband hx hR
    (by
      have hTpos : 0 < T := lt_trans zero_lt_one hT
      have hpow : lambda ^ k < lambda ^ (k + 1) := by
        rw [pow_succ]
        have hpk : 0 < lambda ^ k := by positivity
        nlinarith
      exact (div_lt_div_iff_of_pos_left hTpos (by positivity) (by positivity)).2 hpow)
    hre hmass hwend hpointEnd' hmassEnd'

end RobinBV.Sieve
