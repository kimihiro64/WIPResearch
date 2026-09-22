/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.BKLNWZeroesRect

/-!
# Finite density aggregation for the BKLNW height partition

This module composes the endpoint-safe zero-free band estimate with the
actual zero-density mass consumer.  Every interior band and its upper
endpoint retain their height, real-part, density, and multiplicity hypotheses.
-/

set_option autoImplicit false

open scoped BigOperators

namespace RobinBV.Sieve

theorem rob_bv_zeroes_rect_density_finite_aggregation
    {K : Nat} (a b T lambda x R sigma d : Real)
    (ZDB : zero_density_bound)
    (wend Mend : Nat -> Real)
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
    (hwend : forall k, k < K -> 0 <= wend k)
    (hpointEnd : forall k, k < K ->
      forall z : riemannZeta.zeroes_rect (Set.Icc a b)
          ({T / lambda ^ k} : Set Real),
        norm ((x : Complex) ^ ((z : Complex) - 1) / (z : Complex)) <= wend k)
    (hmassEnd : forall k, k < K ->
      let S := riemannZeta.zeroes_rect (Set.Icc a b)
        ({T / lambda ^ k} : Set Real)
      let hfin : S.Finite :=
        (rob_bv_zeroes_rect_Icc_finite a b
          (T / lambda ^ k - 1) (T / lambda ^ k + 1)).subset (by
            intro z hz
            have hlow : T / lambda ^ k - 1 < (z : Complex).im := by
              have h := Set.mem_singleton_iff.mp hz.2.1
              linarith
            have hhigh : (z : Complex).im < T / lambda ^ k + 1 := by
              have h := Set.mem_singleton_iff.mp hz.2.1
              linarith
            exact And.intro hz.1
              (And.intro (And.intro hlow hhigh) hz.2.2))
      letI : Fintype S := hfin.fintype
      Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) <= Mend k) :
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
        (T / lambda ^ (k + 1))) * ZDB.N sigma d + wend k * Mend k)
  intro k hk
  have hTpos : 0 < T := lt_trans zero_lt_one hT
  have hpow : lambda ^ k < lambda ^ (k + 1) := by
    rw [pow_succ]
    have hpk : 0 < lambda ^ k := by positivity
    nlinarith
  have hcdk : T / lambda ^ (k + 1) < T / lambda ^ k := by
    exact (div_lt_div_iff_of_pos_left hTpos (by positivity) (by positivity)).2 hpow
  have hfin :
      (riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))).Finite :=
    rob_bv_zeroes_rect_Icc_finite a b
      (T / lambda ^ (k + 1)) (T / lambda ^ k)
  have hmass :
      let S := riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
      letI : Fintype S := hfin.fintype
      Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) <= ZDB.N sigma d := by
    let S := riemannZeta.zeroes_rect (Set.Icc a b)
      (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
    letI : Fintype S := hfin.fintype
    refine rob_bv_zeroes_rect_mass_le_density_bound sigma d S hfin ?_ ?_ ?_ ?_ ?_
      ZDB hT0 hrange
    next =>
      intro z
      exact z.property.2.2
    next =>
      intro z
      have hz := (Set.mem_Icc.mp z.property.1).1
      exact lt_of_lt_of_le hsigma hz
    next =>
      intro z
      exact lt_of_le_of_lt (Set.mem_Icc.mp z.property.1).2 hb
    next =>
      intro z
      exact lt_trans (by positivity) (Set.mem_Ioo.mp z.property.2.1).1
    next =>
      intro z
      exact lt_trans (Set.mem_Ioo.mp z.property.2.1).2 (hbandUpper k hk)
  exact rob_bv_zeroes_rect_zero_free_height_band_Ioc_sum
    a b T lambda x R (ZDB.N sigma d) (wend k) (Mend k) k hT hlambda
    (hbandLower k hk) hx hR hcdk (hre k hk) hmass
    (hwend k hk) (hpointEnd k hk) (hmassEnd k hk)

end RobinBV.Sieve
