/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.BKLNWHeightBandDensityAggregation

/-!
# Explicit density-field substitution for a BKLNW height band

This module exposes the numerical content of a `zero_density_bound` at a
single height band.  The positive zero-free weight is proved nonnegative, so
the structure's explicit `c1`, `c2`, `p`, and `q` bound can replace `N` in the
correct direction without hiding a sign assumption.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

def rob_bv_density_c1 : zero_density_bound -> Real -> Real
  | zero_density_bound.mk t s c1 c2 p q b, sigma => c1 sigma

def rob_bv_density_c2 : zero_density_bound -> Real -> Real
  | zero_density_bound.mk t s c1 c2 p q b, sigma => c2 sigma

def rob_bv_density_p : zero_density_bound -> Real -> Real
  | zero_density_bound.mk t s c1 c2 p q b, sigma => p sigma

def rob_bv_density_q : zero_density_bound -> Real -> Real
  | zero_density_bound.mk t s c1 c2 p q b, sigma => q sigma

theorem rob_bv_density_band_term_le_explicit
    (a b T lambda x R sigma d : Real) (k : Nat)
    (ZDB : zero_density_bound)
    (hT : 1 < T) (hlambda : 1 < lambda) (hx : 1 < x) (hR : 0 < R)
    (hT0 : rob_bv_density_T0 ZDB <= d)
    (hrange : Membership.mem (rob_bv_density_range ZDB) sigma) :
    (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
      (T / lambda ^ (k + 1))) * ZDB.N sigma d <=
      (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
        (T / lambda ^ (k + 1))) *
        ((rob_bv_density_c1 ZDB sigma) * d ^ (rob_bv_density_p ZDB sigma) *
            (Real.log d) ^ (rob_bv_density_q ZDB sigma) +
          (rob_bv_density_c2 ZDB sigma) * (Real.log d) ^ 2) := by
  have hN := ZDB.bound d hT0 sigma hrange
  have hN' : ZDB.N sigma d <=
      (rob_bv_density_c1 ZDB sigma) * d ^ (rob_bv_density_p ZDB sigma) *
          (Real.log d) ^ (rob_bv_density_q ZDB sigma) +
        (rob_bv_density_c2 ZDB sigma) * (Real.log d) ^ 2 := by
    simpa [zero_density_bound.N, rob_bv_density_c1, rob_bv_density_c2,
      rob_bv_density_p, rob_bv_density_q] using hN
  have hTpos : 0 < T := lt_trans zero_lt_one hT
  have hden : 0 < T / lambda ^ (k + 1) := by positivity
  have hweight : 0 <=
      x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
        (T / lambda ^ (k + 1)) := by
    exact (div_nonneg
      (le_of_lt (Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) _)) hden.le)
  exact mul_le_mul_of_nonneg_left hN' hweight

theorem rob_bv_zeroes_rect_density_finite_explicit_aggregation
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
          (T / lambda ^ (k + 1))) *
          ((rob_bv_density_c1 ZDB sigma) * d ^ (rob_bv_density_p ZDB sigma) *
              (Real.log d) ^ (rob_bv_density_q ZDB sigma) +
            (rob_bv_density_c2 ZDB sigma) * (Real.log d) ^ 2) +
        wend k * Mend k) := by
  have hagg := rob_bv_zeroes_rect_density_finite_aggregation
    a b T lambda x R sigma d ZDB wend Mend hT hlambda hx hR hsigma hb hT0
    hrange hbandLower hbandUpper hre hwend hpointEnd hmassEnd
  have hsum :
      Finset.sum (Finset.range K) (fun k =>
        (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
          (T / lambda ^ (k + 1))) * ZDB.N sigma d + wend k * Mend k) <=
      Finset.sum (Finset.range K) (fun k =>
        (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
          (T / lambda ^ (k + 1))) *
          ((rob_bv_density_c1 ZDB sigma) * d ^ (rob_bv_density_p ZDB sigma) *
              (Real.log d) ^ (rob_bv_density_q ZDB sigma) +
            (rob_bv_density_c2 ZDB sigma) * (Real.log d) ^ 2) +
        wend k * Mend k) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkN := rob_bv_density_band_term_le_explicit
      a b T lambda x R sigma d k ZDB hT hlambda hx hR hT0 hrange
    simpa [add_comm] using add_le_add_right hkN (wend k * Mend k)
  exact hagg.trans hsum

end RobinBV.Sieve
