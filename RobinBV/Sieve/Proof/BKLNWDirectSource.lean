/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import PrimeNumberTheoremAnd.IEANTN.PrimaryDefinitions
import PrimeNumberTheoremAnd.IEANTN.ZetaSummary

/-!
# Direct Appendix A consumers

These are the source-level A.12 aggregation and A.13 exponential-normalizing
consumers.  They retain the explicit zero-density hypotheses and are kept
separate from the dependency package's application declarations.
-/

set_option autoImplicit false

open Real Chebyshev

theorem bklnw_a12_finite_band_aggregation
    {K : Nat} (f : Nat -> Complex) (u : Nat -> Real)
    (hband : forall k, k < K -> norm (f k) <= u k) :
    norm (Finset.sum (Finset.range K) f) <=
      Finset.sum (Finset.range K) u := by
  calc
    norm (Finset.sum (Finset.range K) f) <=
        Finset.sum (Finset.range K) (fun k => norm (f k)) := by
      exact norm_sum_le (Finset.range K) f
    _ <= Finset.sum (Finset.range K) u := by
      exact Finset.sum_le_sum (fun k hk =>
        hband k (Finset.mem_range.mp hk))

structure DirectInputs where
  H : Real
  R : Real
  ZDB : zero_density_bound

def zdT0 : zero_density_bound -> Real
  | zero_density_bound.mk t s c1 c2 p q b => t

def zdRange : zero_density_bound -> Set Real
  | zero_density_bound.mk t s c1 c2 p q b => s

noncomputable def DirectSigma2 (x T delta : Real) : Complex :=
  riemannZeta.zeroes_sum (Set.Icc (1 - delta) 1)
    (Set.Ioo (-T) T) (fun rho => x ^ (rho - 1) / rho)

theorem bklnw_direct_A12_from_band_packets
    (x T delta : Real) {K : Nat}
    (packet : Nat -> Complex) (bound : Nat -> Real)
    (hdecomp : DirectSigma2 x T delta =
      Finset.sum (Finset.range K) packet)
    (hband : forall k, k < K -> norm (packet k) <= bound k) :
    norm (DirectSigma2 x T delta) <=
      Finset.sum (Finset.range K) bound := by
  rw [hdecomp]
  exact bklnw_a12_finite_band_aggregation packet bound hband

theorem bklnw_direct_A13
    (I : DirectInputs) (hA12 :
      forall (x T delta lambda : Real), 1 < lambda -> 1 < x -> 0 < T ->
        I.H < T -> Membership.mem (zdRange I.ZDB) (1 - delta) ->
        zdT0 I.ZDB <= I.H ->
        let K := Nat.floor (Real.log (T / I.H) / Real.log lambda) + 1
        norm (DirectSigma2 x T delta) <=
          2 * Finset.sum (Finset.range K) (fun k =>
            (lambda ^ (k + 1) *
              x ^ (-(1 / (I.R * Real.log (T / lambda ^ k)))) / T) *
              I.ZDB.N (1 - delta) (T / lambda ^ k)))
    (x T delta lambda : Real) (hlambda : 1 < lambda)
    (hx : 1 < x) (hT : 0 < T) (hTH : I.H < T)
    (hSigma : Membership.mem (zdRange I.ZDB) (1 - delta))
    (hT0 : zdT0 I.ZDB <= I.H) :
    let K := Nat.floor (Real.log (T / I.H) / Real.log lambda) + 1
    norm (DirectSigma2 x T delta) <= (2 * lambda / T) *
      Finset.sum (Finset.range K) (fun k =>
        Real.exp ((k : Real) * Real.log lambda -
          (Real.log x) /
            (I.R * (Real.log T - (k : Real) * Real.log lambda))) *
          I.ZDB.N (1 - delta) (T / lambda ^ k)) := by
  have hA := hA12 x T delta lambda hlambda hx hT hTH hSigma hT0
  dsimp at hA
  dsimp
  refine hA.trans (le_of_eq ?_)
  have h4 (k : Nat) :
      Real.exp ((k : Real) * Real.log lambda - (Real.log x) /
        (I.R * (Real.log T - (k : Real) * Real.log lambda))) =
      lambda ^ k * x ^ (-(1 / (I.R * Real.log (T / lambda ^ k)))) := by
    rw [Real.log_div hT.ne' (by positivity), Real.log_pow,
      sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul,
      Real.exp_log (by positivity), Real.rpow_def_of_pos (by positivity),
      mul_neg, mul_one_div]
  simp_rw [Finset.mul_sum, h4]
  congr 1
  ext k
  ring

theorem fks_second_density_bound_from_first
    (N T H d U C : Real)
    (hT : 1 <= T) (hH : 0 <= H) (hHT : H < T)
    (hd : 0 < d) (hU : 0 <= U) (hC : 0 <= C)
    (hfirst : N <=
      ((T - H) * Real.log T) / (2 * Real.pi * d) *
          Real.log (1 + U / (T - H)) +
        C * (Real.log T)^2 / (2 * Real.pi * d)) :
    N <= U * Real.log T / (2 * Real.pi * d) +
      C * (Real.log T)^2 / (2 * Real.pi * d) := by
  have hTH : 0 < T - H := sub_pos.mpr hHT
  have hlogT : 0 <= Real.log T := Real.log_nonneg hT
  have harg : 0 < 1 + U / (T - H) := by
    have hquot : 0 <= U / (T - H) := div_nonneg hU hTH.le
    linarith
  have hlog : Real.log (1 + U / (T - H)) <= U / (T - H) := by
    have hraw := Real.log_le_sub_one_of_pos harg
    linarith
  have hcoeff : 0 <= ((T - H) * Real.log T) /
      (2 * Real.pi * d) := by
    positivity
  have hmain :
      ((T - H) * Real.log T) / (2 * Real.pi * d) *
          Real.log (1 + U / (T - H)) <=
        U * Real.log T / (2 * Real.pi * d) := by
    calc
      ((T - H) * Real.log T) / (2 * Real.pi * d) *
          Real.log (1 + U / (T - H)) <=
          ((T - H) * Real.log T) / (2 * Real.pi * d) *
            (U / (T - H)) :=
        mul_le_mul_of_nonneg_left hlog hcoeff
      _ = U * Real.log T / (2 * Real.pi * d) := by
        field_simp [ne_of_gt hTH, ne_of_gt hd, ne_of_gt Real.pi_pos]
  linarith

theorem fks_table_power_endpoint
    (T sigmaLow sigma : Real)
    (hT : 1 <= T) (hsigma : sigmaLow <= sigma) :
    T ^ ((8 / 3 : Real) * (1 - sigma)) <=
      T ^ ((8 / 3 : Real) * (1 - sigmaLow)) := by
  apply Real.rpow_le_rpow_of_exponent_le hT
  nlinarith

theorem fks_table_log_power_endpoint
    (T sigmaLow sigma : Real)
    (hT : 1 < Real.log T) (hsigma : sigmaLow <= sigma) :
    (Real.log T) ^ (5 - 2 * sigma) <=
      (Real.log T) ^ (5 - 2 * sigmaLow) := by
  apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hT)
  nlinarith

theorem fks_table_density_term_endpoint
    (T sigmaLow sigma c1 c2 : Real)
    (hT : 1 <= T) (hlogT : 1 < Real.log T)
    (hsigma : sigmaLow <= sigma)
    (hc1 : 0 <= c1) (hc2 : 0 <= c2) :
    c1 * T ^ ((8 / 3 : Real) * (1 - sigma)) *
        (Real.log T) ^ (5 - 2 * sigma) + c2 * (Real.log T)^2 <=
      c1 * T ^ ((8 / 3 : Real) * (1 - sigmaLow)) *
        (Real.log T) ^ (5 - 2 * sigmaLow) + c2 * (Real.log T)^2 := by
  have hpow := fks_table_power_endpoint T sigmaLow sigma hT hsigma
  have hlog := fks_table_log_power_endpoint T sigmaLow sigma hlogT hsigma
  have hTpow : 0 <= T ^ ((8 / 3 : Real) * (1 - sigma)) := by
    positivity
  have hTpowLow : 0 <= T ^ ((8 / 3 : Real) * (1 - sigmaLow)) := by
    positivity
  have hlogpow : 0 <= (Real.log T) ^ (5 - 2 * sigma) := by
    positivity
  have hprod :
      T ^ ((8 / 3 : Real) * (1 - sigma)) *
          (Real.log T) ^ (5 - 2 * sigma) <=
        T ^ ((8 / 3 : Real) * (1 - sigmaLow)) *
          (Real.log T) ^ (5 - 2 * sigmaLow) := by
    exact mul_le_mul hpow hlog hlogpow hTpowLow
  have hcprod := mul_le_mul_of_nonneg_left hprod hc1
  linarith

theorem finite_two_detector_count_from_moments
    {alpha : Type*} (S : Finset alpha)
    (f g : alpha -> Complex) (L MF MG : Real)
    (hL : 0 < L)
    (hcover : forall z, Membership.mem S z ->
      L <= norm (f z) \/ L <= norm (g z))
    (hF : S.sum (fun z => norm (f z)^2) <= MF)
    (hG : S.sum (fun z => norm (g z)^2) <= MG) :
    (S.card : Real) <= (MF + MG) / L^2 := by
  have hpoint : forall z, Membership.mem S z ->
      L^2 <= norm (f z)^2 + norm (g z)^2 := by
    intro z hz
    rcases hcover z hz with hf | hg
    next =>
      have hsq : L^2 <= norm (f z)^2 := by
        nlinarith [sq_nonneg (L - norm (f z))]
      nlinarith [sq_nonneg (norm (g z))]
    next =>
      have hsq : L^2 <= norm (g z)^2 := by
        nlinarith [sq_nonneg (L - norm (g z))]
      nlinarith [sq_nonneg (norm (f z))]
  have hsum : S.sum (fun _ => L^2) <=
      S.sum (fun z => norm (f z)^2 + norm (g z)^2) := by
    exact Finset.sum_le_sum (fun z hz => hpoint z hz)
  have hleft : (S.card : Real) * L^2 <= MF + MG := by
    calc
      (S.card : Real) * L^2 = S.sum (fun _ => L^2) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ <= S.sum (fun z => norm (f z)^2 + norm (g z)^2) := hsum
      _ = S.sum (fun z => norm (f z)^2) +
          S.sum (fun z => norm (g z)^2) := by
        rw [Finset.sum_add_distrib]
      _ <= MF + MG := add_le_add hF hG
  have hLsq : 0 < L^2 := sq_pos_of_pos hL
  apply le_of_mul_le_mul_right _ hLsq
  have hcancel : (MF + MG) / L^2 * L^2 = MF + MG := by
    field_simp [ne_of_gt hLsq]
  rw [hcancel]
  exact hleft
