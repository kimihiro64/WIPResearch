/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import RobinBV.Mathlib.Analysis.Fourier.ExponentialMean

/-!
# Exact covariances of absolutely convergent exponential series

Continuous and logarithmic floor means retain every matching-frequency pair.
Neither distinctness nor linear independence of the frequencies is assumed.
-/

namespace Complex

open Filter

noncomputable section

private theorem exponential_atom_mul_star (x y t : Real) (c d : Complex) :
    (c * exp ((x : Complex)*Complex.I*(t : Complex))) *
      star (d * exp ((y : Complex)*Complex.I*(t : Complex))) =
    (c * star d) * exp (((x-y : Real) : Complex)*Complex.I*(t : Complex)) := by
  rw [star_mul, mul_comm (star (exp _)) (star d)]
  simp only [star_def, <- exp_conj, map_mul, conj_ofReal, conj_I]
  rw [show c * exp ((x : Complex)*Complex.I*(t : Complex)) *
      ((starRingEnd Complex) d * exp ((y : Complex)*(-I)*(t : Complex))) =
      (c*(starRingEnd Complex) d) *
        (exp ((x : Complex)*Complex.I*(t : Complex)) * exp ((y : Complex)*(-I)*(t : Complex))) by ring]
  rw [<- exp_add]
  congr 2
  push_cast
  ring

/-- The full coefficient product family is absolutely summable. -/
theorem summable_norm_exponentialCovariance {I J : Type*}
    (c : I -> Complex) (d : J -> Complex)
    (hC : Summable (fun i => norm (c i))) (hD : Summable (fun j => norm (d j))) :
    Summable (fun p : Prod I J => norm (c p.1 * star (d p.2))) := by
  have hProduct : Summable (fun p : Prod I J => norm (c p.1) * norm (d p.2)) :=
    hC.mul_of_nonneg hD (fun i => norm_nonneg (c i)) (fun j => norm_nonneg (d j))
  apply hProduct.congr
  intro p
  rw [norm_mul, norm_star]

/-- Exact complete conjugate-product expansion, with every frequency difference. -/
theorem exponentialSeries_mul_star_eq {I J : Type*}
    (c : I -> Complex) (omega : I -> Real) (d : J -> Complex) (nu : J -> Real)
    (hC : Summable (fun i => norm (c i))) (hD : Summable (fun j => norm (d j))) (t : Real) :
    exponentialSeries c omega t * star (exponentialSeries d nu t) =
      exponentialSeries (fun p : Prod I J => c p.1 * star (d p.2))
        (fun p : Prod I J => omega p.1 - nu p.2) t := by
  have hNormC : Summable (fun i => norm (c i * exp ((omega i : Complex)*Complex.I*(t : Complex)))) := by
    simpa only [norm_mul, norm_exp, mul_re, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, sub_zero, zero_mul, add_zero, zero_sub, Real.exp_zero, mul_one] using hC
  have hNormD : Summable (fun j => norm (star (d j * exp ((nu j : Complex)*Complex.I*(t : Complex))))) := by
    simpa only [norm_star, norm_mul, norm_exp, mul_re, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, sub_zero, zero_mul, add_zero, zero_sub, Real.exp_zero, mul_one] using hD
  unfold exponentialSeries
  rw [tsum_star, tsum_mul_tsum_of_summable_norm hNormC hNormD]
  exact tsum_congr (fun p => exponential_atom_mul_star (omega p.1) (nu p.2) t (c p.1) (d p.2))

/-- Exact continuous covariance limit, including every frequency collision. -/
theorem tendsto_exponentialSeries_covarianceMean {I J : Type*} [Countable I] [Countable J]
    (c : I -> Complex) (omega : I -> Real) (d : J -> Complex) (nu : J -> Real)
    (hC : Summable (fun i => norm (c i))) (hD : Summable (fun j => norm (d j))) :
    Tendsto (intervalMean (fun t => exponentialSeries c omega t * star (exponentialSeries d nu t)))
      atTop (nhds (tsum (fun p : Prod I J =>
        if omega p.1 = nu p.2 then c p.1 * star (d p.2) else 0))) := by
  classical
  have h := tendsto_exponentialSeriesMean
    (fun p : Prod I J => c p.1 * star (d p.2)) (fun p : Prod I J => omega p.1 - nu p.2)
    (summable_norm_exponentialCovariance c d hC hD)
  change Tendsto (intervalMean (exponentialSeries
    (fun p : Prod I J => c p.1 * star (d p.2)) (fun p : Prod I J => omega p.1 - nu p.2)))
    atTop (nhds _) at h
  have hFunction : exponentialSeries (fun p : Prod I J => c p.1 * star (d p.2))
      (fun p : Prod I J => omega p.1 - nu p.2) =
      (fun t => exponentialSeries c omega t * star (exponentialSeries d nu t)) := by
    funext t
    exact (exponentialSeries_mul_star_eq c omega d nu hC hD t).symm
  simpa only [hFunction, sub_eq_zero] using h

/-- The same full covariance is preserved by logarithmic floor sampling. -/
theorem tendsto_exponentialSeries_covarianceLogFloorMean {I J : Type*}
    [Countable I] [Countable J]
    (c : I -> Complex) (omega : I -> Real) (d : J -> Complex) (nu : J -> Real)
    (hC : Summable (fun i => norm (c i))) (hD : Summable (fun j => norm (d j))) :
    Tendsto (intervalMean (fun t =>
      exponentialSeries c omega (Real.log (Nat.floor (Real.exp t) : Real)) *
        star (exponentialSeries d nu (Real.log (Nat.floor (Real.exp t) : Real)))))
      atTop (nhds (tsum (fun p : Prod I J =>
        if omega p.1 = nu p.2 then c p.1 * star (d p.2) else 0))) := by
  classical
  have h := tendsto_exponentialSeries_logFloorMean
    (fun p : Prod I J => c p.1 * star (d p.2)) (fun p : Prod I J => omega p.1 - nu p.2)
    (summable_norm_exponentialCovariance c d hC hD)
  simpa only [<- exponentialSeries_mul_star_eq c omega d nu hC hD, sub_eq_zero] using h

/-- Exact logarithmic-clock representation of critical-line power phases. -/
theorem exponentialSeries_eq_criticalLinePowerSum {I : Type*}
    (rho c : I -> Complex) (hRe : forall i, (rho i).re=(1/2 : Real))
    (k m : Nat) {x : Real} (hx : 0 < x) :
    exponentialSeries c (fun i => (m : Real)*(rho i).im/(k : Real)) (Real.log x) =
      tsum (fun i => c i * (((x^m : Real) : Complex)^((rho i-1/2)/(k : Complex)))) := by
  unfold exponentialSeries
  apply tsum_congr
  intro i
  congr 1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (pow_pos hx m).ne'),
    <- Complex.ofReal_log (pow_pos hx m).le, Real.log_pow]
  congr 1
  have hRho : rho i-(1/2 : Complex)=((rho i).im : Complex)*Complex.I := by
    apply Complex.ext
    next => simp [hRe i]
    next => simp
  rw [hRho]
  push_cast
  ring

/-- Full critical-line power series is bounded by the complete coefficient mass. -/
theorem norm_criticalLinePowerSum_le {I : Type*}
    (rho c : I -> Complex) (hRe : forall i, (rho i).re=(1/2 : Real))
    (hC : Summable (fun i => norm (c i))) (k m : Nat) {x : Real} (hx : 0 < x) :
    norm (tsum (fun i => c i * (((x^m : Real) : Complex)^((rho i-1/2)/(k : Complex))))) <=
      tsum (fun i => norm (c i)) := by
  rw [<- exponentialSeries_eq_criticalLinePowerSum rho c hRe k m hx]
  exact norm_exponentialSeries_le c _ hC _

/-- Complete critical-line mean square, with all equal-point cross terms retained. -/
theorem tendsto_criticalLinePowerSum_secondMoment {I : Type*} [Countable I]
    (rho c : I -> Complex) (hRe : forall i, (rho i).re=(1/2 : Real))
    (hC : Summable (fun i => norm (c i))) {k m : Nat} (hk : 1 <= k) (hm : 1 <= m) :
    Tendsto (intervalMean (fun t : Real =>
      (tsum (fun i => c i * ((((Nat.floor (Real.exp t) : Real)^m : Real) : Complex)^
        ((rho i-1/2)/(k : Complex))))) *
      star (tsum (fun i => c i * ((((Nat.floor (Real.exp t) : Real)^m : Real) : Complex)^
        ((rho i-1/2)/(k : Complex))))))) atTop
      (nhds (tsum (fun p : Prod I I => if rho p.1 = rho p.2 then c p.1 * star (c p.2) else 0))) := by
  classical
  let omega : I -> Real := fun i => (m : Real)*(rho i).im/(k : Real)
  have hkR : Not ((k : Real)=0) := by exact_mod_cast (by omega : Not (k=0))
  have hmR : Not ((m : Real)=0) := by exact_mod_cast (by omega : Not (m=0))
  have hFrequency (i j : I) : omega i=omega j <-> rho i=rho j := by
    constructor
    next =>
      intro h
      have hIm : (rho i).im=(rho j).im := by
        calc
          _ = omega i * ((k : Real)/(m : Real)) := by
            dsimp only [omega]
            field_simp [hkR, hmR]
          _ = omega j * ((k : Real)/(m : Real)) := by rw [h]
          _ = _ := by
            dsimp only [omega]
            field_simp [hkR, hmR]
      apply Complex.ext
      next => rw [hRe i, hRe j]
      next => exact hIm
    next =>
      intro h
      simp only [omega, h]
  have h := tendsto_exponentialSeries_covarianceLogFloorMean c omega c omega hC hC
  simp only [hFrequency] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with T hT
  unfold intervalMean
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have htI : Membership.mem (Set.Icc (0 : Real) T) t := by
    simpa only [Set.uIcc_of_le hT.le] using ht
  have hP : (0 : Real) < (Nat.floor (Real.exp t) : Real) := by
    exact_mod_cast (Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr htI.1))
  dsimp only [omega]
  rw [exponentialSeries_eq_criticalLinePowerSum rho c hRe k m hP]

/-- Full quadratic perturbation bound, retaining both cross terms. -/
theorem norm_mul_star_self_sub_le (z w : Complex) :
    norm (z*star z-w*star w) <= norm (z-w)*(norm (z-w)+2*norm w) := by
  have hIdentity : z*star z-w*star w =
      (z-w)*star (z-w)+(z-w)*star w+w*star (z-w) := by
    simp only [star_sub]
    ring
  rw [hIdentity]
  have h := (norm_add_le ((z-w)*star (z-w)+(z-w)*star w) (w*star (z-w))).trans
    (add_le_add (norm_add_le ((z-w)*star (z-w)) ((z-w)*star w)) le_rfl)
  simp only [norm_mul, norm_star] at h
  exact h.trans_eq (by ring)

/-- A vanishing additive error preserves second moments pointwise
whenever the comparison sequence is eventually bounded. -/
theorem tendsto_mul_star_self_sub_of_tendsto_sub {A : Type*} {l : Filter A}
    (u v : A -> Complex) {C : Real}
    (hError : Tendsto (fun a => u a-v a) l (nhds (0 : Complex)))
    (hBound : Filter.Eventually (fun a => norm (v a) <= C) l) :
    Tendsto (fun a => u a*star (u a)-v a*star (v a)) l (nhds (0 : Complex)) := by
  have hNorm := hError.norm
  simp only [norm_zero] at hNorm
  have hMajor : Tendsto (fun a => norm (u a-v a)*(norm (u a-v a)+2*C)) l (nhds (0 : Real)) := by
    simpa only [zero_mul] using hNorm.mul (hNorm.add_const (2*C))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => norm_nonneg _)) _ hMajor
  filter_upwards [hBound] with a ha
  apply (norm_mul_star_self_sub_le (u a) (v a)).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  linarith

end

end Complex
