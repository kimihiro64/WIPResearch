/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Sieve.Helpers.LogWindowTest
import Zeta23.WeilEF.ZeroSummability

/-!
# Summability for actual zeta square-window tests

The actual nontrivial-zero carrier is countable because its positive
inverse-square mass is summable. The scaled smooth tests satisfy the
hypotheses of the pinned zeta explicit-formula summability theorem;
restricting to real part at most one half preserves summability.
No zero-density hypothesis or finite height cutoff is assumed here.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem zeta_zero_carrier_countable : Countable Zeta23.zetaZeroConfig.carrier := by
  have hs : Summable (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zeroMult (rho : Complex) : Real)/
        (1+Complex.normSq (Zeta23.gammaOf (rho : Complex)))) :=
    Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam
  have hpos (rho : Zeta23.zetaZeroConfig.carrier) :
      0 < (Zeta23.zeroMult (rho : Complex) : Real)/
        (1+Complex.normSq (Zeta23.gammaOf (rho : Complex))) := by
    have hm1 : 1 <= Zeta23.zeroMult (rho : Complex) :=
      Zeta23.zetaZeroConfig.one_le_mult (rho : Complex) rho.property
    have hm0 : (0 : Real) < (Zeta23.zeroMult (rho : Complex) : Real) := by
      exact_mod_cast (show 0 < Zeta23.zeroMult (rho : Complex) by omega)
    exact _root_.div_pos hm0 (by linarith [Complex.normSq_nonneg (Zeta23.gammaOf (rho : Complex))])
  have hsupport : Function.support (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zeroMult (rho : Complex) : Real)/
        (1+Complex.normSq (Zeta23.gammaOf (rho : Complex)))) = Set.univ := by
    ext rho
    constructor
    next =>
      intro _
      trivial
    next =>
      intro _
      exact ne_of_gt (hpos rho)
  have hc := hs.countable_support
  rw [hsupport] at hc
  exact Set.countable_univ_iff.mp hc

theorem scaledLogWindowTest_left_zero_summable {eta L : Real}
    (he : 0 < eta) (hL : 0 < L) (c : Real) :
    Summable (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if (rho : Complex).re <= 1/2
      then (Zeta23.zeroMult (rho : Complex) : Complex)*
        Zeta23.paperFT (scaledLogWindowTest eta L c) (Zeta23.gammaOf (rho : Complex))
      else 0) := by
  classical
  have hfull : Summable (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zeroMult (rho : Complex) : Complex)*
        Zeta23.paperFT (scaledLogWindowTest eta L c) (Zeta23.gammaOf (rho : Complex))) :=
    Zeta23.WeilEF.EF_zero_sum_summable Zeta23.zetaSeam
      (scaledLogWindowTest_contDiff eta L c) (scaledLogWindowTest_hasCompactSupport he hL c)
  exact hfull.indicator (fun rho : Zeta23.zetaZeroConfig.carrier => (rho : Complex).re <= 1/2)

end RobinBV.Sieve
