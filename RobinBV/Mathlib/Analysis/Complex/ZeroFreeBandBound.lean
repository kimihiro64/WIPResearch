/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Zero-free complex-power band bounds

These lemmas are dependency-independent consumers for the zero-free part of a
finite height-band estimate. They retain the denominator height and do not
discard multiplicity weights.
-/

set_option autoImplicit false

namespace Complex

theorem norm_cpow_zero_free_bound
    {x y R : Real} {rho : Complex}
    (hx : 1 < x) (hy : 1 < y) (hR : 0 < R)
    (hre : rho.re <= 1 - 1 / (R * Real.log y)) :
    norm ((x : Complex) ^ (rho - 1)) <=
      x ^ (-(1 / (R * Real.log y))) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith) (rho - 1)]
  apply Real.rpow_le_rpow_of_exponent_le hx.le
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hden : 0 < R * Real.log y := mul_pos hR hlog
  change rho.re - 1 <= -(1 / (R * Real.log y))
  linarith

theorem norm_cpow_div_zero_free_bound
    {x y R : Real} {rho : Complex}
    (hx : 1 < x) (hy : 1 < y) (hgeom : y <= norm rho)
    (hR : 0 < R)
    (hre : rho.re <= 1 - 1 / (R * Real.log y)) :
    norm (((x : Complex) ^ (rho - 1)) / rho) <=
      x ^ (-(1 / (R * Real.log y))) / y := by
  rw [norm_div]
  have hpow := norm_cpow_zero_free_bound hx hy hR hre
  have hnonneg : 0 <= x ^ (-(1 / (R * Real.log y))) := by
    exact Real.rpow_nonneg (by linarith) _
  have hden : 0 < norm rho := lt_of_lt_of_le (by positivity) hgeom
  have h1 := div_le_div_of_nonneg_right hpow (le_of_lt hden)
  have h2 := div_le_div_of_nonneg_left hnonneg (by linarith) hgeom
  exact h1.trans h2

theorem norm_ge_of_pos_im
    {y : Real} {rho : Complex} (hy : 0 < y) (him : y < rho.im) :
    y <= norm rho := by
  have habs : y <= abs rho.im := by
    rw [abs_of_pos (lt_trans hy him)]
    exact le_of_lt him
  exact habs.trans (Complex.abs_im_le_norm rho)

theorem norm_ge_of_height_band
    {T lambda : Real} {k : Nat} {rho : Complex}
    (hT : 1 < T) (hlambda : 1 < lambda)
    (him : T / lambda ^ (k + 1) < rho.im) :
    T / lambda ^ (k + 1) <= norm rho := by
  apply norm_ge_of_pos_im
  next => positivity
  next => exact him

theorem norm_finite_band_sum_le
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

end Complex
