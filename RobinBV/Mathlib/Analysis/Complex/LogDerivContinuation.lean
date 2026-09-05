/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order

/-!
# Holomorphic continuation of a logarithmic derivative excludes zeros

A finite-order zero has a genuine simple logarithmic-derivative pole.
On an open connected domain, a holomorphic continuation therefore forces
nonvanishing, provided the original analytic function is not identically zero.
The identity theorem is applied to f' = g*f, so no quotient is evaluated
as an analytic expression at a possible zero.
-/

set_option autoImplicit false

namespace Complex

open Filter Set

/-- A local holomorphic extension of the logarithmic derivative is incompatible
with a finite-order zero of the analytic function. -/
theorem ne_zero_of_analytic_logDeriv_continuation
    {f g : Complex -> Complex} {z : Complex}
    (hf : AnalyticAt Complex f z) (hg : AnalyticAt Complex g z)
    (hFinite : Not (meromorphicOrderAt f z = Top.top))
    (hEq : EventuallyEq (nhdsWithin z (Set.compl {z})) (logDeriv f) g) :
    Not (f z = 0) := by
  intro hZero
  have hLimit : Tendsto f (nhdsWithin z (Set.compl {z})) (nhds 0) := by
    simpa only [hZero] using hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hPos := (tendsto_zero_iff_meromorphicOrderAt_pos hf.meromorphicAt).1 hLimit
  have hPole := meromorphicOrderAt_logDeriv_eq_neg_one hf.meromorphicAt
    (ne_of_gt hPos) hFinite
  have hOrderEq := meromorphicOrderAt_congr hEq
  have hNonneg := hg.meromorphicOrderAt_nonneg
  rw [<- hOrderEq, hPole] at hNonneg
  have hNeg : (-1 : WithTop Int) < 0 := WithTop.coe_lt_coe.mpr (by norm_num)
  exact (not_le_of_gt hNeg) hNonneg

/-- An analytic solution of f'=g*f on an open connected domain is either
identically zero or nowhere zero. The proof uses finite analytic order. -/
theorem apply_ne_zero_of_deriv_eq_mul
    {f g : Complex -> Complex} {U : Set Complex}
    (hf : AnalyticOnNhd Complex f U) (hg : AnalyticOnNhd Complex g U)
    (hOpen : IsOpen U) (hConnected : IsPreconnected U)
    {z0 : Complex} (hz0 : Membership.mem U z0) (hStart : Not (f z0 = 0))
    (hODE : forall z : Complex, Membership.mem U z -> deriv f z = g z * f z)
    {z : Complex} (hz : Membership.mem U z) :
    Not (f z = 0) := by
  have hOrderStart : meromorphicOrderAt f z0 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hf z0 hz0).meromorphicAt).1
      (Exists.intro (f z0) (And.intro hStart
        ((hf z0 hz0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)))
  have hFinite : Not (meromorphicOrderAt f z = Top.top) :=
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      hConnected hz0 hz (by rw [hOrderStart]; simp)
  apply ne_zero_of_analytic_logDeriv_continuation (hf z hz) (hg z hz) hFinite
  have hNonzero := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (hf z hz).meromorphicAt).1 hFinite
  have hWithin : Filter.Eventually (fun y => Membership.mem U y) (nhds z) :=
    hOpen.mem_nhds hz
  filter_upwards [hNonzero, hWithin.filter_mono nhdsWithin_le_nhds] with y hy hyU
  rw [logDeriv_apply, hODE y hyU]
  field_simp [hy]

/-- An analytic continuation of logDeriv f from a neighborhood of one
nonzero point forces f to be nowhere zero on an open connected domain. -/
theorem apply_ne_zero_of_logDeriv_continuation
    {f g : Complex -> Complex} {U : Set Complex}
    (hf : AnalyticOnNhd Complex f U) (hg : AnalyticOnNhd Complex g U)
    (hOpen : IsOpen U) (hConnected : IsPreconnected U)
    {z0 : Complex} (hz0 : Membership.mem U z0) (hStart : Not (f z0 = 0))
    (hEq : EventuallyEq (nhds z0) (logDeriv f) g)
    {z : Complex} (hz : Membership.mem U z) :
    Not (f z = 0) := by
  have hNonzero : Filter.Eventually (fun y => Not (f y = 0)) (nhds z0) :=
    ((hf z0 hz0).continuousAt.ne_iff_eventually_ne continuousAt_const).1 hStart
  have hLocalODE : EventuallyEq (nhds z0) (deriv f) (fun y => g y * f y) := by
    filter_upwards [hEq, hNonzero] with y hy hyNe
    rw [logDeriv_apply] at hy
    calc
      deriv f y = (deriv f y / f y) * f y := by field_simp [hyNe]
      _ = g y * f y := by rw [hy]
  have hGlobalODE := hf.deriv.eqOn_of_preconnected_of_eventuallyEq
    (hg.mul hf) hConnected hz0 hLocalODE
  exact apply_ne_zero_of_deriv_eq_mul hf hg hOpen hConnected hz0 hStart hGlobalODE hz

end Complex
