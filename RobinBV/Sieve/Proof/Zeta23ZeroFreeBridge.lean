/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.ZeroFreeBandBound
import Zeta23.FromPNTPlus.ZetaBounds
import Zeta23.Statement

/-!
# Explicit zeta zero-free bridge

This module converts the pinned Zeta23 zero-free theorem into the real-part
inequality used by the high-real-part corridor estimates.
-/

set_option autoImplicit false

theorem zeta23_zero_re_lt_log9
    {rho : Complex} (hzero : Zeta23.IsNontrivialZero rho)
    (him : 3 < abs rho.im) :
    exists A : Real, 0 < A /\ A <= (1/2 : Real) /\
      rho.re < 1-A/(Real.log (abs rho.im))^9 := by
  cases ZetaZeroFree with
  | intro A hrest =>
    cases hrest with
    | intro hA hfree =>
      refine Exists.intro A (And.intro hA.1 (And.intro hA.2 ?_))
      by_contra hnot
      have hge : 1-A/(Real.log (abs rho.im))^9 <= rho.re :=
        le_of_not_gt hnot
      have hne := hfree rho.re rho.im him (And.intro hge hzero.2.2)
      have hrepr : rho = (rho.re : Complex) + (rho.im : Complex)*Complex.I := by
        apply Complex.ext <;> simp <;> ring
      rw [hrepr] at hzero
      exact hne hzero.1

theorem zeta23_zero_re_lt_log9_common :
    exists A : Real, 0 < A /\ A <= (1/2 : Real) /\
      forall rho, Zeta23.IsNontrivialZero rho -> 3 < abs rho.im ->
        rho.re < 1-A/(Real.log (abs rho.im))^9 := by
  cases ZetaZeroFree with
  | intro A hrest =>
    cases hrest with
    | intro hA hfree =>
      refine Exists.intro A
        (And.intro hA.1 (And.intro hA.2 ?_))
      intro rho hzero him
      by_contra hnot
      have hge : 1-A/(Real.log (abs rho.im))^9 <= rho.re :=
        le_of_not_gt hnot
      have hne := hfree rho.re rho.im him
        (And.intro hge hzero.2.2)
      have hrepr : rho = (rho.re : Complex) +
          (rho.im : Complex)*Complex.I := by
        apply Complex.ext <;> simp <;> ring
      rw [hrepr] at hzero
      exact hne hzero.1

theorem zeta23_zero_cpow_div_log9_common {x : Real} (hx : 1 < x) :
    exists A : Real, 0 < A /\ A <= (1/2 : Real) /\
      forall rho, Zeta23.IsNontrivialZero rho -> 3 < abs rho.im ->
        norm (((x : Complex) ^ (rho - 1)) / rho) <=
          x ^ (-(A / (Real.log (abs rho.im))^9)) / abs rho.im := by
  obtain hA := zeta23_zero_re_lt_log9_common
  let A : Real := hA.choose
  have hApos : 0 < A := by exact hA.choose_spec.1
  have hAhalf : A <= (1/2 : Real) := by exact hA.choose_spec.2.1
  refine Exists.intro A (And.intro hApos (And.intro hAhalf ?_))
  intro rho hzero him
  let y : Real := abs rho.im
  let R : Real := (Real.log y)^8 / A
  have hy : 1 < y := by
    dsimp [y]
    linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hR : 0 < R := by
    dsimp [R]
    exact div_pos (pow_pos hlog 8) hApos
  have hidentity : 1 / (R * Real.log y) = A / (Real.log y)^9 := by
    dsimp [R]
    field_simp
  have hRe0 : rho.re <= 1-A/(Real.log y)^9 := by
    have hstrict := hA.choose_spec.2.2 rho hzero him
    exact le_of_lt (by simpa only [y] using hstrict)
  have hre : rho.re <= 1 - 1 / (R * Real.log y) := by
    rw [hidentity]
    exact hRe0
  have hgeom : y <= norm rho := by
    exact Complex.abs_im_le_norm rho
  have hbound := Complex.norm_cpow_div_zero_free_bound
    hx hy hgeom hR hre
  rw [hidentity] at hbound
  simpa only [y] using hbound

theorem zeta23_zero_cpow_div_log9_sum {x : Real} (hx : 1 < x) :
    exists A : Real, 0 < A /\ A <= (1/2 : Real) /\
      forall S : Finset Complex,
      (forall rho, Membership.mem S rho -> Zeta23.IsNontrivialZero rho) ->
      (forall rho, Membership.mem S rho -> 3 < abs rho.im) ->
      norm (Finset.sum S (fun rho =>
        ((x : Complex) ^ (rho - 1) / rho) *
          (Zeta23.zeroMult rho : Complex))) <=
        Finset.sum S (fun rho =>
          (x ^ (-(A / (Real.log (abs rho.im))^9)) / abs rho.im) *
            (Zeta23.zeroMult rho : Real)) := by
  obtain hA := zeta23_zero_cpow_div_log9_common hx
  let A : Real := hA.choose
  have hApos : 0 < A := by exact hA.choose_spec.1
  have hAhalf : A <= (1/2 : Real) := by exact hA.choose_spec.2.1
  refine Exists.intro A (And.intro hApos (And.intro hAhalf ?_))
  intro S hS hheight
  have hpoint (rho : Complex) (hrho : Membership.mem S rho) :
      norm (((x : Complex) ^ (rho - 1) / rho) *
        (Zeta23.zeroMult rho : Complex)) <=
        (x ^ (-(A / (Real.log (abs rho.im))^9)) / abs rho.im) *
          (Zeta23.zeroMult rho : Real) := by
    have hpow := hA.choose_spec.2.2 rho (hS rho hrho) (hheight rho hrho)
    rw [norm_mul]
    have hm : norm (Zeta23.zeroMult rho : Complex) =
        (Zeta23.zeroMult rho : Real) := by simp
    rw [hm]
    exact mul_le_mul_of_nonneg_right hpow (by positivity)
  calc
    norm (Finset.sum S (fun rho =>
        ((x : Complex) ^ (rho - 1) / rho) *
          (Zeta23.zeroMult rho : Complex))) <=
      Finset.sum S (fun rho => norm (((x : Complex) ^ (rho - 1) / rho) *
        (Zeta23.zeroMult rho : Complex))) := by
      exact norm_sum_le S (fun rho =>
        ((x : Complex) ^ (rho - 1) / rho) *
          (Zeta23.zeroMult rho : Complex))
    _ <= Finset.sum S (fun rho =>
        (x ^ (-(A / (Real.log (abs rho.im))^9)) / abs rho.im) *
          (Zeta23.zeroMult rho : Real)) := by
      exact Finset.sum_le_sum (fun rho hrho => hpoint rho hrho)

theorem zeta23_zero_free_band_weight_monotone
    {x A L U y : Real} (hx : 1 < x) (hA : 0 < A)
    (hL : 1 < L) (hLU : L <= y) (hyU : y <= U) :
    x ^ (-(A / (Real.log y)^9)) / y <=
      x ^ (-(A / (Real.log U)^9)) / L := by
  have hy : 1 < y := lt_of_lt_of_le hL hLU
  have hU : 1 < U := lt_of_lt_of_le hy hyU
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hlogle : Real.log y <= Real.log U :=
    Real.log_le_log (by linarith) hyU
  have hpow : (Real.log y)^9 <= (Real.log U)^9 := by
    gcongr
  have hfrac : A / (Real.log U)^9 <= A / (Real.log y)^9 := by
    have hinv := one_div_le_one_div_of_le (pow_pos hlogy 9) hpow
    have hinv' : Inv.inv (Real.log U ^ 9) <= Inv.inv (Real.log y ^ 9) := by
      simpa [one_div] using hinv
    exact mul_le_mul_of_nonneg_left hinv' hA.le
  have hexp : -(A / (Real.log y)^9) <=
      -(A / (Real.log U)^9) := by linarith
  have hpowx := Real.rpow_le_rpow_of_exponent_le hx.le hexp
  have hinv : 1 / y <= 1 / L :=
    one_div_le_one_div_of_le (by linarith) hLU
  have hnonneg : 0 <= x ^ (-(A / (Real.log y)^9)) :=
    Real.rpow_nonneg (by linarith) _
  calc
    x ^ (-(A / (Real.log y)^9)) / y =
        x ^ (-(A / (Real.log y)^9)) * (1 / y) := by ring
    _ <= x ^ (-(A / (Real.log y)^9)) * (1 / L) :=
      mul_le_mul_of_nonneg_left hinv hnonneg
    _ <= x ^ (-(A / (Real.log U)^9)) * (1 / L) :=
      mul_le_mul_of_nonneg_right hpowx (by positivity)
    _ = x ^ (-(A / (Real.log U)^9)) / L := by ring

theorem zeta23_zero_re_le_log9
    {rho : Complex} (hzero : Zeta23.IsNontrivialZero rho)
    (him : 3 < abs rho.im) :
    exists A : Real, 0 < A /\ A <= (1/2 : Real) /\
      rho.re <= 1-A/(Real.log (abs rho.im))^9 := by
  obtain h := zeta23_zero_re_lt_log9 hzero him
  exact Exists.intro h.choose
    (And.intro h.choose_spec.1
      (And.intro h.choose_spec.2.1 (le_of_lt h.choose_spec.2.2)))

theorem zeta23_zero_cpow_div_log9
    {rho : Complex} (hzero : Zeta23.IsNontrivialZero rho)
    (him : 3 < abs rho.im) {x : Real} (hx : 1 < x) :
    exists A : Real, 0 < A /\ A <= (1/2 : Real) /\
      norm (((x : Complex) ^ (rho - 1)) / rho) <=
        x ^ (-(A / (Real.log (abs rho.im))^9)) / abs rho.im := by
  obtain hA := zeta23_zero_re_le_log9 hzero him
  let A : Real := hA.choose
  have hApos : 0 < A := by exact hA.choose_spec.1
  have hAhalf : A <= (1/2 : Real) := by exact hA.choose_spec.2.1
  have hRe0 : rho.re <= 1-A/(Real.log (abs rho.im))^9 := by
    exact hA.choose_spec.2.2
  refine Exists.intro A (And.intro hApos (And.intro hAhalf ?_))
  let y : Real := abs rho.im
  let R : Real := (Real.log y)^8 / A
  have hy : 1 < y := by
    dsimp [y]
    linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hR : 0 < R := by
    dsimp [R]
    exact div_pos (pow_pos hlog 8) hApos
  have hidentity : 1 / (R * Real.log y) = A / (Real.log y)^9 := by
    dsimp [R]
    field_simp
  have hre : rho.re <= 1 - 1 / (R * Real.log y) := by
    have hraw : rho.re <= 1-A/(Real.log y)^9 := by
      simpa only [y] using hRe0
    rw [hidentity]
    exact hraw
  have hgeom : y <= norm rho := by
    exact Complex.abs_im_le_norm rho
  have hbound := Complex.norm_cpow_div_zero_free_bound
    hx hy hgeom hR hre
  rw [hidentity] at hbound
  simpa only [y] using hbound
