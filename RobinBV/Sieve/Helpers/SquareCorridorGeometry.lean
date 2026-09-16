/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Tactic.Positivity
import RobinBV.Sieve.Helpers.SquareIntervalMovingWidth

/-!
# Square-interval persistence geometry

Endpoint coordinates are controlled throughout a positive-length interval of
starting points. Contracted tests therefore remain inside the same original
open square interval; no sampling of a continuous moment at isolated squares
is used.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

/-- Endpoint coordinates for a whole positive-length persistence interval.
This is intended for the actual-P lower/upper corridor moment consumer. -/
theorem square_log_coordinates_persistence
    {n theta x : Real} (hn : 4 <= n)
    (ht0 : 0 < theta) (ht1 : theta <= 1)
    (hx0 : n^2 <= x) (hx1 : x <= n^2+theta*n/4) :
    -theta/4 <= (Real.log (n^2)-Real.log x)/movingSquareLogWidth x /\
    (Real.log (n^2)-Real.log x)/movingSquareLogWidth x <= 0 /\
    1-theta/2 <= (Real.log ((n+1)^2)-Real.log x)/movingSquareLogWidth x /\
    (Real.log ((n+1)^2)-Real.log x)/movingSquareLogWidth x <= 1 := by
  have log_sub_le_relative_gap {u v : Real}
      (hu : 0 < u) (hv : 0 < v) :
      Real.log v-Real.log u <= (v-u)/u := by
    have h := Real.log_le_sub_one_of_pos (div_pos hv hu)
    rw [Real.log_div hv.ne' hu.ne'] at h
    have he : v/u-1 = (v-u)/u := by field_simp
    rwa [he] at h
  have hn0 : 0 < n := by linarith
  have hn2 : 0 < n^2 := sq_pos_of_pos hn0
  have hx : 0 < x := hn2.trans_le hx0
  have hx2 : x <= 2*n^2 := by
    have ht := mul_le_mul_of_nonneg_right ht1 hn0.le
    nlinarith
  have hL := movingSquareLogWidth_dyadic_bounds
    (show 16 <= n^2 by nlinarith) hx0 hx2
  rw [Real.sqrt_sq hn0.le] at hL
  have hL0 := movingSquareLogWidth_pos hx
  have hlogLeft : Real.log x-Real.log (n^2) <= theta/(4*n) := by
    apply (log_sub_le_relative_gap hn2 hx).trans
    suffices hgap : x-n^2 <= theta/(4*n)*n^2 by
      convert div_le_div_of_nonneg_right hgap hn2.le using 1
      field_simp [hn0.ne']
    have he : theta/(4*n)*n^2 = theta*n/4 := by
      field_simp [hn0.ne']
    rw [he]
    linarith
  have hleft : -theta/4 <=
      (Real.log (n^2)-Real.log x)/movingSquareLogWidth x := by
    suffices hb : (-theta/4)*movingSquareLogWidth x <= Real.log (n^2)-Real.log x by
      convert div_le_div_of_nonneg_right hb hL0.le using 1 <;>
        first | rfl | field_simp [hL0.ne']
    have hscale := mul_le_mul_of_nonneg_left hL.1
      (show 0 <= theta/4 by positivity)
    have he : theta/4*(1/n) = theta/(4*n) := by ring
    rw [he] at hscale
    linarith
  have hleft0 : (Real.log (n^2)-Real.log x)/movingSquareLogWidth x <= 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (Real.log_le_log hn2 hx0)) hL0.le
  let r : Real := Real.sqrt x
  have hr0 : 0 < r := Real.sqrt_pos.mpr hx
  have hr2 : r^2 = x := Real.sq_sqrt hx.le
  have hrn : n <= r := by
    have hs := Real.sqrt_le_sqrt hx0
    rwa [Real.sqrt_sq hn0.le] at hs
  let y : Real := (r+1)^2
  let u : Real := (n+1)^2
  have hu : 0 < u := by dsimp [u]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have huy : u <= y := by dsimp [u,y]; nlinarith
  have hgap : y-u <= 2*(x-n^2) := by
    have hp := mul_nonneg (show 0 <= r-n by linarith)
      (show 0 <= r+n-2 by linarith)
    dsimp [y,u]
    nlinarith
  have hgapLog : Real.log y-Real.log u <= theta/(2*n) := by
    apply (log_sub_le_relative_gap hu hy).trans
    suffices hb : y-u <= theta/(2*n)*u by
      convert div_le_div_of_nonneg_right hb hu.le using 1
      field_simp [hu.ne']
    have htheta : theta*n/2 <= theta/(2*n)*u := by
      have hnn : n^2 <= u := by dsimp [u]; nlinarith
      have hmul := mul_le_mul_of_nonneg_left hnn
        (show 0 <= theta/(2*n) by positivity)
      have he : theta/(2*n)*n^2 = theta*n/2 := by
        field_simp [hn0.ne']
      rwa [he] at hmul
    have hshort : 2*(x-n^2) <= theta*n/2 := by linarith
    exact hgap.trans (hshort.trans htheta)
  have hmap : movingSquareMap 1 x = y := by
    rw [movingSquareMap, one_mul, exp_movingSquareLogWidth]
    change x*(1+Inv.inv r)^2 = (r+1)^2
    rw [<- hr2]
    field_simp [hr0.ne']
  have hylog : Real.log y = Real.log x+movingSquareLogWidth x := by
    rw [<- hmap, log_movingSquareMap hx, one_mul]
  have hright : 1-theta/2 <=
      (Real.log u-Real.log x)/movingSquareLogWidth x := by
    suffices hb : (1-theta/2)*movingSquareLogWidth x <= Real.log u-Real.log x by
      convert div_le_div_of_nonneg_right hb hL0.le using 1 <;>
        first | rfl | field_simp [hL0.ne']
    have hscale := mul_le_mul_of_nonneg_left hL.1
      (show 0 <= theta/2 by positivity)
    have he : theta/2*(1/n) = theta/(2*n) := by ring
    rw [he] at hscale
    rw [hylog] at hgapLog
    nlinarith
  have hright1 : (Real.log u-Real.log x)/movingSquareLogWidth x <= 1 := by
    suffices hb : Real.log u-Real.log x <= 1*movingSquareLogWidth x by
      convert div_le_div_of_nonneg_right hb hL0.le using 1 <;>
        first | rfl | field_simp [hL0.ne']
    have hlog := Real.log_le_log hu huy
    rw [hylog] at hlog
    linarith
  exact And.intro hleft (And.intro hleft0 (And.intro hright hright1))

theorem squareCorridorInnerTest_endpoints
    {n : Nat} (hn : 4 <= n) {theta x : Real}
    (ht0 : 0 < theta) (ht1 : theta <= 1/4)
    (hx0 : (n : Real)^2 <= x) (hx1 : x <= (n : Real)^2+theta*n/4) :
    Real.log (n*n : Nat) <= Real.log x+theta*movingSquareLogWidth x /\
      Real.log x+theta*movingSquareLogWidth x+
        (1-2*theta)*movingSquareLogWidth x <=
          Real.log ((n+1)*(n+1) : Nat) := by
  have hnR : (4 : Real) <= n := by exact_mod_cast hn
  have hn0 : (0 : Real) < n := by linarith
  have hn2 : (0 : Real) < (n : Real)^2 := sq_pos_of_pos hn0
  have hx : 0 < x := hn2.trans_le hx0
  have hL := movingSquareLogWidth_pos hx
  have hgeom := square_log_coordinates_persistence hnR ht0
    (show theta <= 1 by linarith) hx0 hx1
  have hlogn : Real.log (n*n : Nat) = Real.log ((n : Real)^2) := by
    congr 1
    push_cast
    ring
  have hlogA : Real.log ((n+1)*(n+1) : Nat) = Real.log (((n : Real)+1)^2) := by
    congr 1
    push_cast
    ring
  rw [hlogn,hlogA]
  refine And.intro ?_ ?_
  next =>
    have hlog := Real.log_le_log hn2 hx0
    have hp := mul_nonneg ht0.le hL.le
    linarith
  next =>
    have hmul := mul_le_mul_of_nonneg_right hgeom.2.2.1 hL.le
    have hmain : (1-theta/2)*movingSquareLogWidth x <=
        Real.log (((n : Real)+1)^2)-Real.log x := by
      convert hmul using 1 <;> first | rfl | field_simp [hL.ne']
    have hp := mul_nonneg ht0.le hL.le
    nlinarith

end RobinBV.Sieve
