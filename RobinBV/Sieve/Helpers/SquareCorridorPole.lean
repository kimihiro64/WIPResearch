/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import RobinBV.Sieve.Helpers.SquareCorridorTest
import Zeta23.Defs

/-!
# Explicit pole bounds throughout a square corridor

The growing pole is bounded by its full support and its unit plateau.
The entire shifted family retains lower supply (2n-2)(1-2theta)(1-2eta)
and upper mass (2n+7)(1+4theta). These are uniform continuum estimates,
not arithmetic evaluations or bounds on the actual zero series.
-/

set_option autoImplicit false

open MeasureTheory

namespace RobinBV.Sieve

theorem scaledLogWindowTest_pole_bounds {eta L c : Real}
    (he : 0 < eta) (he2 : eta <= 1/2) (hL : 0 < L) :
    Real.exp c * L * (1-2*eta) <=
      (Zeta23.paperFT (scaledLogWindowTest eta L c) (-Complex.I/2)).re /\
    (Zeta23.paperFT (scaledLogWindowTest eta L c) (-Complex.I/2)).re <=
      Real.exp (c+L) * L := by
  let f : Real -> Real := fun u => Real.exp u * logWindowCutoff eta ((u-c)/L)
  have hcont : Continuous f := by
    dsimp [f, logWindowCutoff]
    fun_prop
  have hnonneg (u : Real) : 0 <= f u := by
    exact mul_nonneg (Real.exp_pos u).le
      (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
  have hzero (u : Real) (hu : Not ((Set.Icc c (c+L)) u)) : f u = 0 := by
    by_cases hc : u <= c
    next =>
      have hz := logWindowCutoff_zero_left (v := (u-c)/L) he
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le)
      simp only [f, hz, mul_zero]
    next =>
      have hcu : c <= u := le_of_lt (lt_of_not_ge hc)
      have hright : c+L <= u := by
        by_contra h
        exact hu (And.intro hcu (le_of_lt (lt_of_not_ge h)))
      have hv : 1 <= (u-c)/L := by
        calc
          (1 : Real) = L/L := (div_self hL.ne').symm
          _ <= (u-c)/L := div_le_div_of_nonneg_right (by linarith) hL.le
      have hz := logWindowCutoff_zero_right he hv
      simp only [f, hz, mul_zero]
  have hcomp : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := c) (b := c+L))
    intro u hu
    by_contra h
    exact hu (hzero u h)
  have hf : Integrable f := hcont.integrable_of_hasCompactSupport hcomp
  have hpole : (Zeta23.paperFT (scaledLogWindowTest eta L c) (-Complex.I/2)).re =
      MeasureTheory.integral MeasureTheory.volume f := by
    have hfun : (fun u : Real => scaledLogWindowTest eta L c u *
        Complex.exp (Complex.I*(-Complex.I/2)*(u : Complex))) =
        fun u : Real => (f u : Complex) := by
      funext u
      have he : (u : Complex)/2+Complex.I*(-Complex.I/2)*(u : Complex) =
          (u : Complex) := by
        ring_nf
        rw [Complex.I_sq]
        ring
      calc
        _ = (Complex.exp ((u : Complex)/2)*
            Complex.exp (Complex.I*(-Complex.I/2)*(u : Complex)))*
              (logWindowCutoff eta ((u-c)/L) : Complex) := by
          unfold scaledLogWindowTest
          ring
        _ = Complex.exp (u : Complex)*(logWindowCutoff eta ((u-c)/L) : Complex) := by
          rw [<- Complex.exp_add, he]
        _ = _ := by rw [<- Complex.ofReal_exp]; simp only [f, Complex.ofReal_mul]
    rw [Zeta23.paperFT, hfun, _root_.integral_complex_ofReal, Complex.ofReal_re]
  have hcoreOrder : c+eta*L <= c+(1-eta)*L := by nlinarith
  have hcore (u : Real) (hu : (Set.Icc (c+eta*L) (c+(1-eta)*L)) u) :
      Real.exp c <= f u := by
    have hv0 : eta <= (u-c)/L := by
      convert div_le_div_of_nonneg_right (show eta*L <= u-c by linarith [hu.1]) hL.le using 1 <;>
        first | rfl | field_simp [hL.ne']
    have hv1 : eta <= 1-(u-c)/L := by
      have ht := div_le_div_of_nonneg_right
        (show u-c <= (1-eta)*L by linarith [hu.2]) hL.le
      have ht' : (u-c)/L <= 1-eta := by
        convert ht using 1 <;> first | rfl | field_simp [hL.ne']
      linarith
    have h1 := Real.smoothTransition.one_of_one_le ((_root_.one_le_div he).mpr hv0)
    have h2 := Real.smoothTransition.one_of_one_le ((_root_.one_le_div he).mpr hv1)
    have hc : c <= u := by nlinarith [hu.1]
    simpa only [f, logWindowCutoff, h1, h2, one_mul, mul_one] using
      Real.exp_le_exp.mpr hc
  have hlo := MeasureTheory.setIntegral_ge_of_const_le_real
    measurableSet_Icc isCompact_Icc.measure_lt_top.ne hcore hf.integrableOn
  have hglobal := MeasureTheory.setIntegral_le_integral
    (s := Set.Icc (c+eta*L) (c+(1-eta)*L)) hf (Filter.Eventually.of_forall hnonneg)
  rw [Real.volume_real_Icc_of_le hcoreOrder] at hlo
  have hlower : Real.exp c*L*(1-2*eta) <= MeasureTheory.integral MeasureTheory.volume f := by
    calc
      _ = Real.exp c*((c+(1-eta)*L)-(c+eta*L)) := by ring
      _ <= _ := hlo.trans hglobal
  have hpoint (u : Real) (hu : (Set.Icc c (c+L)) u) :
      norm (f u) <= Real.exp (c+L) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u)]
    have hcut : logWindowCutoff eta ((u-c)/L) <= 1 := by
      have h := logWindowProfile_norm_le_one eta ((u-c)/L)
      have hp : 0 <= logWindowCutoff eta ((u-c)/L) :=
        mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
      simpa only [logWindowProfile, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hp] using h
    calc
      _ <= Real.exp u*1 := mul_le_mul_of_nonneg_left hcut (Real.exp_pos u).le
      _ <= Real.exp (c+L) := by simpa only [mul_one] using Real.exp_le_exp.mpr hu.2
  have hu : norm (MeasureTheory.integral
      (MeasureTheory.volume.restrict (Set.Icc c (c+L))) f) <=
      Real.exp (c+L)*MeasureTheory.volume.real (Set.Icc c (c+L)) :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const
      isCompact_Icc.measure_lt_top hpoint
  have hsupportIntegral : MeasureTheory.integral
      (MeasureTheory.volume.restrict (Set.Icc c (c+L))) f =
      MeasureTheory.integral MeasureTheory.volume f :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc c (c+L)) hzero
  rw [Real.volume_real_Icc_of_le (show c <= c+L by linarith),
    hsupportIntegral] at hu
  have hupper : MeasureTheory.integral MeasureTheory.volume f <= Real.exp (c+L)*L := by
    calc
      _ <= norm (MeasureTheory.integral MeasureTheory.volume f) := le_abs_self _
      _ <= _ := by simpa only [add_sub_cancel_left] using hu
  rw [hpole]
  exact And.intro hlower hupper

theorem squareCorridor_scalar_parameters {n theta x : Real}
    (hn : 4 <= n) (ht0 : 0 < theta) (ht1 : theta <= 1/4)
    (hx0 : n^2 <= x) (hx1 : x <= n^2+theta*n/4) :
    0 < movingSquareLogWidth x /\ movingSquareLogWidth x <= 1/2 /\
    3/2 <= Real.log x /\ 2*n-2 <= x*movingSquareLogWidth x /\
    Real.sqrt x <= n+theta/8 /\
    Real.exp (theta*movingSquareLogWidth x) <= 1+theta := by
  have hn0 : 0 < n := by linarith
  have hx : 0 < x := (sq_pos_of_pos hn0).trans_le hx0
  have hx16 : 16 <= x := by nlinarith only [hn, hx0]
  let r : Real := Real.sqrt x
  have hr0 : 0 < r := Real.sqrt_pos.mpr hx
  have hr2 : r^2 = x := Real.sq_sqrt hx.le
  have hrn : n <= r := by
    have h := Real.sqrt_le_sqrt hx0
    rwa [Real.sqrt_sq hn0.le] at h
  have hr4 : 4 <= r := hn.trans hrn
  have hir : 1/r <= 1/4 :=
    one_div_le_one_div_of_le (by norm_num : (0 : Real) < 4) hr4
  have hL := movingSquareLogWidth_pos hx
  have hdyad := movingSquareLogWidth_dyadic_bounds hx16 le_rfl
    (show x <= 2*x by linarith)
  have hLhalf : movingSquareLogWidth x <= 1/2 := by
    have h := hdyad.2
    change movingSquareLogWidth x <= 2/r at h
    rw [show 2/r = 2*(1/r) by ring] at h
    linarith only [h, hir]
  have hlogr := Real.one_sub_inv_le_log_of_pos hr0
  have hlogid : Real.log x = 2*Real.log r := by
    rw [<- hr2, Real.log_pow]
    norm_num
  have hlogx : 3/2 <= Real.log x := by
    rw [hlogid]
    rw [<- one_div] at hlogr
    linarith only [hlogr, hir]
  have harg : 0 < 1+Inv.inv r := by positivity
  have hlo := Real.one_sub_inv_le_log_of_pos harg
  have hfrac : 1-Inv.inv (1+Inv.inv r) = 1/(r+1) := by
    field_simp [hr0.ne', (show Not (r+1 = 0) by positivity)]
    ring
  rw [hfrac] at hlo
  have hlx : 2*n-2 <= x*movingSquareLogWidth x := by
    have hprod := mul_le_mul_of_nonneg_left hlo (show 0 <= 2*x by positivity)
    have hid : 2*x*(1/(r+1)) = 2*r-2+2/(r+1) := by
      rw [<- hr2]
      field_simp
      ring
    rw [hid] at hprod
    change 2*n-2 <= x*(2*Real.log (1+Inv.inv r))
    nlinarith only [hrn, hprod, show 0 <= 2/(r+1) by positivity]
  have hrs : r <= n+theta/8 := by
    by_contra h
    have hh : n+theta/8 < r := lt_of_not_ge h
    have hprod := mul_pos (sub_pos.mpr hh)
      (show 0 < r+n+theta/8 by linarith only [hr0, hn0, ht0])
    nlinarith only [hprod, hr2, hx1, sq_nonneg (theta/8)]
  have htplus : 0 < 1+theta := by linarith
  have htlog := Real.one_sub_inv_le_log_of_pos htplus
  have htid : 1-Inv.inv (1+theta) = theta/(1+theta) := by field_simp; ring
  rw [htid] at htlog
  have htfrac : theta/2 <= theta/(1+theta) := by
    have hm : (theta/2)*(1+theta) <= theta := by
      have hp := mul_nonneg ht0.le (show 0 <= 1-theta by linarith only [ht1])
      nlinarith only [hp]
    convert div_le_div_of_nonneg_right hm htplus.le using 1 <;>
      first | rfl | field_simp [htplus.ne']
  have htexp : Real.exp (theta*movingSquareLogWidth x) <= 1+theta := by
    have hmul : theta*movingSquareLogWidth x <= theta/2 := by
      calc
        _ <= theta*(1/2) := mul_le_mul_of_nonneg_left hLhalf ht0.le
        _ = _ := by ring
    have h := Real.exp_le_exp.mpr (hmul.trans (htfrac.trans htlog))
    rwa [Real.exp_log htplus] at h
  exact And.intro hL (And.intro hLhalf (And.intro hlogx
    (And.intro hlx (And.intro hrs htexp))))

theorem squareCorridor_pole_bounds {n theta eta x : Real}
    (hn : 4 <= n) (ht0 : 0 < theta) (ht1 : theta <= 1/4)
    (he : 0 < eta) (he2 : eta <= 1/2)
    (hx0 : n^2 <= x) (hx1 : x <= n^2+theta*n/4) :
    (2*n-2)*(1-2*theta)*(1-2*eta) <=
      (Zeta23.paperFT (squareCorridorInnerTest theta eta x) (-Complex.I/2)).re /\
    (Zeta23.paperFT (squareCorridorOuterTest theta eta x) (-Complex.I/2)).re <=
      (2*n+7)*(1+4*theta) := by
  have hp := squareCorridor_scalar_parameters hn ht0 ht1 hx0 hx1
  have hn0 : 0 < n := by linarith
  have hx : 0 < x := (sq_pos_of_pos hn0).trans_le hx0
  have ha : 0 < 1-2*theta := by linarith
  have hb : 0 <= 1-2*eta := by linarith
  have hout : 0 < 1+2*theta := by linarith
  have hInner := (scaledLogWindowTest_pole_bounds
    (c := Real.log x+theta*movingSquareLogWidth x) he he2 (mul_pos ha hp.1)).1
  have hec : x <= Real.exp (Real.log x+theta*movingSquareLogWidth x) := by
    calc
      x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ <= _ := Real.exp_le_exp.mpr (by nlinarith [hp.1])
  have hlow : (2*n-2)*(1-2*theta)*(1-2*eta) <=
      (Zeta23.paperFT (squareCorridorInnerTest theta eta x) (-Complex.I/2)).re := by
    calc
      _ <= (x*movingSquareLogWidth x)*(1-2*theta)*(1-2*eta) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hp.2.2.2.1 ha.le) hb
      _ = x*((1-2*theta)*movingSquareLogWidth x)*(1-2*eta) := by ring
      _ <= Real.exp (Real.log x+theta*movingSquareLogWidth x)*
          ((1-2*theta)*movingSquareLogWidth x)*(1-2*eta) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hec (mul_pos ha hp.1).le) hb
      _ <= _ := hInner
  have hOuter := (scaledLogWindowTest_pole_bounds
    (c := Real.log x-theta*movingSquareLogWidth x) he he2 (mul_pos hout hp.1)).2
  let r : Real := Real.sqrt x
  have hr0 : 0 < r := Real.sqrt_pos.mpr hx
  have hr2 : r^2 = x := Real.sq_sqrt hx.le
  have hrn : n <= r := by
    have h := Real.sqrt_le_sqrt hx0
    rwa [Real.sqrt_sq hn0.le] at h
  have hir : 1/r <= 1/4 :=
    one_div_le_one_div_of_le (by norm_num : (0 : Real) < 4) (hn.trans hrn)
  have hdyad := movingSquareLogWidth_dyadic_bounds (show 16 <= x by nlinarith)
    le_rfl (show x <= 2*x by linarith)
  have hbase : x*Real.exp (movingSquareLogWidth x)*movingSquareLogWidth x <=
      2*n+7 := by
    have h := mul_le_mul_of_nonneg_left hdyad.2
      (show 0 <= x*Real.exp (movingSquareLogWidth x) by positivity)
    have hid : x*Real.exp (movingSquareLogWidth x)*(2/r) = 2*r+4+2/r := by
      rw [exp_movingSquareLogWidth]
      change x*(1+Inv.inv r)^2*(2/r) = _
      rw [<- hr2]
      field_simp [hr0.ne']
      ring
    change x*Real.exp (movingSquareLogWidth x)*movingSquareLogWidth x <=
      x*Real.exp (movingSquareLogWidth x)*(2/r) at h
    rw [hid] at h
    have hrs := hp.2.2.2.2.1
    change r <= n+theta/8 at hrs
    rw [show 2/r = 2*(1/r) by ring] at h
    linarith only [h, hrs, hir, ht1]
  have hpoly : (1+theta)*(1+2*theta) <= 1+4*theta := by
    have hp' := mul_nonneg ht0.le (show 0 <= 1-2*theta by linarith only [ht1])
    nlinarith only [hp']
  have hmain : Real.exp (Real.log x-theta*movingSquareLogWidth x+
        (1+2*theta)*movingSquareLogWidth x)*((1+2*theta)*movingSquareLogWidth x) <=
      (2*n+7)*(1+4*theta) := by
    have hid : Real.log x-theta*movingSquareLogWidth x+
        (1+2*theta)*movingSquareLogWidth x =
        Real.log x+movingSquareLogWidth x+theta*movingSquareLogWidth x := by ring
    rw [hid, Real.exp_add, Real.exp_add, Real.exp_log hx]
    calc
      _ = (x*Real.exp (movingSquareLogWidth x)*movingSquareLogWidth x)*
          Real.exp (theta*movingSquareLogWidth x)*(1+2*theta) := by ring
      _ <= (2*n+7)*Real.exp (theta*movingSquareLogWidth x)*(1+2*theta) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le) hout.le
      _ <= (2*n+7)*(1+theta)*(1+2*theta) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp.2.2.2.2.2 (by linarith)) hout.le
      _ <= (2*n+7)*(1+4*theta) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hpoly (show 0 <= 2*n+7 by linarith)
  exact And.intro hlow (hOuter.trans hmain)

end RobinBV.Sieve
