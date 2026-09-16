/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Sieve.Helpers.SquareCorridorGeometry
import RobinBV.Sieve.Helpers.SquareCorridorTest
import RobinBV.Sieve.Proof.SquareIntervalExplicitFormula

/-!
# Actual prime counts from persistent inner and outer tests

Both bounds hold at every real starting point in the specified positive-length
interval. The lower consumer retains the complete prime-power allowance.
The upper consumer keeps every nonnegative Mangoldt contribution and needs no
prime-power subtraction. The signed explicit value retains both poles, the
gamma integral and all actual zeta zeros with multiplicities.

This proves no bound on the zero series and no almost-all prime-count theorem.
Import this module separately from the general RobinBV root, as required by
the existing pinned-provider namespace separation.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem prime_count_ge_contracted_square_corridor_test
    {n : Nat} (hn : 4 <= n) {theta eta x : Real}
    (ht0 : 0 < theta) (ht1 : theta <= 1/4) (he : 0 < eta)
    (hx0 : (n : Real)^2 <= x) (hx1 : x <= (n : Real)^2+theta*n/4) :
    (squareIntervalExplicitValue (squareCorridorInnerTest theta eta x)).re /
        Real.log ((n+1)*(n+1) : Nat) -
      (((n+1)*(n+1) : Nat) : Real)^(1/3 : Real) *
        Real.log ((n+1)*(n+1) : Nat)/Real.log 2 <=
      ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) := by
  have hn2 : 2 <= n := by omega
  have hnR : (4 : Real) <= n := by exact_mod_cast hn
  have hx : 0 < x := by nlinarith
  have hL0 := movingSquareLogWidth_pos hx
  have hb : 0 < 1-2*theta := by linarith
  let L : Real := (1-2*theta)*movingSquareLogWidth x
  let c : Real := Real.log x+theta*movingSquareLogWidth x
  have hL : 0 < L := mul_pos hb hL0
  have hends := squareCorridorInnerTest_endpoints hn ht0 ht1 hx0 hx1
  have hc : 0 <= c := by
    have hnn : (1 : Real) <= (n*n : Nat) := by
      exact_mod_cast (show 1 <= n*n by nlinarith)
    exact (Real.log_nonneg hnn).trans hends.1
  have hzeroLeft (u : Real) (hu : u <= c) :
      scaledLogWindowTest eta L c u = 0 := by
    have hz := logWindowCutoff_zero_left he
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) hL.le)
    simp only [scaledLogWindowTest,hz,Complex.ofReal_zero,mul_zero]
  have hzeroRight (u : Real) (hu : c+L <= u) :
      scaledLogWindowTest eta L c u = 0 := by
    have hfrac : 1 <= (u-c)/L := by
      have hdiv := div_le_div_of_nonneg_right (show L <= u-c by linarith) hL.le
      simpa only [div_self hL.ne'] using hdiv
    have hz := logWindowCutoff_zero_right he hfrac
    simp only [scaledLogWindowTest,hz,Complex.ofReal_zero,mul_zero]
  have hsupport : forall m : Nat,
      Not (Membership.mem (Finset.Ioo (n*n) ((n+1)*(n+1))) m) ->
        squareCorridorInnerTest theta eta x (Real.log m) = 0 := by
    intro m hm
    change scaledLogWindowTest eta L c (Real.log m) = 0
    by_cases hm0 : m = 0
    next =>
      rw [hm0,Nat.cast_zero,Real.log_zero]
      exact hzeroLeft 0 hc
    have hmpos : (0 : Real) < m := by
      exact_mod_cast (show 0 < m by omega)
    by_cases hsmall : m <= n*n
    next =>
      exact hzeroLeft (Real.log m) ((Real.log_le_log hmpos
        (by exact_mod_cast hsmall)).trans hends.1)
    next =>
      have hlarge : (n+1)*(n+1) <= m := by
        have hnot : Not (n*n < m /\ m < (n+1)*(n+1)) := by
          simpa only [Finset.mem_Ioo] using hm
        omega
      have hlog := Real.log_le_log
        (show (0 : Real) < ((n+1)*(n+1) : Nat) by positivity)
        (show (((n+1)*(n+1) : Nat) : Real) <= m by exact_mod_cast hlarge)
      exact hzeroRight (Real.log m) (hends.2.trans hlog)
  have hnegative : forall m : Nat,
      squareCorridorInnerTest theta eta x (-Real.log m) = 0 := by
    intro m
    have hm : 0 <= Real.log (m : Real) := by
      by_cases hm0 : m = 0
      next => simp only [hm0,Nat.cast_zero,Real.log_zero,le_refl]
      next =>
        exact Real.log_nonneg (by exact_mod_cast (show 1 <= m by omega))
    exact hzeroLeft (-Real.log m) (by linarith)
  have hweight : forall m : Nat,
      Membership.mem (Finset.Ioo (n*n) ((n+1)*(n+1))) m ->
        0 <= (squareCorridorInnerTest theta eta x (Real.log m)).re / Real.sqrt m /\
          (squareCorridorInnerTest theta eta x (Real.log m)).re / Real.sqrt m <= 1 := by
    intro m hm
    have hmpos : 0 < m := by
      have h := (Finset.mem_Ioo.mp hm).1
      nlinarith
    change 0 <= (scaledLogWindowTest eta L c (Real.log m)).re / Real.sqrt m /\
      (scaledLogWindowTest eta L c (Real.log m)).re / Real.sqrt m <= 1
    rw [scaledLogWindowTest_weight_eq hmpos]
    refine And.intro ?_ ?_
    next =>
      exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    next =>
      have hnorm := logWindowProfile_norm_le_one eta ((Real.log m-c)/L)
      have hle : abs (logWindowCutoff eta ((Real.log m-c)/L)) <= 1 := by
        simpa only [logWindowProfile,Complex.norm_real,Real.norm_eq_abs] using hnorm
      exact (le_abs_self _).trans hle
  exact prime_count_ge_square_interval_explicit_formula hn2
    (scaledLogWindowTest_contDiff eta L c)
    (scaledLogWindowTest_hasCompactSupport he hL c) hsupport hnegative hweight

private theorem finite_mangoldt_test_eq_explicit
    (S : Finset Nat) {k : Real -> Complex}
    (hk : ContDiff Real 2 k) (hkc : HasCompactSupport k)
    (hsupport : forall m : Nat, Not (Membership.mem S m) -> k (Real.log m) = 0)
    (hnegative : forall m : Nat, k (-Real.log m) = 0) :
    Finset.sum S (fun m => ArithmeticFunction.vonMangoldt m *
      ((k (Real.log m)).re/Real.sqrt m)) =
      (squareIntervalExplicitValue k).re := by
  let a : Nat -> Complex := fun m =>
    ((ArithmeticFunction.vonMangoldt m/Real.sqrt m : Real) : Complex) *
      (k (Real.log m)+k (-Real.log m))
  have ef := (Zeta23.WeilEF.EF_lit_zetaZeroConfig k hk hkc).2
  have ha : tsum a = squareIntervalExplicitValue k := by
    dsimp [a,squareIntervalExplicitValue]
    unfold Zeta23.EF.literatureRHS at ef
    dsimp [Zeta23.zetaZeroConfig] at ef
    linear_combination ef
  have hf : tsum a = Finset.sum S a := by
    apply tsum_eq_sum
    intro m hm
    change ((ArithmeticFunction.vonMangoldt m/Real.sqrt m : Real) : Complex) *
      (k (Real.log m)+k (-Real.log m)) = 0
    rw [hsupport m hm,hnegative m]
    simp only [add_zero,mul_zero]
  have hmap := map_sum Complex.reAddGroupHom a S
  calc
    _ = Finset.sum S (fun m => (a m).re) := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp [a]
      rw [hnegative m]
      simp only [add_zero,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      ring
    _ = (Finset.sum S a).re := hmap.symm
    _ = (tsum a).re := congrArg Complex.re hf.symm
    _ = _ := congrArg Complex.re ha

theorem prime_count_le_expanded_square_corridor_test
    {n : Nat} (hn : 4 <= n) {theta eta x : Real}
    (ht0 : 0 < theta) (ht1 : theta <= 1/4) (he : 0 < eta)
    (het : eta*(1+2*theta) <= theta/2)
    (hx0 : (n : Real)^2 <= x) (hx1 : x <= (n : Real)^2+theta*n/4) :
    ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real)*Real.log (n*n : Nat) <=
      (squareIntervalExplicitValue (squareCorridorOuterTest theta eta x)).re := by
  classical
  have hnR : (4 : Real) <= n := by exact_mod_cast hn
  have hn0 : (0 : Real) < n := by linarith
  have hx : 0 < x := by nlinarith
  have hx2 : x <= 2*(n : Real)^2 := by
    have hp := mul_le_mul_of_nonneg_right ht1 hn0.le
    nlinarith
  have hN16 : (16 : Real) <= (n : Real)^2 := by nlinarith
  have hL0 := movingSquareLogWidth_pos hx
  have hwidth := movingSquareLogWidth_dyadic_bounds hN16 hx0 hx2
  rw [Real.sqrt_sq hn0.le] at hwidth
  let L : Real := (1+2*theta)*movingSquareLogWidth x
  let c : Real := Real.log x-theta*movingSquareLogWidth x
  let M : Nat := 8*n*n
  let S : Finset Nat := Finset.Icc 1 M
  let k : Real -> Complex := squareCorridorOuterTest theta eta x
  have hL : 0 < L := mul_pos (by linarith) hL0
  have hLhalf : movingSquareLogWidth x <= 1/2 := by
    have hr := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 4) hnR
    have hu := hwidth.2
    simp only [div_eq_mul_inv] at hr hu
    nlinarith
  have hc : 0 < c := by
    have hrec := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 16)
      (show (16 : Real) <= x by nlinarith)
    have hlog := Real.one_sub_inv_le_log_of_pos hx
    have hp := mul_le_mul ht1 hLhalf hL0.le (by norm_num : (0 : Real) <= 1/4)
    dsimp [c]
    simp only [one_div] at hrec
    linarith
  have hzeroLeft (u : Real) (hu : u <= c) : k u = 0 := by
    have hz := logWindowCutoff_zero_left he
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) hL.le)
    change scaledLogWindowTest eta L c u = 0
    simp only [scaledLogWindowTest,hz,Complex.ofReal_zero,mul_zero]
  have hzeroRight (u : Real) (hu : c+L <= u) : k u = 0 := by
    have hfrac : 1 <= (u-c)/L := by
      have hd := div_le_div_of_nonneg_right (show L <= u-c by linarith) hL.le
      simpa only [div_self hL.ne'] using hd
    have hz := logWindowCutoff_zero_right he hfrac
    change scaledLogWindowTest eta L c u = 0
    simp only [scaledLogWindowTest,hz,Complex.ofReal_zero,mul_zero]
  have hcap : c+L <= Real.log (M : Real) := by
    have hmap := movingSquareMap_image_bounds hN16 hx0 hx2
      (show -1 <= 1+theta by linarith) (show 1+theta <= 2 by linarith)
    have hpos : 0 < movingSquareMap (1+theta) x := by
      exact mul_pos hx (Real.exp_pos _)
    have hlog := Real.log_le_log hpos hmap.2
    rw [log_movingSquareMap hx] at hlog
    have hM : (M : Real) = 8*(n : Real)^2 := by dsimp [M]; push_cast; ring
    rw [hM]
    dsimp [c,L]
    nlinarith
  have hsupport : forall m : Nat, Not (Membership.mem S m) -> k (Real.log m) = 0 := by
    intro m hm
    by_cases hm0 : m = 0
    next =>
      rw [hm0,Nat.cast_zero,Real.log_zero]
      exact hzeroLeft 0 hc.le
    have hlarge : M < m := by
      have hnot : Not (1 <= m /\ m <= M) := by simpa only [S,Finset.mem_Icc] using hm
      omega
    have hMpos : (0 : Real) < M := by dsimp [M]; positivity
    exact hzeroRight (Real.log m) (hcap.trans
      (Real.log_le_log hMpos (by exact_mod_cast hlarge.le)))
  have hnegative : forall m : Nat, k (-Real.log m) = 0 := by
    intro m
    have hm : 0 <= Real.log (m : Real) := by
      by_cases hm0 : m = 0
      next => simp only [hm0,Nat.cast_zero,Real.log_zero,le_refl]
      next => exact Real.log_nonneg (by exact_mod_cast (show 1 <= m by omega))
    exact hzeroLeft (-Real.log m) (by linarith)
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
  have hleft : (-theta/4)*movingSquareLogWidth x <= Real.log (n*n : Nat)-Real.log x := by
    rw [hlogn]
    have hm := mul_le_mul_of_nonneg_right hgeom.1 hL0.le
    convert hm using 1 <;> first | rfl | field_simp [hL0.ne']
  have hright : Real.log ((n+1)*(n+1) : Nat)-Real.log x <= movingSquareLogWidth x := by
    rw [hlogA]
    have hm := mul_le_mul_of_nonneg_right hgeom.2.2.2 hL0.le
    convert hm using 1 <;> first | rfl | field_simp [hL0.ne']
  have heta := mul_le_mul_of_nonneg_right het hL0.le
  have htheta := mul_nonneg ht0.le hL0.le
  have hcore : forall m : Nat,
      Membership.mem (Nat.PrimeSieve.squareIntervalPrimes n) m ->
        c+eta*L <= Real.log m /\ Real.log m <= c+(1-eta)*L := by
    intro m hm
    have hm' := Finset.mem_filter.mp hm
    have hlo : n*n < m := hm'.2.1
    have hhi : m < (n+1)*(n+1) := Finset.mem_range.mp hm'.1
    have hmpos : (0 : Real) < m := by exact_mod_cast hm'.2.2.pos
    have hloLog := Real.log_le_log
      (show (0 : Real) < (n*n : Nat) by positivity)
      (show ((n*n : Nat) : Real) <= m by exact_mod_cast hlo.le)
    have hhiLog := Real.log_le_log hmpos
      (show (m : Real) <= ((n+1)*(n+1) : Nat) by exact_mod_cast hhi.le)
    dsimp [c,L]
    constructor <;> nlinarith
  have hweightOne : forall m : Nat,
      Membership.mem (Nat.PrimeSieve.squareIntervalPrimes n) m ->
        (k (Real.log m)).re/Real.sqrt m = 1 := by
    intro m hm
    have hp : Nat.Prime m := (Finset.mem_filter.mp hm).2.2
    change (scaledLogWindowTest eta L c (Real.log m)).re/Real.sqrt m = 1
    rw [scaledLogWindowTest_weight_eq hp.pos]
    have hco := hcore m hm
    have hl : eta <= (Real.log m-c)/L := by
      have hd := div_le_div_of_nonneg_right (show eta*L <= Real.log m-c by linarith) hL.le
      convert hd using 1 <;> first | rfl | field_simp [hL.ne']
    have hr : eta <= 1-(Real.log m-c)/L := by
      have hd := div_le_div_of_nonneg_right (show Real.log m-c <= (1-eta)*L by linarith) hL.le
      have hd' : (Real.log m-c)/L <= 1-eta := by
        convert hd using 1 <;> first | rfl | field_simp [hL.ne']
      linarith
    have h1 := Real.smoothTransition.one_of_one_le ((_root_.one_le_div he).mpr hl)
    have h2 := Real.smoothTransition.one_of_one_le ((_root_.one_le_div he).mpr hr)
    simp only [logWindowCutoff,h1,h2,mul_one]
  let f : Nat -> Real := fun m => ArithmeticFunction.vonMangoldt m*
    ((k (Real.log m)).re/Real.sqrt m)
  have hnonneg : forall m : Nat, Membership.mem S m -> 0 <= f m := by
    intro m hm
    have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
    simp only [f]
    change 0 <= ArithmeticFunction.vonMangoldt m*
      ((scaledLogWindowTest eta L c (Real.log m)).re/Real.sqrt m)
    rw [scaledLogWindowTest_weight_eq hmpos]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))
  have hsubset : Nat.PrimeSieve.squareIntervalPrimes n <= S := by
    intro m hm
    have hm' := Finset.mem_filter.mp hm
    have hhi := Finset.mem_range.mp hm'.1
    have hp := hm'.2.2
    apply Finset.mem_Icc.mpr
    refine And.intro hp.one_le ?_
    dsimp [M]
    nlinarith
  have hsum : ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real)*
      Real.log (n*n : Nat) <= Finset.sum (Nat.PrimeSieve.squareIntervalPrimes n) f := by
    calc
      _ = Finset.sum (Nat.PrimeSieve.squareIntervalPrimes n)
          (fun _ => Real.log (n*n : Nat)) := by simp
      _ <= _ := by
        apply Finset.sum_le_sum
        intro m hm
        have hm' := Finset.mem_filter.mp hm
        rw [hweightOne m hm,mul_one,ArithmeticFunction.vonMangoldt_apply_prime hm'.2.2]
        exact Real.log_le_log (by positivity) (by exact_mod_cast hm'.2.1.le)
  have hS := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun m hm _ => hnonneg m hm)
  have hef := finite_mangoldt_test_eq_explicit S
    (scaledLogWindowTest_contDiff eta L c)
    (scaledLogWindowTest_hasCompactSupport he hL c) hsupport hnegative
  exact (hsum.trans hS).trans_eq hef

end RobinBV.Sieve
