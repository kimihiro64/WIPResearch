/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.BernoulliPeriodic
import Zeta23.FromPNTPlus.ZetaBounds
import Zeta23.Statement

/-!
# Euler--Maclaurin zero detection for actual zeta zeros

The imported unconditional first-order zeta identity is combined with the
normalized periodic Bernoulli recursion. Every finite boundary correction
and the final absolutely convergent tail are retained before estimation.

For each fixed real delta in (0,1/2], the final theorem gives a fixed
constant C >= 1 such that the Dirichlet sum through ceil(T^(1+delta)) has
norm at most C*T^(-1/4), for every T >= 1 and every actual nontrivial
zero s with Re s >= 1/2 and T <= abs(Im s) <= 2*T. The constant is
existential and is not numerically evaluated. The extra length exponent
delta is retained; this is not a zero-energy, zero-density, or prime-count
estimate.

The actual first-order identity is provided by the pinned Zeta23 source.
This module is directly importable and is not exported through the general
project root, which has a separate PNT dependency closure.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

/-- The first-order identity at an actual nontrivial zero, with positive integer support. -/
theorem nontrivial_zero_euler_first {s : Complex} (hs : Zeta23.IsNontrivialZero s)
    {N : Nat} (hN : 0 < N) :
    (0 : Complex) =
      (Finset.range N).sum (fun n => ((n+1 : Nat) : Complex)^(-s)) +
      (N : Complex)^(1-s)/(s-1) - (N : Complex)^(-s)/2 -
      s*MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
        (fun x : Real => Complex.ofReal (Polynomial.bernoulliPeriodic 1 x)*
          Complex.ofReal x^(-s-1)) := by
  have hs1 : Not (s = 1) := by
    intro heq
    have h := hs.2.2
    rw [heq] at h
    norm_num at h
  have hs0 : Not (s = 0) := by
    intro heq
    have h := hs.2.1
    rw [heq] at h
    norm_num at h
  have hZ : riemannZeta0 N s = 0 := (Zeta0EqZeta hN hs.2.1 hs1).trans hs.1
  have hS : (Finset.range (N+1)).sum (fun n => 1/(n : Complex)^s) =
      (Finset.range N).sum (fun n => ((n+1 : Nat) : Complex)^(-s)) := by
    simp only [one_div_cpow_eq_cpow_neg]
    rw [Finset.sum_range_succ']
    simp [Complex.zero_cpow, hs0]
  have hB (x : Real) : Polynomial.bernoulliPeriodic 1 x =
      x - (Int.floor x : Real) - 1/2 := by
    simp only [Polynomial.bernoulliPeriodic, Polynomial.bernoulliNormalizedReal,
      Polynomial.bernoulliNormalized, Nat.factorial_one, Nat.cast_one, div_one,
      map_one, one_mul, Polynomial.bernoulli_one, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Int.fract]
    norm_num
  have hI : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
      (fun x : Real => ((Int.floor x : Complex)+1/2-(x : Complex))*
        (x : Complex)^(-(s+1))) =
      -MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
        (fun x : Real => Complex.ofReal (Polynomial.bernoulliPeriodic 1 x)*
          Complex.ofReal x^(-s-1)) := by
    rw [<- MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [hB x]
      push_cast
      rw [show -(s+1) = -s-1 by ring]
      ring)
  have hPole : (-(N : Complex)^(1-s))/(1-s) =
      (N : Complex)^(1-s)/(s-1) := by
    rw [show (1 : Complex)-s = -(s-1) by ring, div_neg, neg_div, neg_neg]
  rw [riemannZeta0_apply, hS, hI, hPole] at hZ
  calc
    _ = (Finset.range N).sum (fun n => ((n+1 : Nat) : Complex)^(-s)) +
        ((N : Complex)^(1-s)/(s-1) + (-(N : Complex)^(-s))/2 +
        s*(-MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
          (fun x : Real => Complex.ofReal (Polynomial.bernoulliPeriodic 1 x)*
            Complex.ofReal x^(-s-1)))) := hZ.symm
    _ = _ := by ring

/-- Exact expansion to every finite order, including all boundary corrections and the tail. -/
theorem nontrivial_zero_euler_expansion {s : Complex}
    (hs : Zeta23.IsNontrivialZero s) {N : Nat} (hN : 0 < N) (m : Nat) :
    let A : Nat -> Complex := fun k => (Finset.range k).prod (fun r => s+(r : Complex))
    let R : Nat -> Complex := fun k =>
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
        (fun x : Real => Complex.ofReal (Polynomial.bernoulliPeriodic k x)*
          Complex.ofReal x^(-s-(k : Complex)))
    (0 : Complex) =
      (Finset.range N).sum (fun n => ((n+1 : Nat) : Complex)^(-s)) +
      (N : Complex)^(1-s)/(s-1) - (N : Complex)^(-s)/2 +
      (Finset.range m).sum (fun j =>
        Complex.ofReal (Polynomial.bernoulliNormalizedReal (j+2) 0)*
          A (j+1)*(N : Complex)^(-s-((j+1 : Nat) : Complex))) -
      A (m+1)*R (m+1) := by
  let A : Nat -> Complex := fun k => (Finset.range k).prod (fun r => s+(r : Complex))
  let R : Nat -> Complex := fun k =>
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
      (fun x : Real => Complex.ofReal (Polynomial.bernoulliPeriodic k x)*
        Complex.ofReal x^(-s-(k : Complex)))
  change (0 : Complex) =
    (Finset.range N).sum (fun n => ((n+1 : Nat) : Complex)^(-s)) +
    (N : Complex)^(1-s)/(s-1) - (N : Complex)^(-s)/2 +
    (Finset.range m).sum (fun j =>
      Complex.ofReal (Polynomial.bernoulliNormalizedReal (j+2) 0)*
        A (j+1)*(N : Complex)^(-s-((j+1 : Nat) : Complex))) -
    A (m+1)*R (m+1)
  have hA (k : Nat) : A (k+1) = A k*(s+(k : Complex)) :=
    Finset.prod_range_succ _ k
  have hR (k : Nat) (hk : 1 <= k) :
      R k = -Complex.ofReal (Polynomial.bernoulliNormalizedReal (k+1) 0)*
        (N : Complex)^(-s-(k : Complex)) + (s+(k : Complex))*R (k+1) := by
    have hkR : (1 : Real) <= k := by exact_mod_cast hk
    have hz : (-s-(k : Complex)).re < -1 := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
      linarith [hs.2.1]
    have h := Polynomial.bernoulliPeriodic_cpow_tail_recursion hk hN hz
    have hexp : -s-(k : Complex)-1 = -s-((k+1 : Nat) : Complex) := by
      push_cast
      ring
    calc
      _ = -Complex.ofReal (Polynomial.bernoulliNormalizedReal (k+1) 0)*
          (N : Complex)^(-s-(k : Complex)) -
          (-s-(k : Complex))*R (k+1) := by
        simpa only [R, hexp, Complex.ofReal_natCast] using h
      _ = _ := by ring
  induction m with
  | zero =>
    simpa only [A, R, Finset.sum_range_zero, Finset.prod_range_succ,
      Finset.prod_range_zero, Nat.zero_add, Nat.cast_zero, Nat.cast_one, add_zero, one_mul]
      using nontrivial_zero_euler_first hs hN
  | succ m ih =>
    rw [Finset.sum_range_succ, hA (m+1)]
    rw [hR (m+1) (by omega)] at ih
    linear_combination ih

/-- A complete uniform norm bound before selecting the Dirichlet-polynomial cutoff. -/
theorem nontrivial_zero_euler_norm_bound (m : Nat) (hm : 1 <= m) :
    Exists fun C : Real => 1 <= C /\
      forall (N : Nat) (T : Real) (s : Complex), 0 < N -> 1 <= T ->
      T <= (N : Real) -> Zeta23.IsNontrivialZero s -> (1/2 : Real) <= s.re ->
      T <= abs s.im -> abs s.im <= 2*T ->
      norm ((Finset.range N).sum (fun n => ((n+1 : Nat) : Complex)^(-s))) <=
        (N : Real)^(1/2 : Real)/T + C*(N : Real)^(-(1/2 : Real)) +
        C*T^(m+1)*(N : Real)^((1/2 : Real)-((m+1 : Nat) : Real)) := by
  let hTail := Polynomial.bernoulliPeriodic_cpow_tail_bound (m+1)
  let Ct : Real := hTail.choose
  have hCt : 1 <= Ct := hTail.choose_spec.1
  let K : Nat -> Real := fun j => ((j : Real)+3)^j
  let D : Real := (Finset.range m).sum (fun j =>
    norm (Complex.ofReal (Polynomial.bernoulliNormalizedReal (j+2) 0))*K (j+1))
  have hK (j : Nat) : 0 <= K j := by dsimp [K]; positivity
  have hD : 0 <= D := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hK _))
  let C : Real := 1+D+Ct*K (m+1)
  have hC1 : 1+D <= C := by
    dsimp [C]
    exact le_add_of_nonneg_right (mul_nonneg (by linarith) (hK _))
  have hC2 : Ct*K (m+1) <= C := by dsimp [C]; linarith
  refine Exists.intro C (And.intro (by linarith) ?_)
  intro N T s hN hT hTN hs hsig ht0 ht1
  have hN0 : (0 : Real) < N := by exact_mod_cast hN
  have hN1 : (1 : Real) <= N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  have hmR : (1 : Real) <= m := by exact_mod_cast hm
  let A : Nat -> Complex := fun k => (Finset.range k).prod (fun r => s+(r : Complex))
  let R : Nat -> Complex := fun k =>
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
      (fun x : Real => Complex.ofReal (Polynomial.bernoulliPeriodic k x)*
        Complex.ofReal x^(-s-(k : Complex)))
  let B : Complex := (Finset.range m).sum (fun j =>
    Complex.ofReal (Polynomial.bernoulliNormalizedReal (j+2) 0)*
      A (j+1)*(N : Complex)^(-s-((j+1 : Nat) : Complex)))
  have hA (j : Nat) (U : Real) (hU : 1 <= U) (hu : abs s.im <= 2*U) :
      norm (A j) <= K j*U^j := by
    dsimp [A, K]
    rw [norm_prod, <- mul_pow]
    calc
      _ <= (Finset.range j).prod (fun _ => ((j : Real)+3)*U) := by
        apply Finset.prod_le_prod (fun r _ => norm_nonneg _)
        intro r hr
        have hrR : (r : Real) <= j := by
          exact_mod_cast (Finset.mem_range.mp hr).le
        have hr0 : (0 : Real) <= r := Nat.cast_nonneg r
        calc
          _ <= abs (s+(r : Complex)).re + abs (s+(r : Complex)).im :=
            Complex.norm_le_abs_re_add_abs_im _
          _ = s.re+(r : Real)+abs s.im := by
            simp only [Complex.add_re, Complex.natCast_re, Complex.add_im,
              Complex.natCast_im, add_zero, abs_of_nonneg (add_nonneg hs.2.1.le hr0)]
          _ <= ((j : Real)+3)*U := by
            nlinarith [show (0 : Real) <= j from Nat.cast_nonneg j, hs.2.2]
      _ = _ := by rw [Finset.prod_const, Finset.card_range]
  have hPow (j : Nat) :
      norm ((N : Complex)^(-s-(j : Complex))) <=
        (N : Real)^(-(1/2 : Real)-(j : Real)) := by
    rw [show (N : Complex) = Complex.ofReal (N : Real) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
    linarith
  have hCancel (j : Nat) :
      (N : Real)^j*(N : Real)^(-(1/2 : Real)-(j : Real)) =
        (N : Real)^(-(1/2 : Real)) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_add hN0]
    congr 1
    ring
  have hB : norm B <= D*(N : Real)^(-(1/2 : Real)) := by
    calc
      _ <= (Finset.range m).sum (fun j =>
          norm (Complex.ofReal (Polynomial.bernoulliNormalizedReal (j+2) 0)*
            A (j+1)*(N : Complex)^(-s-((j+1 : Nat) : Complex)))) :=
        norm_sum_le _ _
      _ <= (Finset.range m).sum (fun j =>
          (norm (Complex.ofReal (Polynomial.bernoulliNormalizedReal (j+2) 0))*K (j+1))*
            (N : Real)^(-(1/2 : Real))) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_mul]
        calc
          _ <= norm (Complex.ofReal (Polynomial.bernoulliNormalizedReal (j+2) 0))*
              (K (j+1)*(N : Real)^(j+1))*
              (N : Real)^(-(1/2 : Real)-((j+1 : Nat) : Real)) := by
            apply mul_le_mul
            next =>
              exact mul_le_mul_of_nonneg_left
                (hA (j+1) (N : Real) hN1 (by linarith)) (norm_nonneg _)
            next =>
              exact hPow (j+1)
            next =>
              exact norm_nonneg _
            next =>
              exact mul_nonneg (norm_nonneg _)
                (mul_nonneg (hK _) (pow_nonneg hN0.le _))
          _ = (norm (Complex.ofReal (Polynomial.bernoulliNormalizedReal (j+2) 0))*K (j+1))*
              ((N : Real)^(j+1)*(N : Real)^(-(1/2 : Real)-((j+1 : Nat) : Real))) := by ring
          _ = _ := by rw [hCancel]
      _ = _ := by rw [<- Finset.sum_mul]
  have hPole : norm ((N : Complex)^(1-s)/(s-1)) <= (N : Real)^(1/2 : Real)/T := by
    have hd : T <= norm (s-1) := ht0.trans (by
      simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (s-1))
    have hn : norm ((N : Complex)^(1-s)) <= (N : Real)^(1/2 : Real) := by
      rw [show (N : Complex) = Complex.ofReal (N : Real) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hN0]
      apply Real.rpow_le_rpow_of_exponent_le hN1
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    rw [norm_div]
    exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) hT0 hd)
  have hHalf : norm ((N : Complex)^(-s)/2) <= (N : Real)^(-(1/2 : Real)) := by
    have hn : norm ((N : Complex)^(-s)) <= (N : Real)^(-(1/2 : Real)) := by
      simpa only [Nat.cast_zero, sub_zero] using hPow 0
    have h2 : norm (2 : Complex) = 2 := by norm_num
    rw [norm_div, h2]
    have h := div_le_div_of_nonneg_right hn (by norm_num : (0 : Real) <= 2)
    linarith [Real.rpow_nonneg hN0.le (-(1/2 : Real))]
  have hR : norm (R (m+1)) <= Ct*(N : Real)^((1/2 : Real)-((m+1 : Nat) : Real)) := by
    have hz : (-s-((m+1 : Nat) : Complex)).re < -1 := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re,
        Nat.cast_add, Nat.cast_one, Complex.add_re, Complex.one_re]
      linarith [hs.2.1]
    have he : (-s-((m+1 : Nat) : Complex)).re+1 = -s.re-(m : Real) := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re,
        Nat.cast_add, Nat.cast_one, Complex.add_re, Complex.one_re]
      ring
    have hb := (hTail.choose_spec.2 (N : Real) (-s-((m+1 : Nat) : Complex)) hN0 hz).2
    rw [he] at hb
    change norm (R (m+1)) <= Ct*(-(N : Real)^(-s.re-(m : Real))/(-s.re-(m : Real))) at hb
    have hd : (1 : Real) <= s.re+(m : Real) := by linarith
    have hf : -(N : Real)^(-s.re-(m : Real))/(-s.re-(m : Real)) =
        (N : Real)^(-s.re-(m : Real))/(s.re+(m : Real)) := by
      rw [show -s.re-(m : Real) = -(s.re+(m : Real)) by ring,
        div_neg, neg_div, neg_neg]
    rw [hf] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    calc
      _ <= (N : Real)^(-s.re-(m : Real))/1 :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) (by norm_num) hd
      _ <= _ := by
        rw [div_one]
        apply Real.rpow_le_rpow_of_exponent_le hN1
        push_cast
        linarith
  have hRem : norm (A (m+1)*R (m+1)) <=
      Ct*K (m+1)*T^(m+1)*(N : Real)^((1/2 : Real)-((m+1 : Nat) : Real)) := by
    rw [norm_mul]
    calc
      _ <= (K (m+1)*T^(m+1))*
          (Ct*(N : Real)^((1/2 : Real)-((m+1 : Nat) : Real))) :=
        mul_le_mul (hA (m+1) T hT ht1) hR (norm_nonneg _)
          (mul_nonneg (hK _) (pow_nonneg hT0.le _))
      _ = _ := by ring
  have he := nontrivial_zero_euler_expansion hs hN m
  change (0 : Complex) =
    (Finset.range N).sum (fun n => ((n+1 : Nat) : Complex)^(-s)) +
    (N : Complex)^(1-s)/(s-1) - (N : Complex)^(-s)/2 + B -
    A (m+1)*R (m+1) at he
  have hS : (Finset.range N).sum (fun n => ((n+1 : Nat) : Complex)^(-s)) =
      -(N : Complex)^(1-s)/(s-1) + (N : Complex)^(-s)/2 - B + A (m+1)*R (m+1) := by
    linear_combination -he
  rw [hS]
  have hn1 := norm_add_le
    (-(N : Complex)^(1-s)/(s-1) + (N : Complex)^(-s)/2 - B) (A (m+1)*R (m+1))
  have hn2 := norm_sub_le
    (-(N : Complex)^(1-s)/(s-1) + (N : Complex)^(-s)/2) B
  have hn3 := norm_add_le (-(N : Complex)^(1-s)/(s-1)) ((N : Complex)^(-s)/2)
  simp only [neg_div] at hn1 hn2 hn3
  simp only [neg_div]
  rw [norm_neg] at hn3
  calc
    _ <= (N : Real)^(1/2 : Real)/T + (1+D)*(N : Real)^(-(1/2 : Real)) +
        (Ct*K (m+1))*(T^(m+1)*(N : Real)^((1/2 : Real)-((m+1 : Nat) : Real))) := by
      nlinarith
    _ <= (N : Real)^(1/2 : Real)/T + C*(N : Real)^(-(1/2 : Real)) +
        C*(T^(m+1)*(N : Real)^((1/2 : Real)-((m+1 : Nat) : Real))) := by
      gcongr
    _ = _ := by ring

/-- An explicit ceiling cutoff makes the actual-zero Dirichlet sum uniformly small. -/
theorem nontrivial_zero_dirichlet_sum_small {delta : Real}
    (hd0 : 0 < delta) (hd1 : delta <= 1/2) :
    Exists fun C : Real => 1 <= C /\
      forall (T : Real) (s : Complex), 1 <= T -> Zeta23.IsNontrivialZero s ->
      (1/2 : Real) <= s.re -> T <= abs s.im -> abs s.im <= 2*T ->
      norm ((Finset.range (Nat.ceil (T^(1+delta)))).sum
        (fun n => ((n+1 : Nat) : Complex)^(-s))) <= C*T^(-(1/4 : Real)) := by
  let hm := exists_nat_gt (2/delta)
  let m : Nat := hm.choose
  have hm2 : (2 : Real) < delta*(m : Real) := by
    have h := mul_lt_mul_of_pos_left hm.choose_spec hd0
    have he : delta*(2/delta) = 2 := by field_simp
    rw [he] at h
    exact h
  have hm1 : 1 <= m := by
    by_contra h
    have he : m = 0 := by omega
    rw [he, Nat.cast_zero, mul_zero] at hm2
    norm_num at hm2
  have hmR : (1 : Real) <= m := by exact_mod_cast hm1
  let hC := nontrivial_zero_euler_norm_bound m hm1
  let C : Real := hC.choose
  have hC1 : 1 <= C := hC.choose_spec.1
  refine Exists.intro (2+2*C) (And.intro (by linarith) ?_)
  intro T s hT hs hsig ht0 ht1
  have hT0 : 0 < T := by linarith
  let q : Real := T^(1+delta)
  let N : Nat := Nat.ceil q
  have hq0 : 0 < q := Real.rpow_pos_of_pos hT0 _
  have hq1 : 1 <= q := Real.one_le_rpow hT (by linarith)
  have hqT : T <= q := by
    calc
      _ = T^(1 : Real) := (Real.rpow_one T).symm
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hNlo : q <= (N : Real) := Nat.le_ceil q
  have hNhi : (N : Real) <= 2*q := by
    have h := Nat.ceil_lt_add_one hq0.le
    change (N : Real) < q+1 at h
    linarith
  have hN : 0 < N := Nat.ceil_pos.mpr hq0
  have hN0 : (0 : Real) < N := by exact_mod_cast hN
  have hn := hC.choose_spec.2 N T s hN hT (hqT.trans hNlo) hs hsig ht0 ht1
  have hPole : (N : Real)^(1/2 : Real)/T <= 2*T^(-(1/4 : Real)) := by
    have htwo : (2 : Real)^(1/2 : Real) <= 2 := by
      calc
        _ <= (2 : Real)^(1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = _ := Real.rpow_one 2
    have hpow : (N : Real)^(1/2 : Real) <= 2*q^(1/2 : Real) := by
      calc
        _ <= (2*q)^(1/2 : Real) :=
          Real.rpow_le_rpow hN0.le hNhi (by norm_num)
        _ = (2 : Real)^(1/2 : Real)*q^(1/2 : Real) :=
          Real.mul_rpow (by norm_num) hq0.le
        _ <= _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hq0.le _)
    calc
      _ <= (2*q^(1/2 : Real))/T := div_le_div_of_nonneg_right hpow hT0.le
      _ = 2*T^((1+delta)*(1/2 : Real)-1) := by
        dsimp [q]
        rw [<- Real.rpow_mul hT0.le, Real.rpow_sub hT0, Real.rpow_one]
        ring
      _ <= _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) (by norm_num)
  have hSmall : (N : Real)^(-(1/2 : Real)) <= T^(-(1/4 : Real)) := by
    calc
      _ <= q^(-(1/2 : Real)) := Real.rpow_le_rpow_of_nonpos hq0 hNlo (by norm_num)
      _ = T^((1+delta)*(-(1/2 : Real))) := by
        dsimp [q]
        rw [<- Real.rpow_mul hT0.le]
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hRem : T^(m+1)*(N : Real)^((1/2 : Real)-((m+1 : Nat) : Real)) <=
      T^(-(1/4 : Real)) := by
    have hp : (1/2 : Real)-((m+1 : Nat) : Real) <= 0 := by
      push_cast
      linarith
    calc
      _ <= T^(m+1)*q^((1/2 : Real)-((m+1 : Nat) : Real)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hq0 hNlo hp)
          (pow_nonneg hT0.le _)
      _ = T^(((m+1 : Nat) : Real)+(1+delta)*((1/2 : Real)-((m+1 : Nat) : Real))) := by
        dsimp [q]
        rw [<- Real.rpow_natCast T (m+1), <- Real.rpow_mul hT0.le,
          <- Real.rpow_add hT0]
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hT (by
        push_cast
        nlinarith)
  change norm ((Finset.range N).sum (fun n => ((n+1 : Nat) : Complex)^(-s))) <=
    (2+2*C)*T^(-(1/4 : Real))
  calc
    _ <= (N : Real)^(1/2 : Real)/T + C*(N : Real)^(-(1/2 : Real)) +
        C*T^(m+1)*(N : Real)^((1/2 : Real)-((m+1 : Nat) : Real)) := hn
    _ <= 2*T^(-(1/4 : Real))+C*T^(-(1/4 : Real))+C*T^(-(1/4 : Real)) := by
      have h1 := mul_le_mul_of_nonneg_left hSmall (show 0 <= C by linarith)
      have h2 := mul_le_mul_of_nonneg_left hRem (show 0 <= C by linarith)
      nlinarith
    _ = _ := by ring

end RobinBV.Sieve
