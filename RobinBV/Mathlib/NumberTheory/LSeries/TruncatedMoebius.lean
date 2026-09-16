/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.Convolution
import RobinBV.Mathlib.NumberTheory.DivisorSubpower

/-!
# Finite Mobius convolution and a Dirichlet-polynomial alternative

Finite support supplies all L-series convergence hypotheses. Both rectangular
cutoffs survive in the convolution coefficients; the coefficients through
the smaller cutoff cancel by Mobius inversion. The resulting exact residual
identity gives a large-polynomial alternative, with a proved power-height
threshold when the full Dirichlet sum is bounded by C*T^(-1/4).

No zeta-zero, zero-density, or prime-count assumption is part of this module.
The coefficient bounds include both the exact divisor-count majorant and
an explicit subpower majorant uniform in both cutoffs.
-/

set_option autoImplicit false

namespace LSeries

/-- A cutoff sequence has an L-series sum given by its finite support. -/
theorem hasSum_cutoff (f : Nat -> Complex) (N : Nat) (s : Complex) :
    LSeriesHasSum (fun n => if n <= N then f n else 0) s
      ((Finset.range (N+1)).sum (fun n => LSeries.term f s n)) := by
  have hfinite : HasSum
      (LSeries.term (fun n => if n <= N then f n else 0) s)
      ((Finset.range (N+1)).sum
        (fun n => LSeries.term (fun k => if k <= N then f k else 0) s n)) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      have hcut : Not (n <= N) := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
      simp only [LSeries.term, if_neg hcut, zero_div, ite_self])
  have he : (Finset.range (N+1)).sum
      (fun n => LSeries.term (fun k => if k <= N then f k else 0) s n) =
      (Finset.range (N+1)).sum (fun n => LSeries.term f s n) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hcut : n <= N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    simp only [LSeries.term, if_pos hcut]
  rw [he] at hfinite
  exact hfinite

/-- The rectangular convolution vanishes beyond the product cutoff. -/
theorem convolution_cutoff_eq_zero (f g : Nat -> Complex) {H L n : Nat}
    (hn : H*L < n) :
    LSeries.convolution (fun d => if d <= H then f d else 0)
      (fun k => if k <= L then g k else 0) n = 0 := by
  rw [LSeries.convolution_def]
  dsimp only
  apply Finset.sum_eq_zero
  intro p hp
  have hpEq := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases hd : p.1 <= H
  next =>
    by_cases hk : p.2 <= L
    next =>
      have hmul := Nat.mul_le_mul hd hk
      rw [hpEq] at hmul
      omega
    next =>
      simp only [if_neg hk, mul_zero]
  next =>
    simp only [if_neg hd, zero_mul]

/-- Two finite L-series sums multiply by exact finite Dirichlet convolution. -/
theorem sum_cutoff_mul_eq_convolution (f g : Nat -> Complex) (H L : Nat) (s : Complex) :
    ((Finset.range (H+1)).sum (fun n => LSeries.term f s n))*
      ((Finset.range (L+1)).sum (fun n => LSeries.term g s n)) =
      (Finset.range (H*L+1)).sum (fun n =>
        LSeries.term (LSeries.convolution (fun d => if d <= H then f d else 0)
          (fun k => if k <= L then g k else 0)) s n) := by
  have hProd := (hasSum_cutoff f H s).convolution (hasSum_cutoff g L s)
  have hFinite : LSeriesHasSum
      (LSeries.convolution (fun d => if d <= H then f d else 0)
        (fun k => if k <= L then g k else 0)) s
      ((Finset.range (H*L+1)).sum (fun n =>
        LSeries.term (LSeries.convolution (fun d => if d <= H then f d else 0)
          (fun k => if k <= L then g k else 0)) s n)) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      have hbig : H*L < n := by
        have hnot : Not (n <= H*L) := by
          simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
        omega
      have hn0 : Not (n = 0) := by omega
      rw [LSeries.term_of_ne_zero hn0, convolution_cutoff_eq_zero f g hbig, zero_div])
  exact HasSum.unique hProd hFinite

/-- Remove the zero term and express the finite L-series as complex powers. -/
theorem sum_term_eq_sum_cpow (f : Nat -> Complex) (N : Nat) (s : Complex) :
    (Finset.range (N+1)).sum (fun n => LSeries.term f s n) =
      (Finset.range N).sum (fun j => f (j+1)*((j+1 : Nat) : Complex)^(-s)) := by
  rw [Finset.sum_range_succ', LSeries.term_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [LSeries.term_of_ne_zero (by omega), Complex.cpow_neg, div_eq_mul_inv]

/-- The complex Mobius coefficients with both rectangular cutoff conditions. -/
noncomputable def truncatedMoebius (H L : Nat) : Nat -> Complex :=
  LSeries.convolution
    (fun d => if d <= H then (ArithmeticFunction.moebius d : Complex) else 0)
    (fun k => if k <= L then 1 else 0)

/-- The exact divisor formula retains both the divisor and quotient cutoffs. -/
theorem truncatedMoebius_divisors (H L n : Nat) :
    truncatedMoebius H L n =
      n.divisors.sum (fun d =>
        if d <= H /\ n/d <= L then (ArithmeticFunction.moebius d : Complex) else 0) := by
  rw [truncatedMoebius, LSeries.convolution_def]
  dsimp only
  rw [Nat.sum_divisorsAntidiagonal (fun d k =>
    (if d <= H then (ArithmeticFunction.moebius d : Complex) else 0)*
      (if k <= L then (1 : Complex) else 0))]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h1 : d <= H <;> by_cases h2 : n/d <= L <;> simp [h1, h2]

/-- Mobius cancellation is exact through the smaller cutoff. -/
theorem truncatedMoebius_eq_unit {H L n : Nat} (hn : n <= H) (hHL : H <= L) :
    truncatedMoebius H L n = if n = 1 then 1 else 0 := by
  rw [truncatedMoebius_divisors]
  have hsum : n.divisors.sum (fun d =>
        if d <= H /\ n/d <= L then (ArithmeticFunction.moebius d : Complex) else 0) =
      n.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex)) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdH : d <= H := (Nat.divisor_le hd).trans hn
    have hqL : n/d <= L := (Nat.div_le_self n d).trans (hn.trans hHL)
    simp only [hdH, hqL, and_self, if_true]
  rw [hsum]
  have he := congrArg (fun f : ArithmeticFunction Complex => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := Complex))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using he

/-- The complex cast of a Mobius value has norm at most one. -/
theorem norm_moebius_complex_le_one (n : Nat) :
    norm (ArithmeticFunction.moebius n : Complex) <= 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num

/-- Every truncated coefficient is bounded by the full divisor count. -/
theorem norm_truncatedMoebius_le (H L n : Nat) :
    norm (truncatedMoebius H L n) <= (n.divisors.card : Real) := by
  rw [truncatedMoebius_divisors]
  calc
    norm (n.divisors.sum (fun d =>
        if d <= H /\ n/d <= L then (ArithmeticFunction.moebius d : Complex) else 0)) <=
        n.divisors.sum (fun d =>
          norm (if d <= H /\ n/d <= L then (ArithmeticFunction.moebius d : Complex) else 0)) :=
      norm_sum_le _ _
    _ <= n.divisors.sum (fun _ => (1 : Real)) := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases h : d <= H /\ n/d <= L
      next =>
        rw [if_pos h]
        exact norm_moebius_complex_le_one d
      next =>
        simp only [if_neg h, norm_zero, zero_le_one]
    _ = (n.divisors.card : Real) := by simp

/-- The entire low coefficient packet contributes exactly one. -/
theorem sum_truncatedMoebius_prefix {H L : Nat} (hH : 1 <= H) (hHL : H <= L)
    (s : Complex) :
    (Finset.range (H+1)).sum (fun n => LSeries.term (truncatedMoebius H L) s n) = 1 := by
  rw [Finset.sum_eq_single 1]
  next =>
    rw [LSeries.term_of_ne_zero (by omega), truncatedMoebius_eq_unit hH hHL]
    simp
  next =>
    intro n hn hn1
    have hnH : n <= H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    simp only [LSeries.term, truncatedMoebius_eq_unit hnH hHL, if_neg hn1,
      zero_div, ite_self]
  next =>
    intro hn
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

/-- The full mollified sum is one plus the retained residual interval. -/
theorem sum_moebius_mul_sum_eq_one_add {H L : Nat} (hH : 1 <= H) (hHL : H <= L)
    (s : Complex) :
    ((Finset.range H).sum (fun j =>
        (ArithmeticFunction.moebius (j+1) : Complex)*((j+1 : Nat) : Complex)^(-s)))*
      ((Finset.range L).sum (fun j => ((j+1 : Nat) : Complex)^(-s))) =
      1+(Finset.range (H*L-H)).sum (fun j =>
        truncatedMoebius H L (H+j+1)*((H+j+1 : Nat) : Complex)^(-s)) := by
  have hHLmul : H <= H*L := by
    have hL : 1 <= L := hH.trans hHL
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left H hL
  calc
    _ = ((Finset.range (H+1)).sum (fun n =>
        LSeries.term (fun d => (ArithmeticFunction.moebius d : Complex)) s n))*
        ((Finset.range (L+1)).sum (fun n => LSeries.term (fun _ => 1) s n)) := by
      rw [sum_term_eq_sum_cpow, sum_term_eq_sum_cpow]
      simp only [one_mul]
    _ = (Finset.range (H*L+1)).sum (fun n =>
        LSeries.term (truncatedMoebius H L) s n) :=
      sum_cutoff_mul_eq_convolution _ _ H L s
    _ = 1+(Finset.range (H*L-H)).sum (fun j =>
        LSeries.term (truncatedMoebius H L) s (H+1+j)) := by
      rw [show H*L+1 = (H+1)+(H*L-H) by omega, Finset.sum_range_add,
        sum_truncatedMoebius_prefix hH hHL]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [show H+1+j = H+j+1 by omega, LSeries.term_of_ne_zero (by omega),
        Complex.cpow_neg, div_eq_mul_inv]

/-- For nonnegative real part, the mollifier norm is at most its length. -/
theorem norm_sum_moebius_cpow_le (H : Nat) {s : Complex} (hs : 0 <= s.re) :
    norm ((Finset.range H).sum (fun j =>
      (ArithmeticFunction.moebius (j+1) : Complex)*((j+1 : Nat) : Complex)^(-s))) <=
      (H : Real) := by
  calc
    _ <= (Finset.range H).sum (fun j =>
        norm ((ArithmeticFunction.moebius (j+1) : Complex)*
          ((j+1 : Nat) : Complex)^(-s))) := norm_sum_le _ _
    _ <= (Finset.range H).sum (fun _ => (1 : Real)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      have hbase : 0 < ((j+1 : Nat) : Real) := by positivity
      have hbase1 : 1 <= ((j+1 : Nat) : Real) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
      have he := Complex.norm_cpow_eq_rpow_re_of_pos hbase (-s)
      simp only [Complex.ofReal_natCast, Complex.neg_re] at he
      have hpow : norm (((j+1 : Nat) : Complex)^(-s)) <= 1 := by
        rw [he]
        calc
          _ <= ((j+1 : Nat) : Real)^(0 : Real) :=
            Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith)
          _ = 1 := Real.rpow_zero _
      exact (mul_le_mul (norm_moebius_complex_le_one (j+1)) hpow
        (norm_nonneg _) (by norm_num)).trans (by norm_num)
    _ = (H : Real) := by simp

/-- A small full sum forces a long-sum or residual large value. -/
theorem dirichlet_sum_small_or_moebius_residual_large
    {H L M : Nat} (hH : 1 <= H) (hHL : H <= L) (hLM : L <= M)
    {s : Complex} (hs : 0 <= s.re) {eta : Real} (_heta : 0 <= eta)
    (hbudget : 4*(H : Real)*eta <= 1)
    (hsmall : norm ((Finset.range M).sum
      (fun j => ((j+1 : Nat) : Complex)^(-s))) <= eta) :
    eta <= norm ((Finset.range (M-L)).sum
      (fun j => ((L+j+1 : Nat) : Complex)^(-s))) \/
    (1 : Real)/2 <= norm ((Finset.range (H*L-H)).sum
      (fun j => truncatedMoebius H L (H+j+1)*((H+j+1 : Nat) : Complex)^(-s))) := by
  by_cases hlarge : eta <= norm ((Finset.range (M-L)).sum
      (fun j => ((L+j+1 : Nat) : Complex)^(-s)))
  next =>
    exact Or.inl hlarge
  next =>
    apply Or.inr
    have htail : norm ((Finset.range (M-L)).sum
        (fun j => ((L+j+1 : Nat) : Complex)^(-s))) <= eta :=
      le_of_lt (lt_of_not_ge hlarge)
    have hsplit : (Finset.range M).sum (fun j => ((j+1 : Nat) : Complex)^(-s)) =
        (Finset.range L).sum (fun j => ((j+1 : Nat) : Complex)^(-s))+
        (Finset.range (M-L)).sum (fun j => ((L+j+1 : Nat) : Complex)^(-s)) := by
      rw [show M = L+(M-L) by omega, Finset.sum_range_add]
      have hcancel : L+(M-L)-L = M-L := by omega
      rw [hcancel]
    have hnormShort : norm ((Finset.range L).sum
        (fun j => ((j+1 : Nat) : Complex)^(-s))) <= 2*eta := by
      have htri := norm_sub_le
        ((Finset.range M).sum (fun j => ((j+1 : Nat) : Complex)^(-s)))
        ((Finset.range (M-L)).sum (fun j => ((L+j+1 : Nat) : Complex)^(-s)))
      rw [hsplit, add_sub_cancel_right] at htri
      rw [hsplit] at hsmall
      linarith
    have hproduct := sum_moebius_mul_sum_eq_one_add hH hHL s
    have hprodNorm : norm
        (((Finset.range H).sum (fun j =>
          (ArithmeticFunction.moebius (j+1) : Complex)*((j+1 : Nat) : Complex)^(-s)))*
          ((Finset.range L).sum (fun j => ((j+1 : Nat) : Complex)^(-s)))) <=
        (1 : Real)/2 := by
      rw [norm_mul]
      calc
        _ <= (H : Real)*(2*eta) := mul_le_mul (norm_sum_moebius_cpow_le H hs)
          hnormShort (norm_nonneg _) (Nat.cast_nonneg H)
        _ <= (1 : Real)/2 := by linarith
    rw [hproduct] at hprodNorm
    have htri := norm_sub_le
      (1+(Finset.range (H*L-H)).sum (fun j =>
        truncatedMoebius H L (H+j+1)*((H+j+1 : Nat) : Complex)^(-s)))
      ((Finset.range (H*L-H)).sum (fun j =>
        truncatedMoebius H L (H+j+1)*((H+j+1 : Nat) : Complex)^(-s)))
    rw [add_sub_cancel_right, norm_one] at htri
    linarith

/-- Power-height cutoffs satisfy the full detection budget above an explicit threshold. -/
theorem dirichlet_sum_height_or_moebius_residual_large
    {C T a b : Real} (hC : 1 <= C) (hb : 0 < b) (hba : b < a) (ha : a < 1)
    (hbSmall : b < (1/8 : Real))
    (hT : max 1 (max (C^(1/((1/4 : Real)-2*b))) ((4 : Real)^(1/b))) <= T)
    {s : Complex} (hs : 0 <= s.re)
    (hsmall : norm ((Finset.range (Nat.floor T)).sum
      (fun j => ((j+1 : Nat) : Complex)^(-s))) <= C*T^(-(1/4 : Real))) :
    T^(-2*b) <= norm ((Finset.range (Nat.floor T-Nat.floor (T^a))).sum
      (fun j => ((Nat.floor (T^a)+j+1 : Nat) : Complex)^(-s))) \/
    (1 : Real)/2 <= norm
      ((Finset.range (Nat.floor (T^b)*Nat.floor (T^a)-Nat.floor (T^b))).sum
        (fun j => truncatedMoebius (Nat.floor (T^b)) (Nat.floor (T^a))
          (Nat.floor (T^b)+j+1)*((Nat.floor (T^b)+j+1 : Nat) : Complex)^(-s))) := by
  have hT1 : 1 <= T := (le_max_left _ _).trans hT
  have hTC : C^(1/((1/4 : Real)-2*b)) <= T :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hT
  have hT4 : (4 : Real)^(1/b) <= T :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hTnonneg : 0 <= T := le_of_lt hTpos
  have hq : 0 < (1/4 : Real)-2*b := by linarith
  have hcancel (x r : Real) (hx : 0 <= x) (hr : 0 < r) :
      (x^(1/r))^r = x := by
    rw [<- Real.rpow_mul hx]
    rw [show (1/r)*r = 1 by field_simp]
    exact Real.rpow_one x
  have hCpow : C <= T^((1/4 : Real)-2*b) := by
    have hh := Real.rpow_le_rpow
      (Real.rpow_nonneg (le_trans zero_le_one hC) _) hTC (le_of_lt hq)
    rw [hcancel C _ (le_trans zero_le_one hC) hq] at hh
    exact hh
  have h4pow : (4 : Real) <= T^b := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : Real) <= 4) _)
      hT4 (le_of_lt hb)
    rw [hcancel 4 b (by norm_num) hb] at hh
    exact hh
  have hH : 1 <= Nat.floor (T^b) :=
    Nat.le_floor (by simpa only [Nat.cast_one] using Real.one_le_rpow hT1 (le_of_lt hb))
  have hHL : Nat.floor (T^b) <= Nat.floor (T^a) :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hT1 (le_of_lt hba))
  have hLM : Nat.floor (T^a) <= Nat.floor T := by
    apply Nat.floor_mono
    calc
      T^a <= T^(1 : Real) := Real.rpow_le_rpow_of_exponent_le hT1 (le_of_lt ha)
      _ = T := Real.rpow_one T
  have heta : 0 <= T^(-2*b) := Real.rpow_nonneg hTnonneg _
  have hsmallEta : norm ((Finset.range (Nat.floor T)).sum
      (fun j => ((j+1 : Nat) : Complex)^(-s))) <= T^(-2*b) := by
    calc
      _ <= C*T^(-(1/4 : Real)) := hsmall
      _ <= T^((1/4 : Real)-2*b)*T^(-(1/4 : Real)) :=
        mul_le_mul_of_nonneg_right hCpow (Real.rpow_nonneg hTnonneg _)
      _ = T^(-2*b) := by
        rw [<- Real.rpow_add hTpos]
        congr 1
        ring
  have hbudget : 4*(Nat.floor (T^b) : Real)*T^(-2*b) <= 1 := by
    calc
      _ <= 4*T^b*T^(-2*b) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hTnonneg b))
          (by norm_num)) heta
      _ = 4*T^(-b) := by
        rw [mul_assoc, <- Real.rpow_add hTpos]
        congr 1
        congr 1
        ring
      _ <= T^b*T^(-b) := mul_le_mul_of_nonneg_right h4pow
        (Real.rpow_nonneg hTnonneg _)
      _ = 1 := by rw [<- Real.rpow_add hTpos, add_neg_cancel, Real.rpow_zero]
  exact dirichlet_sum_small_or_moebius_residual_large hH hHL hLM hs heta hbudget hsmallEta

/-- The retained signed coefficients have an explicit subpower majorant,
uniformly in both cutoff parameters and every positive index. -/
theorem norm_truncatedMoebius_le_rpow_explicit (H L : Nat) {n : Nat}
    (hn : Not (n = 0)) {epsilon : Real} (hepsilon : 0 < epsilon) :
    norm (truncatedMoebius H L n) <=
      (((2 : Real)^epsilon)/((2 : Real)^epsilon-1))^(Nat.ceil ((2 : Real)^(1/epsilon)))*
        (n : Real)^epsilon :=
  (norm_truncatedMoebius_le H L n).trans (Nat.card_divisors_le_rpow_explicit hepsilon hn)

end LSeries
