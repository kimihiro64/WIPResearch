/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational-approximation geometry for Linnik's technical inequality

This module begins the source proof of Lemma 24.6.  It defines distance to the
nearest integer using Mathlib's exact rounding operation, proves its Lipschitz
lower estimate, proves the sharp `1/q` lower bound for a nonzero reduced
rational residue, and combines both facts on the half block `2*n <= q` under
the source hypothesis `|alpha-a/q| <= q^-2`.
-/

noncomputable def linnikNearestIntDist (x : Real) : Real :=
  abs (x - (round x : Real))

theorem linnik_sum_Ioo_inv_sq_le_two (q : Nat) :
    Finset.sum (Finset.Ioo 0 (q + 1))
      (fun i => Inv.inv ((i : Real) ^ 2)) <= 2 := by
  calc
    Finset.sum (Finset.Ioo 0 (q + 1))
        (fun i => Inv.inv ((i : Real) ^ 2)) <=
        (2 : Real) / (((0 : Nat) : Real) + 1) :=
          sum_Ioo_inv_sq_le 0 (q + 1)
    _ = 2 := by norm_num

noncomputable def linnikCenteredQuotient (n q : Nat) : Int :=
  round ((n : Real) / q)

noncomputable def linnikCenteredRemainder (n q : Nat) : Int :=
  (n : Int) - linnikCenteredQuotient n q * (q : Int)

theorem linnik_centered_decomposition (n q : Nat) :
    (n : Int) = linnikCenteredQuotient n q * (q : Int) +
      linnikCenteredRemainder n q := by
  unfold linnikCenteredRemainder
  ring

theorem linnik_centered_remainder_half (n q : Nat) (hq : 0 < q) :
    2 * (linnikCenteredRemainder n q).natAbs <= q := by
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hround := abs_sub_round ((n : Real) / q)
  have hreal : abs ((n : Real) - (linnikCenteredQuotient n q : Real) * q) <=
      (q : Real) / 2 := by
    calc
      abs ((n : Real) - (linnikCenteredQuotient n q : Real) * q) =
          abs (((n : Real) / q - (linnikCenteredQuotient n q : Real)) * q) := by
            congr 1
            field_simp
      _ = abs ((n : Real) / q - (linnikCenteredQuotient n q : Real)) * q := by
        rw [abs_mul, abs_of_pos hqReal]
      _ <= (1 / 2) * (q : Real) := by
        gcongr
        simpa [linnikCenteredQuotient] using hround
      _ = (q : Real) / 2 := by ring
  have hcast : ((linnikCenteredRemainder n q).natAbs : Real) =
      abs ((n : Real) - (linnikCenteredQuotient n q : Real) * q) := by
    unfold linnikCenteredRemainder
    rw [Nat.cast_natAbs, Int.cast_abs]
    push_cast
    rfl
  have hdouble : (2 * (linnikCenteredRemainder n q).natAbs : Nat) <= q := by
    exact_mod_cast (show (2 : Real) *
      (linnikCenteredRemainder n q).natAbs <= q by rw [hcast]; linarith)
  exact hdouble

theorem linnikNearestIntDist_nonneg (x : Real) :
    0 <= linnikNearestIntDist x := by
  unfold linnikNearestIntDist
  positivity

theorem linnikNearestIntDist_le_half (x : Real) :
    linnikNearestIntDist x <= 1 / 2 := by
  exact abs_sub_round x

theorem linnikNearestIntDist_add_int (x : Real) (z : Int) :
    linnikNearestIntDist (x + z) = linnikNearestIntDist x := by
  unfold linnikNearestIntDist
  rw [round_add_intCast]
  congr 1
  push_cast
  ring

theorem linnikNearestIntDist_neg (x : Real) :
    linnikNearestIntDist (-x) = linnikNearestIntDist x := by
  have hforward := round_le (-x) (-(round x))
  have hbackward := round_le x (-(round (-x)))
  unfold linnikNearestIntDist
  have hforward' : abs (-x - (round (-x) : Real)) <=
      abs (x - (round x : Real)) := by
    simpa only [Int.cast_neg, abs_neg, neg_sub_neg, abs_sub_comm] using hforward
  have hbackward' : abs (x - (round x : Real)) <=
      abs (-x - (round (-x) : Real)) := by
    have heq : abs (x - (-(round (-x)) : Int)) =
        abs (-x - (round (-x) : Real)) := by
      push_cast
      rw [show -x - (round (-x) : Real) =
        -(x + (round (-x) : Real)) by ring, abs_neg]
      ring
    rw [<- heq]
    exact hbackward
  exact le_antisymm hforward' hbackward'

theorem linnikNearestIntDist_sub_abs_le (x y : Real) :
    linnikNearestIntDist y - abs (y - x) <= linnikNearestIntDist x := by
  have hround := round_le y (round x)
  have htriangle : abs (y - (round x : Real)) <=
      abs (y - x) + abs (x - (round x : Real)) := by
    calc
      abs (y - (round x : Real)) =
          abs ((y - x) + (x - (round x : Real))) := by ring_nf
      _ <= abs (y - x) + abs (x - (round x : Real)) := abs_add_le _ _
  unfold linnikNearestIntDist
  linarith

theorem linnikNearestIntDist_ge_half_of_approx
    (x y d : Real)
    (hy : d <= linnikNearestIntDist y)
    (hxy : abs (x - y) <= d / 2) :
    d / 2 <= linnikNearestIntDist x := by
  have hlip := linnikNearestIntDist_sub_abs_le x y
  have habs : abs (y - x) = abs (x - y) := by rw [abs_sub_comm]
  rw [habs] at hlip
  linarith

theorem linnikNearestIntDist_nat_div_ge
    (a n q : Nat) (hq : 0 < q) (hn : 0 < n) (hnq : n < q)
    (hcop : Nat.Coprime a q) :
    1 / (q : Real) <=
      linnikNearestIntDist (((n * a : Nat) : Real) / q) := by
  have hnotdvd : Not (Dvd.dvd q (n * a)) := by
    intro hdvd
    have hdvd' : Dvd.dvd q (a * n) := by simpa [Nat.mul_comm] using hdvd
    have hqn : Dvd.dvd q n := (hcop.symm.dvd_mul_left).1 hdvd'
    have hle : q <= n := Nat.le_of_dvd hn hqn
    omega
  have hmodNe : Not ((n * a) % q = 0) := by
    intro hzero
    exact hnotdvd (Nat.dvd_of_mod_eq_zero hzero)
  have hmodPos : 0 < (n * a) % q := Nat.pos_of_ne_zero hmodNe
  have hmodLt : (n * a) % q < q := Nat.mod_lt _ hq
  have hmin : 1 <= min ((n * a) % q) (q - (n * a) % q) := by
    omega
  unfold linnikNearestIntDist
  rw [abs_sub_round_div_natCast_eq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hmin

theorem linnikNearestIntDist_approx_rational_half
    (alpha : Real) (a n q : Nat)
    (hq : 0 < q) (hn : 0 < n) (hnHalf : 2 * n <= q)
    (hcop : Nat.Coprime a q)
    (happrox : abs (alpha - (a : Real) / q) <= 1 / (q : Real) ^ 2) :
    1 / (2 * (q : Real)) <= linnikNearestIntDist ((n : Real) * alpha) := by
  have hnq : n < q := by omega
  have hrational := linnikNearestIntDist_nat_div_ge a n q hq hn hnq hcop
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hnHalfReal : 2 * (n : Real) <= (q : Real) := by exact_mod_cast hnHalf
  have hfrac : (n : Real) / (q : Real) ^ 2 <= 1 / (2 * (q : Real)) := by
    have hid : 1 / (2 * (q : Real)) - (n : Real) / (q : Real) ^ 2 =
        ((q : Real) - 2 * (n : Real)) / (2 * (q : Real) ^ 2) := by
      field_simp
    apply sub_nonneg.mp
    rw [hid]
    positivity
  have hxy : abs ((n : Real) * alpha - ((n * a : Nat) : Real) / q) <=
      (1 / (q : Real)) / 2 := by
    have heq : (n : Real) * alpha - ((n * a : Nat) : Real) / q =
        (n : Real) * (alpha - (a : Real) / q) := by
      push_cast
      ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : Real) <= n)]
    calc
      (n : Real) * abs (alpha - (a : Real) / q) <=
          (n : Real) * (1 / (q : Real) ^ 2) := by gcongr
      _ = (n : Real) / (q : Real) ^ 2 := by ring
      _ <= 1 / (2 * (q : Real)) := hfrac
      _ = (1 / (q : Real)) / 2 := by ring
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (linnikNearestIntDist_ge_half_of_approx
      ((n : Real) * alpha) (((n * a : Nat) : Real) / q)
      (1 / (q : Real)) hrational hxy)

/-- The half-block estimate in the centered integer parametrization used by
the source proof.  Both positive and negative offsets are covered, and zero is
excluded explicitly because its rational residue has distance zero. -/
theorem linnikNearestIntDist_approx_rational_centered
    (alpha : Real) (a q : Nat) (v : Int)
    (hq : 0 < q) (hv : Not (v = 0)) (hvHalf : 2 * v.natAbs <= q)
    (hcop : Nat.Coprime a q)
    (happrox : abs (alpha - (a : Real) / q) <= 1 / (q : Real) ^ 2) :
    1 / (2 * (q : Real)) <= linnikNearestIntDist ((v : Real) * alpha) := by
  cases v with
  | ofNat n =>
      have hn : 0 < n := by
        by_contra hnpos
        have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
        apply hv
        simp only [hnzero, Int.ofNat_eq_coe, Nat.cast_zero]
      have hhalf : 2 * n <= q := by simpa using hvHalf
      simpa using linnikNearestIntDist_approx_rational_half
        alpha a n q hq hn hhalf hcop happrox
  | negSucc n =>
      have hn : 0 < n + 1 := Nat.succ_pos n
      have hhalf : 2 * (n + 1) <= q := by simpa using hvHalf
      have h := linnikNearestIntDist_approx_rational_half
        alpha a (n + 1) q hq hn hhalf hcop happrox
      have heq : ((Int.negSucc n : Int) : Real) * alpha =
          -(((n + 1 : Nat) : Real) * alpha) := by
        push_cast
        ring
      rw [heq, linnikNearestIntDist_neg]
      exact h

/-- The complete arithmetic error in one centered `q`-block.  Rounding
`u*theta` into the rational numerator leaves error at most `1/q`, improving
the floor-based `3/(2q)` envelope used in the published proof. -/
theorem linnik_block_rational_rounding_error
    (alpha theta : Real) (a q u : Nat) (v : Int)
    (hq : 0 < q) (htheta : abs theta <= 1)
    (hvHalf : 2 * v.natAbs <= q)
    (halpha : alpha = (a : Real) / q + theta / (q : Real) ^ 2) :
    abs ((((u * q : Nat) : Int) + v : Int) * alpha -
      ((u * a : Nat) : Real) -
      (((v : Real) * a + (round ((u : Real) * theta) : Real)) / q)) <=
        1 / (q : Real) := by
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hvCast : abs (v : Real) = (v.natAbs : Real) := by
    rw [<- Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hvHalfReal : 2 * (v.natAbs : Real) <= (q : Real) := by
    exact_mod_cast hvHalf
  have hround := abs_sub_round ((u : Real) * theta)
  have heq :
      ((((u * q : Nat) : Int) + v : Int) : Real) * alpha -
          ((u * a : Nat) : Real) -
          (((v : Real) * a + (round ((u : Real) * theta) : Real)) / q) =
        (((u : Real) * theta - (round ((u : Real) * theta) : Real)) / q) +
          ((v : Real) * theta / (q : Real) ^ 2) := by
    rw [halpha]
    push_cast
    field_simp
    ring
  rw [heq]
  calc
    abs ((((u : Real) * theta - (round ((u : Real) * theta) : Real)) / q) +
        ((v : Real) * theta / (q : Real) ^ 2)) <=
        abs (((u : Real) * theta - (round ((u : Real) * theta) : Real)) / q) +
          abs ((v : Real) * theta / (q : Real) ^ 2) := abs_add_le _ _
    _ = abs ((u : Real) * theta - (round ((u : Real) * theta) : Real)) / q +
        (abs (v : Real) * abs theta) / (q : Real) ^ 2 := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hqReal, abs_of_pos (sq_pos_of_pos hqReal)]
    _ <= (1 / 2) / (q : Real) +
        ((v.natAbs : Real) * 1) / (q : Real) ^ 2 := by
      apply add_le_add
      next => exact div_le_div_of_nonneg_right hround hqReal.le
      next =>
        apply div_le_div_of_nonneg_right _ (sq_nonneg (q : Real))
        rw [hvCast]
        exact mul_le_mul_of_nonneg_left htheta (by positivity)
    _ <= (1 / 2) / (q : Real) + (1 / 2) / (q : Real) := by
      have hid : (v.natAbs : Real) / (q : Real) ^ 2 <=
          (1 / 2) / (q : Real) := by
        have hdiff : (1 / 2) / (q : Real) -
            (v.natAbs : Real) / (q : Real) ^ 2 =
            ((q : Real) - 2 * (v.natAbs : Real)) /
              (2 * (q : Real) ^ 2) := by
          field_simp
        apply sub_nonneg.mp
        rw [hdiff]
        positivity
      apply add_le_add le_rfl
      simpa using hid
    _ = 1 / (q : Real) := by ring
