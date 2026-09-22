/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMVTAsymptotic

/-!
# Source-sized threshold for the global Linnik VMVT induction

This module proves that the finite prime-band and scale cutoffs in the explicit
VMVT recurrence are dominated by a single source-sized exponential cutoff.
Consequently, the small-input branch contributes
`exp (C * r * k^2 * log k)` rather than a full trivial-power coefficient.
This is the quantitative threshold input for the sharp global coefficient
induction and its later zero-density consumer.
-/

theorem nat_le_two_pow_for_linnikVMVT (n : Nat) : n <= 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpow : 0 < 2 ^ n := pow_pos (by omega) n
      omega

theorem linnikVMVT_band_base_le_power
    (Y0 k : Nat) (hk : 2 <= k) :
    max (max k Y0) (32 * (k ^ 3 + 1) ^ 2) <= k ^ max 13 Y0 := by
  have hkPos : 0 < k := by omega
  have hCPos : 0 < max 13 Y0 := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hkC : k <= k ^ max 13 Y0 := Nat.le_pow hCPos
  have hY : Y0 <= k ^ max 13 Y0 := by
    calc
      Y0 <= 2 ^ Y0 := nat_le_two_pow_for_linnikVMVT Y0
      _ <= k ^ Y0 := Nat.pow_le_pow_left hk Y0
      _ <= k ^ max 13 Y0 := Nat.pow_le_pow_right hkPos (le_max_right _ _)
  have hk3One : 1 <= k ^ 3 := pow_pos hkPos 3
  have hsum : k ^ 3 + 1 <= k ^ 4 := by
    calc
      k ^ 3 + 1 <= 2 * k ^ 3 := by omega
      _ <= k * k ^ 3 := Nat.mul_le_mul_right (k ^ 3) hk
      _ = k ^ 4 := by ring
  have hsq : (k ^ 3 + 1) ^ 2 <= k ^ 8 := by
    calc
      (k ^ 3 + 1) ^ 2 <= (k ^ 4) ^ 2 := Nat.pow_le_pow_left hsum 2
      _ = k ^ 8 := by ring
  have h32 : 32 <= k ^ 5 := by
    calc
      32 = 2 ^ 5 := by norm_num
      _ <= k ^ 5 := Nat.pow_le_pow_left hk 5
  have hpoly : 32 * (k ^ 3 + 1) ^ 2 <= k ^ 13 := by
    calc
      32 * (k ^ 3 + 1) ^ 2 <= k ^ 5 * k ^ 8 := Nat.mul_le_mul h32 hsq
      _ = k ^ 13 := by ring
  have hpolyC : 32 * (k ^ 3 + 1) ^ 2 <= k ^ max 13 Y0 :=
    hpoly.trans (Nat.pow_le_pow_right hkPos (le_max_left _ _))
  exact max_le (max_le hkC hY) hpolyC

theorem linnikVMVT_scale_log_le
    (k r : Nat) (hk : 2 <= k) (hkr : k <= r) :
    (k : Real) * Real.log (4 * (r : Real) * k) <=
      6 * (r : Real) * Real.log k := by
  have hkPos : 0 < k := by omega
  have hrPos : 0 < r := lt_of_lt_of_le hkPos hkr
  have hkReal : 0 < (k : Real) := by exact_mod_cast hkPos
  have hrReal : 0 < (r : Real) := by exact_mod_cast hrPos
  have hkrReal : (k : Real) <= r := by exact_mod_cast hkr
  have hlogkNonneg : 0 <= Real.log (k : Real) :=
    (Real.log_pos (by exact_mod_cast hk)).le
  have hlogTwoLe : Real.log 2 <= Real.log (k : Real) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  have hlogHalf : (1 : Real) / 2 <= Real.log (k : Real) := by
    have hsource := Real.log_two_gt_d9
    norm_num at hsource
    linarith
  have hOne : (1 : Real) <= 2 * Real.log (k : Real) := by linarith
  have hk2Nat : 4 <= k ^ 2 := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ <= k ^ 2 := Nat.pow_le_pow_left hk 2
  have hk2 : (4 : Real) <= (k : Real) ^ 2 := by exact_mod_cast hk2Nat
  have hlogFour : Real.log 4 <= 2 * Real.log (k : Real) := by
    calc
      Real.log 4 <= Real.log ((k : Real) ^ 2) :=
        Real.log_le_log (by norm_num) hk2
      _ = 2 * Real.log (k : Real) := by
        rw [Real.log_pow]
        norm_num
  have hratioPos : 0 < (r : Real) / k := div_pos hrReal hkReal
  have hratio := Real.log_le_sub_one_of_pos hratioPos
  have hfactor : (r : Real) = ((r : Real) / k) * k := by
    field_simp
  have hlogR : Real.log (r : Real) <=
      Real.log (k : Real) + ((r : Real) / k - 1) := by
    calc
      Real.log (r : Real) = Real.log (((r : Real) / k) * k) :=
        congrArg Real.log hfactor
      _ = Real.log ((r : Real) / k) + Real.log (k : Real) :=
        Real.log_mul (ne_of_gt hratioPos) (ne_of_gt hkReal)
      _ <= ((r : Real) / k - 1) + Real.log (k : Real) :=
        _root_.add_le_add hratio le_rfl
      _ = Real.log (k : Real) + ((r : Real) / k - 1) := by ring
  have hlogProduct : Real.log (4 * (r : Real) * k) =
      (Real.log 4 + Real.log (r : Real)) + Real.log (k : Real) := by
    rw [Real.log_mul (by positivity : Not (4 * (r : Real) = 0))
      (ne_of_gt hkReal)]
    rw [Real.log_mul (by norm_num : Not ((4 : Real) = 0)) (ne_of_gt hrReal)]
  have hraw : (k : Real) * Real.log (4 * (r : Real) * k) <=
      4 * (k : Real) * Real.log k + r - k := by
    calc
      (k : Real) * Real.log (4 * (r : Real) * k) =
          (k : Real) * ((Real.log 4 + Real.log r) + Real.log k) := by
        rw [hlogProduct]
      _ <= (k : Real) *
          ((2 * Real.log k +
            (Real.log k + ((r : Real) / k - 1))) + Real.log k) :=
        mul_le_mul_of_nonneg_left
          (_root_.add_le_add
            (_root_.add_le_add hlogFour hlogR) le_rfl) (by positivity)
      _ = 4 * (k : Real) * Real.log k + r - k := by
        field_simp
        ring
  have hmain : 4 * (k : Real) * Real.log k <=
      4 * (r : Real) * Real.log k := by
    nlinarith [mul_le_mul_of_nonneg_right hkrReal hlogkNonneg]
  have htail0 : (r : Real) - k <= r := by linarith
  have htail1 : (r : Real) <= 2 * r * Real.log k := by
    nlinarith [mul_le_mul_of_nonneg_left hOne
      (show 0 <= (r : Real) by positivity)]
  linarith

theorem nat_power_cast_eq_exp_for_linnikVMVT
    (a m : Nat) (ha : 0 < a) :
    ((a ^ m : Nat) : Real) = Real.exp ((m : Real) * Real.log a) := by
  calc
    ((a ^ m : Nat) : Real) = (a : Real) ^ m := by norm_cast
    _ = (Real.exp (Real.log (a : Real))) ^ m := by
      rw [Real.exp_log (by exact_mod_cast ha)]
    _ = Real.exp ((m : Real) * Real.log a) := (Real.exp_nat_mul _ _).symm

theorem linnikVMVT_band_threshold_nat_le_power
    (Y0 k r : Nat) (hk : 2 <= k) :
    (max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)) ^ k <=
      k ^ (max 13 Y0 * max k r) := by
  have hkPos : 0 < k := by omega
  calc
    (max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)) ^ k <=
        (k ^ max 13 Y0) ^ k :=
      Nat.pow_le_pow_left (linnikVMVT_band_base_le_power Y0 k hk) k
    _ = k ^ (max 13 Y0 * k) := by ring
    _ <= k ^ (max 13 Y0 * max k r) :=
      Nat.pow_le_pow_right hkPos
        (Nat.mul_le_mul_left (max 13 Y0) (le_max_left _ _))

theorem linnikVMVT_band_threshold_le_exp
    (Y0 k r : Nat) (hk : 2 <= k) :
    ((max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)) ^ k : Nat) <=
      Real.exp ((max 13 Y0 : Real) *
        max (k : Real) (r : Real) * Real.log k) := by
  have hkPos : 0 < k := by omega
  have hnat := linnikVMVT_band_threshold_nat_le_power Y0 k r hk
  calc
    (((max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)) ^ k : Nat) : Real) <=
        ((k ^ (max 13 Y0 * max k r) : Nat) : Real) := by exact_mod_cast hnat
    _ = Real.exp (((max 13 Y0 * max k r : Nat) : Real) * Real.log k) :=
      nat_power_cast_eq_exp_for_linnikVMVT k (max 13 Y0 * max k r) hkPos
    _ = Real.exp ((max 13 Y0 : Real) *
        max (k : Real) (r : Real) * Real.log k) := by
      congr 1
      push_cast
      norm_cast

theorem linnikVMVT_scale_threshold_le_exp
    (Y0 k r : Nat) (hk : 2 <= k) (hr : 0 < r) :
    (((4 * (r - 1) * k) ^ k : Nat) : Real) <=
      Real.exp ((max 13 Y0 : Real) *
        max (k : Real) (r : Real) * Real.log k) := by
  have hkPos : 0 < k := by omega
  have hkReal : 0 < (k : Real) := by exact_mod_cast hkPos
  have hlogk : 0 <= Real.log (k : Real) :=
    (Real.log_pos (by exact_mod_cast hk)).le
  have hC6Nat : 6 <= max 13 Y0 :=
    le_trans (by norm_num) (le_max_left _ _)
  by_cases hrk : r <= k
  next =>
    have hs : r - 1 <= k := (Nat.sub_le r 1).trans hrk
    have hk2Nat : 4 <= k ^ 2 := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ <= k ^ 2 := Nat.pow_le_pow_left hk 2
    have hbase : 4 * (r - 1) * k <= k ^ 4 := by
      calc
        4 * (r - 1) * k <= k ^ 2 * k * k :=
          Nat.mul_le_mul (Nat.mul_le_mul hk2Nat hs) le_rfl
        _ = k ^ 4 := by ring
    have hC4Nat : 4 <= max 13 Y0 := le_trans (by norm_num) hC6Nat
    have hexp : 4 * k <= max 13 Y0 * max k r :=
      Nat.mul_le_mul hC4Nat (le_max_left _ _)
    have hnat : (4 * (r - 1) * k) ^ k <=
        k ^ (max 13 Y0 * max k r) := by
      calc
        (4 * (r - 1) * k) ^ k <= (k ^ 4) ^ k :=
          Nat.pow_le_pow_left hbase k
        _ = k ^ (4 * k) := by ring
        _ <= k ^ (max 13 Y0 * max k r) :=
          Nat.pow_le_pow_right hkPos hexp
    calc
      (((4 * (r - 1) * k) ^ k : Nat) : Real) <=
          ((k ^ (max 13 Y0 * max k r) : Nat) : Real) := by exact_mod_cast hnat
      _ = Real.exp (((max 13 Y0 * max k r : Nat) : Real) * Real.log k) :=
        nat_power_cast_eq_exp_for_linnikVMVT k (max 13 Y0 * max k r) hkPos
      _ = Real.exp ((max 13 Y0 : Real) *
          max (k : Real) (r : Real) * Real.log k) := by
        congr 1
        push_cast
        norm_cast
  next =>
    have hkr : k <= r := Nat.le_of_lt (Nat.lt_of_not_ge hrk)
    have hbase : 4 * (r - 1) * k <= 4 * r * k :=
      Nat.mul_le_mul_right k (Nat.mul_le_mul_left 4 (Nat.sub_le r 1))
    have hpow : (4 * (r - 1) * k) ^ k <= (4 * r * k) ^ k :=
      Nat.pow_le_pow_left hbase k
    have hbigPos : 0 < 4 * r * k := by positivity
    have hlog := linnikVMVT_scale_log_le k r hk hkr
    have hkrReal : (k : Real) <= r := by exact_mod_cast hkr
    have hmax : max (k : Real) (r : Real) = r := max_eq_right hkrReal
    have hC6 : (6 : Real) <= (max 13 Y0 : Real) := by exact_mod_cast hC6Nat
    have hcoef : 6 * (r : Real) <= (max 13 Y0 : Real) * r := by
      nlinarith
    have hexp : 6 * (r : Real) * Real.log k <=
        (max 13 Y0 : Real) * max (k : Real) (r : Real) * Real.log k := by
      rw [hmax]
      exact mul_le_mul_of_nonneg_right hcoef hlogk
    calc
      (((4 * (r - 1) * k) ^ k : Nat) : Real) <=
          (((4 * r * k) ^ k : Nat) : Real) := by exact_mod_cast hpow
      _ = Real.exp ((k : Real) * Real.log (4 * r * k)) := by
        simpa using nat_power_cast_eq_exp_for_linnikVMVT (4 * r * k) k hbigPos
      _ <= Real.exp (6 * (r : Real) * Real.log k) :=
        Real.exp_le_exp.mpr hlog
      _ <= Real.exp ((max 13 Y0 : Real) *
          max (k : Real) (r : Real) * Real.log k) :=
        Real.exp_le_exp.mpr hexp

theorem linnikVMVTStepThreshold_le_exp
    (Y0 k r : Nat) (hk : 2 <= k) (hr : 0 < r) :
    (linnikVMVTStepThreshold Y0 k (r - 1) : Real) <=
      Real.exp ((max 13 Y0 : Real) *
        max (k : Real) (r : Real) * Real.log k) := by
  have hband := linnikVMVT_band_threshold_le_exp Y0 k r hk
  have hscale := linnikVMVT_scale_threshold_le_exp Y0 k r hk hr
  simp only [linnikVMVTStepThreshold, Nat.cast_max]
  exact max_le hband hscale

theorem linnikVMVT_source_small_argument_le
    (Y0 k r X : Nat) (hk : 2 <= k) (hr : 0 < r) (hX : 0 < X)
    (hsmall : X < linnikVMVTStepThreshold Y0 k (r - 1)) :
    (Finset.vinogradovMeanValue k (k * r) X : Real) <=
      Real.exp ((max 13 Y0 : Real) * (r : Real) *
          (k : Real) ^ 2 * Real.log k) *
        (X : Real) ^ linnikVMVTExponent k r := by
  have hXthreshold : (X : Real) <=
      (linnikVMVTStepThreshold Y0 k (r - 1) : Real) := by
    exact_mod_cast Nat.le_of_lt hsmall
  have hXupper := hXthreshold.trans
    (linnikVMVTStepThreshold_le_exp Y0 k r hk hr)
  have hdefect := linnikVMVT_defect_rpow_le_exp k r X
    (max 13 Y0 : Real) hk hr hX (by positivity) hXupper
  exact linnikVMVT_small_argument_of_defect_bound k r X
    (Real.exp ((max 13 Y0 : Real) * (r : Real) *
      (k : Real) ^ 2 * Real.log k)) hX hdefect
