/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMVTPrimeSum

/-!
# Global coefficient induction for the Linnik VMVT estimate

This module combines the explicit large-branch recurrence with the existing
diagonal base case and trivial small-argument estimate.
-/

def linnikVMVTStepThreshold (Y0 k s : Nat) : Nat :=
  max ((max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)) ^ k)
    ((4 * s * k) ^ k)

noncomputable def linnikVMVTStepMultiplier (k : Nat) : Real :=
  4 * ((k ^ 3 + 1 : Nat) : Real) ^ 2 *
    (k.factorial : Real) * Real.exp 1 *
      (2 : Real) ^ ((k : Real) ^ 2)

theorem linnikVMVTStepThreshold_band
    (Y0 k s X : Nat) (hX : linnikVMVTStepThreshold Y0 k s <= X) :
    (max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)) ^ k <= X := by
  exact (le_max_left _ _).trans hX

theorem linnikVMVTStepThreshold_scale
    (Y0 k s X : Nat) (hX : linnikVMVTStepThreshold Y0 k s <= X) :
    (4 * s * k) ^ k <= X := by
  exact (le_max_right _ _).trans hX

/-- Below the step threshold, the trivial count is absorbed by its explicit power. -/
theorem linnikVMVT_small_argument_le
    (Y0 k t r X : Nat) (hk : 0 < k) (hr : 0 < r) (hXPos : 0 < X)
    (hsmall : X < linnikVMVTStepThreshold Y0 k t) :
    (Finset.vinogradovMeanValue k (k * r) X : Real) <=
      (linnikVMVTStepThreshold Y0 k t : Real) ^ (2 * k * r : Nat) *
        (X : Real) ^ linnikVMVTExponent k r := by
  have hcountNat := Finset.vinogradovMeanValue_le_trivial_kr k r X
  have hcount :
      (Finset.vinogradovMeanValue k (k * r) X : Real) <=
        ((X ^ (2 * k * r) : Nat) : Real) := by
    exact_mod_cast hcountNat
  have hpowNat : X ^ (2 * k * r) <=
      linnikVMVTStepThreshold Y0 k t ^ (2 * k * r) :=
    Nat.pow_le_pow_left (Nat.le_of_lt hsmall) _
  have hpow : ((X ^ (2 * k * r) : Nat) : Real) <=
      ((linnikVMVTStepThreshold Y0 k t ^ (2 * k * r) : Nat) : Real) := by
    exact_mod_cast hpowNat
  have hXReal : 1 <= (X : Real) := by exact_mod_cast hXPos
  have hrpow : 1 <= (X : Real) ^ linnikVMVTExponent k r :=
    Real.one_le_rpow hXReal (linnikVMVTExponent_nonneg k r hk hr)
  calc
    (Finset.vinogradovMeanValue k (k * r) X : Real) <=
        ((X ^ (2 * k * r) : Nat) : Real) := hcount
    _ <= ((linnikVMVTStepThreshold Y0 k t ^ (2 * k * r) : Nat) : Real) := hpow
    _ = (linnikVMVTStepThreshold Y0 k t : Real) ^ (2 * k * r : Nat) := by
      norm_cast
    _ <= (linnikVMVTStepThreshold Y0 k t : Real) ^ (2 * k * r : Nat) *
        (X : Real) ^ linnikVMVTExponent k r := by
      calc
        (linnikVMVTStepThreshold Y0 k t : Real) ^ (2 * k * r : Nat) =
            (linnikVMVTStepThreshold Y0 k t : Real) ^ (2 * k * r : Nat) * 1 := by
          ring
        _ <= _ := mul_le_mul_of_nonneg_left hrpow (by positivity)

noncomputable def linnikVMVTDefect (k r : Nat) : Real :=
  2 * (r : Real) * k - linnikVMVTExponent k r

theorem linnikVMVTDefect_eq (k r : Nat) :
    linnikVMVTDefect k r =
      (k : Real) * (k + 1) / 2 - linnikVMVTEta k r := by
  simp only [linnikVMVTDefect, linnikVMVTExponent]
  ring

theorem linnikVMVTDefect_nonneg
    (k r : Nat) (hk : 0 < k) :
    0 <= linnikVMVTDefect k r := by
  have heta := linnikVMVTEta_le_half_square k r hk
  rw [linnikVMVTDefect_eq]
  have hkReal : 0 <= (k : Real) := by positivity
  nlinarith

theorem one_sub_pow_le_nat_mul_one_sub
    (a : Real) (r : Nat) (ha0 : 0 <= a) (ha1 : a <= 1) :
    1 - a ^ r <= (r : Real) * (1 - a) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hpow0 : 0 <= a ^ r := pow_nonneg ha0 r
      have hpow1all : forall n : Nat, a ^ n <= 1 := by
        intro n
        induction n with
        | zero => simp
        | succ n ihn =>
            rw [pow_succ]
            have hpow0' : 0 <= a ^ n := pow_nonneg ha0 n
            nlinarith
      have hpow1 : a ^ r <= 1 := hpow1all r
      have hsub : 0 <= 1 - a := sub_nonneg.mpr ha1
      rw [pow_succ]
      calc
        1 - a ^ r * a = (1 - a ^ r) + a ^ r * (1 - a) := by ring
        _ <= (r : Real) * (1 - a) + 1 * (1 - a) :=
          _root_.add_le_add ih (mul_le_mul_of_nonneg_right hpow1 hsub)
        _ = ((r + 1 : Nat) : Real) * (1 - a) := by
          push_cast
          ring

theorem linnikVMVTDefect_le_square
    (k r : Nat) (hk : 0 < k) :
    linnikVMVTDefect k r <= (k : Real) ^ 2 := by
  have heta := linnikVMVTEta_nonneg k r hk
  have hkOne : (1 : Real) <= k := by exact_mod_cast hk
  rw [linnikVMVTDefect_eq]
  nlinarith [sq_nonneg ((k : Real) - 1)]

theorem linnikVMVTDefect_le_level_mul_degree
    (k r : Nat) (hk : 0 < k) (hr : 0 < r) :
    linnikVMVTDefect k r <= (r : Real) * k := by
  have hkReal : 0 < (k : Real) := by exact_mod_cast hk
  have hkOne : (1 : Real) <= k := by exact_mod_cast hk
  have hrOne : (1 : Real) <= r := by exact_mod_cast hr
  let a : Real := 1 - 1 / (k : Real)
  have hdiv : 1 / (k : Real) <= 1 :=
    (one_div_le hkReal zero_lt_one).2 (by simpa using hkOne)
  have ha0 : 0 <= a := by
    simp only [a]
    exact sub_nonneg.mpr hdiv
  have ha1 : a <= 1 := by
    simp only [a]
    exact sub_le_self 1 (by positivity)
  have hgap0 := one_sub_pow_le_nat_mul_one_sub a r ha0 ha1
  have hgap : 1 - a ^ r <= (r : Real) / k := by
    calc
      1 - a ^ r <= (r : Real) * (1 - a) := hgap0
      _ = (r : Real) / k := by
        simp only [a]
        field_simp
        ring
  have hrepr : linnikVMVTDefect k r =
      (k : Real) / 2 + (k : Real) ^ 2 / 2 * (1 - a ^ r) := by
    rw [linnikVMVTDefect_eq]
    simp only [linnikVMVTEta, a]
    ring
  rw [hrepr]
  have hmul : (k : Real) ^ 2 / 2 * (1 - a ^ r) <=
      (k : Real) ^ 2 / 2 * ((r : Real) / k) :=
    mul_le_mul_of_nonneg_left hgap (by positivity)
  have hsimplify : (k : Real) ^ 2 / 2 * ((r : Real) / k) =
      (r : Real) * k / 2 := by
    field_simp
  rw [hsimplify] at hmul
  nlinarith

theorem max_mul_linnikVMVTDefect_le
    (k r : Nat) (hk : 0 < k) (hr : 0 < r) :
    max (k : Real) (r : Real) * linnikVMVTDefect k r <=
      (r : Real) * (k : Real) ^ 2 := by
  by_cases hkr : k <= r
  next =>
    have hkrReal : (k : Real) <= r := by exact_mod_cast hkr
    rw [max_eq_right hkrReal]
    exact mul_le_mul_of_nonneg_left (linnikVMVTDefect_le_square k r hk)
      (by positivity)
  next =>
    have hrk : r <= k := Nat.le_of_lt (Nat.lt_of_not_ge hkr)
    have hrkReal : (r : Real) <= k := by exact_mod_cast hrk
    rw [max_eq_left hrkReal]
    calc
      (k : Real) * linnikVMVTDefect k r <=
          (k : Real) * ((r : Real) * k) :=
        mul_le_mul_of_nonneg_left
          (linnikVMVTDefect_le_level_mul_degree k r hk hr) (by positivity)
      _ = (r : Real) * (k : Real) ^ 2 := by ring

theorem linnikVMVT_defect_rpow_le_exp
    (k r X : Nat) (C : Real)
    (hk : 2 <= k) (hr : 0 < r) (hX : 0 < X) (hC : 0 <= C)
    (hXupper : (X : Real) <=
      Real.exp (C * max (k : Real) (r : Real) * Real.log k)) :
    (X : Real) ^ linnikVMVTDefect k r <=
      Real.exp (C * (r : Real) * (k : Real) ^ 2 * Real.log k) := by
  have hkPos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hkReal : (1 : Real) < k := by exact_mod_cast hk
  have hlogk : 0 <= Real.log (k : Real) := (Real.log_pos hkReal).le
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  have hlogX : Real.log (X : Real) <=
      C * max (k : Real) (r : Real) * Real.log k := by
    apply (Real.exp_le_exp).mp
    calc
      Real.exp (Real.log (X : Real)) = (X : Real) := Real.exp_log hXReal
      _ <= Real.exp (C * max (k : Real) (r : Real) * Real.log k) := hXupper
  have hdefect := max_mul_linnikVMVTDefect_le k r hkPos hr
  have hscale :
      C * Real.log k *
          (max (k : Real) (r : Real) * linnikVMVTDefect k r) <=
        C * Real.log k * ((r : Real) * (k : Real) ^ 2) :=
    mul_le_mul_of_nonneg_left hdefect (mul_nonneg hC hlogk)
  rw [Real.rpow_def_of_pos hXReal]
  apply Real.exp_le_exp.mpr
  calc
    Real.log (X : Real) * linnikVMVTDefect k r <=
        (C * max (k : Real) (r : Real) * Real.log k) *
          linnikVMVTDefect k r :=
      mul_le_mul_of_nonneg_right hlogX
        (linnikVMVTDefect_nonneg k r hkPos)
    _ = C * Real.log k *
        (max (k : Real) (r : Real) * linnikVMVTDefect k r) := by ring
    _ <= C * Real.log k * ((r : Real) * (k : Real) ^ 2) := hscale
    _ = C * (r : Real) * (k : Real) ^ 2 * Real.log k := by ring

theorem linnikVMVT_rpow_split
    (k r X : Nat) (hX : 0 < X) :
    (X : Real) ^ (2 * (r : Real) * k) =
      (X : Real) ^ linnikVMVTExponent k r *
        (X : Real) ^ linnikVMVTDefect k r := by
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  rw [<- Real.rpow_add hXReal]
  congr 1
  simp only [linnikVMVTDefect]
  ring

/-- Use only the exact exponent defect in the trivial small-input branch. -/
theorem linnikVMVT_small_argument_of_defect_bound
    (k r X : Nat) (H : Real) (hX : 0 < X)
    (hdefect : (X : Real) ^ linnikVMVTDefect k r <= H) :
    (Finset.vinogradovMeanValue k (k * r) X : Real) <=
      H * (X : Real) ^ linnikVMVTExponent k r := by
  have hcountNat := Finset.vinogradovMeanValue_le_trivial_kr k r X
  have hcount :
      (Finset.vinogradovMeanValue k (k * r) X : Real) <=
        ((X ^ (2 * k * r) : Nat) : Real) := by
    exact_mod_cast hcountNat
  have hcast : ((X ^ (2 * k * r) : Nat) : Real) =
      (X : Real) ^ (2 * (r : Real) * k) := by
    calc
      ((X ^ (2 * k * r) : Nat) : Real) =
          (X : Real) ^ (2 * k * r : Nat) := by norm_cast
      _ = (X : Real) ^ ((2 * k * r : Nat) : Real) :=
        (Real.rpow_natCast _ _).symm
      _ = (X : Real) ^ (2 * (r : Real) * k) := by
        congr 1
        push_cast
        ring
  calc
    (Finset.vinogradovMeanValue k (k * r) X : Real) <=
        ((X ^ (2 * k * r) : Nat) : Real) := hcount
    _ = (X : Real) ^ (2 * (r : Real) * k) := hcast
    _ = (X : Real) ^ linnikVMVTExponent k r *
        (X : Real) ^ linnikVMVTDefect k r :=
      linnikVMVT_rpow_split k r X hX
    _ <= (X : Real) ^ linnikVMVTExponent k r * H :=
      mul_le_mul_of_nonneg_left hdefect (by positivity)
    _ = H * (X : Real) ^ linnikVMVTExponent k r := by ring
