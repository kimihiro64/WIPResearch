/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikUniformPrimeBand

/-!
# Exponent bookkeeping for Linnik's VMVT recurrence

This module formalizes the exponent identities used after the exact finite
prime-band recurrence.  The error exponent is

`eta(k,r) = k^2 / 2 * (1 - 1/k)^r`,

and the full mean-value exponent is

`E(k,r) = 2*r*k - k*(k+1)/2 + eta(k,r)`.

The joint modulus calculation retains the complete exponent `k^2 - eta`.
Keeping that term intact is what makes the prime-band loss compatible with
the next induction exponent; replacing it by separate coarse modulus bounds
would destroy the cancellation used by the analytic consumer.
-/

noncomputable def linnikVMVTEta (k r : Nat) : Real :=
  (k : Real) ^ 2 / 2 * (1 - 1 / (k : Real)) ^ r

noncomputable def linnikVMVTExponent (k r : Nat) : Real :=
  2 * (r : Real) * k - (k : Real) * (k + 1) / 2 + linnikVMVTEta k r

/-- The error exponent contracts by `1 - 1/k` at each induction step. -/
theorem linnikVMVTEta_succ (k r : Nat) :
    linnikVMVTEta k (r + 1) =
      (1 - 1 / (k : Real)) * linnikVMVTEta k r := by
  simp only [linnikVMVTEta, pow_succ]
  ring

/-- The initial full exponent is exactly `k`. -/
theorem linnikVMVTExponent_one (k : Nat) (hk : 0 < k) :
    linnikVMVTExponent k 1 = k := by
  simp only [linnikVMVTExponent, linnikVMVTEta, Nat.cast_one, pow_one]
  field_simp
  ring

/-- Exact joint modulus exponent after inserting the preceding VMVT term. -/
theorem linnikVMVT_joint_modulus_exponent (k s : Nat) :
    2 * (k : Real) * s + (k : Real) * (k - 1) / 2 -
        linnikVMVTExponent k s =
      (k : Real) ^ 2 - linnikVMVTEta k s := by
  simp only [linnikVMVTExponent]
  ring

/-- The algebraic induction step for the complete VMVT exponent. -/
theorem linnikVMVTExponent_step (k s : Nat) (hk : 0 < k) :
    (k : Real) + linnikVMVTExponent k s +
        (((k : Real) ^ 2 - linnikVMVTEta k s) / k) =
      linnikVMVTExponent k (s + 1) := by
  simp only [linnikVMVTExponent]
  rw [linnikVMVTEta_succ k s]
  push_cast
  field_simp
  ring

/-- The error exponent is nonnegative for every positive degree. -/
theorem linnikVMVTEta_nonneg (k r : Nat) (hk : 0 < k) :
    0 <= linnikVMVTEta k r := by
  have hkReal : 0 < (k : Real) := by exact_mod_cast hk
  have hkOne : (1 : Real) <= k := by exact_mod_cast hk
  have hdiv : 1 / (k : Real) <= 1 :=
    (one_div_le hkReal zero_lt_one).2 (by simpa using hkOne)
  have hbase : 0 <= 1 - 1 / (k : Real) := sub_nonneg.mpr hdiv
  simp only [linnikVMVTEta]
  positivity

/-- The geometric error never exceeds its initial half-square value. -/
theorem linnikVMVTEta_le_half_square (k r : Nat) (hk : 0 < k) :
    linnikVMVTEta k r <= (k : Real) ^ 2 / 2 := by
  have hkReal : 0 < (k : Real) := by exact_mod_cast hk
  have hkOne : (1 : Real) <= k := by exact_mod_cast hk
  have hdiv : 1 / (k : Real) <= 1 :=
    (one_div_le hkReal zero_lt_one).2 (by simpa using hkOne)
  have hbaseNonneg : 0 <= 1 - 1 / (k : Real) := sub_nonneg.mpr hdiv
  have hbaseLe : 1 - 1 / (k : Real) <= 1 :=
    sub_le_self 1 (by positivity)
  have hpow : (1 - 1 / (k : Real)) ^ r <= 1 := by
    induction r with
    | zero => simp
    | succ r ih =>
        rw [pow_succ]
        have hpowNonneg : 0 <= (1 - 1 / (k : Real)) ^ r :=
          pow_nonneg hbaseNonneg r
        nlinarith
  simp only [linnikVMVTEta]
  nlinarith [sq_nonneg (k : Real)]

/-- The full exponent is no larger than the raw `2*r*k` moment exponent. -/
theorem linnikVMVTExponent_le_main (k r : Nat) (hk : 0 < k) :
    linnikVMVTExponent k r <= 2 * (r : Real) * k := by
  have heta := linnikVMVTEta_le_half_square k r hk
  simp only [linnikVMVTExponent]
  nlinarith [sq_nonneg (k : Real)]

/-- Positivity of the full exponent on every positive induction level. -/
theorem linnikVMVTExponent_succ_nonneg (k s : Nat) (hk : 0 < k) :
    0 <= linnikVMVTExponent k (s + 1) := by
  induction s with
  | zero =>
      rw [Nat.zero_add]
      rw [linnikVMVTExponent_one k hk]
      positivity
  | succ s ih =>
      have hkReal : 0 < (k : Real) := by exact_mod_cast hk
      have heta := linnikVMVTEta_le_half_square k (s + 1) hk
      have hnum : 0 <= (k : Real) ^ 2 - linnikVMVTEta k (s + 1) := by
        nlinarith [sq_nonneg (k : Real)]
      have hdiv : 0 <= ((k : Real) ^ 2 - linnikVMVTEta k (s + 1)) / k :=
        div_nonneg hnum hkReal.le
      have hstep := linnikVMVTExponent_step k (s + 1) hk
      have hsum :
          0 <= (k : Real) + linnikVMVTExponent k (s + 1) +
            (((k : Real) ^ 2 - linnikVMVTEta k (s + 1)) / k) := by
        positivity
      simpa [Nat.succ_eq_add_one] using hsum.trans_eq hstep

/-- Positivity of the full exponent for every positive induction level. -/
theorem linnikVMVTExponent_nonneg (k r : Nat) (hk : 0 < k) (hr : 0 < r) :
    0 <= linnikVMVTExponent k r := by
  choose s hs using Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [hs]
  exact linnikVMVTExponent_succ_nonneg k s hk

/-- Casting the natural triangular exponent loses no factor of two. -/
theorem natCast_mul_sub_one_div_two (k : Nat) :
    ((k * (k - 1) / 2 : Nat) : Real) =
      (k : Real) * ((k : Real) - 1) / 2 := by
  cases k with
  | zero => norm_num
  | succ k =>
      rw [Nat.cast_div (Nat.two_dvd_mul_sub_one (k + 1)) (by norm_num)]
      push_cast
      simp

/-- Exact real-power factorization used before bounding a prime modulus. -/
theorem real_mul_one_add_div_rpow_factorization
    (X p A E : Real) (hX : 0 < X) (hp : 0 < p) :
    p ^ A * (1 + X / p) ^ E =
      X ^ E * p ^ (A - E) * (1 + p / X) ^ E := by
  have hfactor : 0 <= 1 + p / X := by positivity
  have hidentity : 1 + X / p = (X / p) * (1 + p / X) := by
    field_simp
    ring
  rw [hidentity]
  rw [Real.mul_rpow (div_nonneg hX.le hp.le) hfactor]
  rw [Real.div_rpow hX.le hp.le E]
  rw [Real.rpow_sub hp A E]
  ring

/-- The exact source recurrence factorization with joint exponent `k^2-eta`. -/
theorem linnikVMVT_joint_rpow_factorization
    (X p : Real) (hX : 0 < X) (hp : 0 < p) (k s : Nat) :
    p ^ (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) *
        (1 + X / p) ^ linnikVMVTExponent k s =
      X ^ linnikVMVTExponent k s *
        p ^ ((k : Real) ^ 2 - linnikVMVTEta k s) *
          (1 + p / X) ^ linnikVMVTExponent k s := by
  calc
    p ^ (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) *
          (1 + X / p) ^ linnikVMVTExponent k s =
        X ^ linnikVMVTExponent k s *
          p ^ (2 * (k : Real) * s + (k : Real) * (k - 1) / 2 -
            linnikVMVTExponent k s) *
            (1 + p / X) ^ linnikVMVTExponent k s :=
      real_mul_one_add_div_rpow_factorization X p _ _ hX hp
    _ = X ^ linnikVMVTExponent k s *
          p ^ ((k : Real) ^ 2 - linnikVMVTEta k s) *
            (1 + p / X) ^ linnikVMVTExponent k s := by
      rw [linnikVMVT_joint_modulus_exponent]

/-- The retained modulus exponent is nonnegative. -/
theorem linnikVMVT_net_modulus_exponent_nonneg
    (k s : Nat) (hk : 0 < k) :
    0 <= (k : Real) ^ 2 - linnikVMVTEta k s := by
  have heta := linnikVMVTEta_le_half_square k s hk
  nlinarith [sq_nonneg (k : Real)]

/-- The retained modulus exponent is at most `k^2`. -/
theorem linnikVMVT_net_modulus_exponent_le_square
    (k s : Nat) (hk : 0 < k) :
    (k : Real) ^ 2 - linnikVMVTEta k s <= (k : Real) ^ 2 := by
  have heta := linnikVMVTEta_nonneg k s hk
  linarith

/-- The natural integer root is bounded by the corresponding real power. -/
theorem natCast_nthRoot_le_rpow
    (k X : Nat) (hk : 0 < k) (hX : 0 < X) :
    (Nat.nthRoot k X : Real) <= (X : Real) ^ (1 / (k : Real)) := by
  have hkReal : 0 < (k : Real) := by exact_mod_cast hk
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  have hpowNat : Nat.nthRoot k X ^ k <= X :=
    Nat.pow_nthRoot_le (Or.inl hk.ne')
  have hpowReal : (Nat.nthRoot k X : Real) ^ k <= (X : Real) := by
    exact_mod_cast hpowNat
  have hmono := Real.rpow_le_rpow
    (show 0 <= (Nat.nthRoot k X : Real) ^ k by positivity)
    hpowReal (show 0 <= 1 / (k : Real) by positivity)
  calc
    (Nat.nthRoot k X : Real) =
        (Nat.nthRoot k X : Real) ^ (1 : Real) := by
          rw [Real.rpow_one]
    _ = (Nat.nthRoot k X : Real) ^
          ((k : Real) * (1 / (k : Real))) := by
          congr 1
          field_simp
    _ = ((Nat.nthRoot k X : Real) ^ (k : Real)) ^
          (1 / (k : Real)) :=
        Real.rpow_mul (by positivity) _ _
    _ = ((Nat.nthRoot k X : Real) ^ k) ^
          (1 / (k : Real)) := by
        rw [Real.rpow_natCast]
    _ <= (X : Real) ^ (1 / (k : Real)) := hmono

/-- Sharp dyadic bound for the complete joint modulus exponent. -/
theorem linnikVMVT_prime_modulus_rpow_le
    (k s X p : Nat) (hk : 0 < k) (hX : 0 < X)
    (hp : p <= 2 * Nat.nthRoot k X) :
    (p : Real) ^ ((k : Real) ^ 2 - linnikVMVTEta k s) <=
      (2 : Real) ^ ((k : Real) ^ 2) *
        (X : Real) ^ (((k : Real) ^ 2 - linnikVMVTEta k s) / k) := by
  let q : Real := (k : Real) ^ 2 - linnikVMVTEta k s
  change (p : Real) ^ q <= (2 : Real) ^ ((k : Real) ^ 2) *
    (X : Real) ^ (q / (k : Real))
  have hqNonneg : 0 <= q :=
    linnikVMVT_net_modulus_exponent_nonneg k s hk
  have hqUpper : q <= (k : Real) ^ 2 :=
    linnikVMVT_net_modulus_exponent_le_square k s hk
  have hroot := natCast_nthRoot_le_rpow k X hk hX
  have hpReal : (p : Real) <=
      2 * (X : Real) ^ (1 / (k : Real)) := by
    have hpCast : (p : Real) <= 2 * (Nat.nthRoot k X : Real) := by
      exact_mod_cast hp
    exact hpCast.trans (mul_le_mul_of_nonneg_left hroot (by norm_num))
  have hbase := Real.rpow_le_rpow (by positivity : (0 : Real) <= p)
    hpReal hqNonneg
  have htwo := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : Real) <= 2) hqUpper
  have hXpowNonneg :
      0 <= (X : Real) ^ (q / (k : Real)) :=
    Real.rpow_nonneg (by positivity) _
  calc
    (p : Real) ^ q <=
        (2 * (X : Real) ^ (1 / (k : Real))) ^ q := hbase
    _ = (2 : Real) ^ q * (X : Real) ^ (q / (k : Real)) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by positivity) _)]
      rw [(Real.rpow_mul (show 0 <= (X : Real) by positivity)
        (1 / (k : Real)) q).symm]
      congr 2
      ring
    _ <= (2 : Real) ^ ((k : Real) ^ 2) *
        (X : Real) ^ (q / (k : Real)) :=
      mul_le_mul_of_nonneg_right htwo hXpowNonneg

/-- The residual `(1+p/X)^E` factor costs at most `e` on the large branch. -/
theorem linnikVMVT_one_add_modulus_rpow_le_exp_one
    (k s X p : Nat) (hk : 0 < k) (hs : 0 < s) (hX : 0 < X)
    (hp : p <= 2 * Nat.nthRoot k X)
    (hscale : 4 * (s : Real) * k *
      (X : Real) ^ (1 / (k : Real)) <= X) :
    (1 + (p : Real) / X) ^ linnikVMVTExponent k s <= Real.exp 1 := by
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  have hE0 := linnikVMVTExponent_nonneg k s hk hs
  have hE := linnikVMVTExponent_le_main k s hk
  have hroot := natCast_nthRoot_le_rpow k X hk hX
  have hpReal : (p : Real) <=
      2 * (X : Real) ^ (1 / (k : Real)) := by
    have hpCast : (p : Real) <= 2 * (Nat.nthRoot k X : Real) := by
      exact_mod_cast hp
    exact hpCast.trans (mul_le_mul_of_nonneg_left hroot (by norm_num))
  have hproduct : linnikVMVTExponent k s * p <=
      4 * (s : Real) * k * (X : Real) ^ (1 / (k : Real)) := by
    have hmul := mul_le_mul hE hpReal
      (by positivity : (0 : Real) <= p)
      (by positivity : (0 : Real) <= 2 * s * k)
    nlinarith
  have hratio : linnikVMVTExponent k s * ((p : Real) / X) <= 1 := by
    calc
      linnikVMVTExponent k s * ((p : Real) / X) =
          (linnikVMVTExponent k s * p) / X := by ring
      _ <= (X : Real) / X :=
        div_le_div_of_nonneg_right (hproduct.trans hscale) hXReal.le
      _ = 1 := by field_simp
  have hlog : Real.log (1 + (p : Real) / X) <= (p : Real) / X := by
    have hpos : 0 < 1 + (p : Real) / X := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    nlinarith
  rw [Real.rpow_def_of_pos (by positivity)]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hlog hE0
  nlinarith

/-- The explicit natural large-branch cutoff implies the residual scale bound. -/
theorem linnikVMVT_scale_of_pow_le
    (k s X : Nat) (hk : 2 <= k) (hs : 0 < s)
    (hthreshold : (4 * s * k) ^ k <= X) :
    4 * (s : Real) * k * (X : Real) ^ (1 / (k : Real)) <= X := by
  have hkPos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hbasePos : 0 < 4 * s * k := by positivity
  have hpowPos : 0 < (4 * s * k) ^ k := pow_pos hbasePos k
  have hX : 0 < X := lt_of_lt_of_le hpowPos hthreshold
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  have hXOne : (1 : Real) <= X := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hX.ne')
  have hrootNat : 4 * s * k <= Nat.nthRoot k X :=
    (Nat.le_nthRoot_iff hkPos.ne').mpr hthreshold
  have hrootReal := natCast_nthRoot_le_rpow k X hkPos hX
  have hbaseRoot : (4 * s * k : Nat) <=
      (X : Real) ^ (1 / (k : Real)) := by
    push_cast
    have hcast : (4 * s * k : Real) <= Nat.nthRoot k X := by
      exact_mod_cast hrootNat
    exact hcast.trans hrootReal
  have hexponent : (2 : Real) / k <= 1 := by
    have hkReal : (2 : Real) <= k := by exact_mod_cast hk
    have hkRealPos : 0 < (k : Real) := by positivity
    exact (div_le_one hkRealPos).mpr hkReal
  have hrootSq :
      (X : Real) ^ (1 / (k : Real)) *
          (X : Real) ^ (1 / (k : Real)) <= X := by
    calc
      (X : Real) ^ (1 / (k : Real)) *
          (X : Real) ^ (1 / (k : Real)) =
        (X : Real) ^ (1 / (k : Real) + 1 / (k : Real)) :=
          (Real.rpow_add hXReal _ _).symm
      _ = (X : Real) ^ ((2 : Real) / k) := by
        congr 1
        ring
      _ <= (X : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hXOne hexponent
      _ = X := Real.rpow_one _
  calc
    4 * (s : Real) * k * (X : Real) ^ (1 / (k : Real)) =
        (4 * s * k : Nat) * (X : Real) ^ (1 / (k : Real)) := by
      push_cast
      ring
    _ <= (X : Real) ^ (1 / (k : Real)) *
        (X : Real) ^ (1 / (k : Real)) :=
      mul_le_mul_of_nonneg_right hbaseRoot (Real.rpow_nonneg hXReal.le _)
    _ <= X := hrootSq

/-- The complete large-branch prime term, with every modulus factor eliminated. -/
theorem linnikVMVT_joint_prime_term_le
    (k s X p : Nat) (hk : 2 <= k) (hs : 0 < s) (hpPos : 0 < p)
    (hthreshold : (4 * s * k) ^ k <= X)
    (hp : p <= 2 * Nat.nthRoot k X) :
    (X : Real) ^ (k : Real) *
        ((p : Real) ^
            (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) *
          (1 + (X : Real) / p) ^ linnikVMVTExponent k s) <=
      Real.exp 1 * (2 : Real) ^ ((k : Real) ^ 2) *
        (X : Real) ^ linnikVMVTExponent k (s + 1) := by
  have hkPos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hbasePos : 0 < 4 * s * k := by positivity
  have hpowPos : 0 < (4 * s * k) ^ k := pow_pos hbasePos k
  have hX : 0 < X := lt_of_lt_of_le hpowPos hthreshold
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  let E := linnikVMVTExponent k s
  let q := (k : Real) ^ 2 - linnikVMVTEta k s
  have hfactor := linnikVMVT_joint_rpow_factorization
    (X : Real) (p : Real) hXReal (by exact_mod_cast hpPos) k s
  have hpBound := linnikVMVT_prime_modulus_rpow_le
    k s X p hkPos hX hp
  have hscale := linnikVMVT_scale_of_pow_le k s X hk hs hthreshold
  have hresidual := linnikVMVT_one_add_modulus_rpow_le_exp_one
    k s X p hkPos hs hX hp hscale
  have hfirst :
      (p : Real) ^ q * (1 + (p : Real) / X) ^ E <=
        ((2 : Real) ^ ((k : Real) ^ 2) *
          (X : Real) ^ (q / (k : Real))) *
            (1 + (p : Real) / X) ^ E :=
    mul_le_mul_of_nonneg_right hpBound (Real.rpow_nonneg (by positivity) _)
  have hsecond :
      ((2 : Real) ^ ((k : Real) ^ 2) *
          (X : Real) ^ (q / (k : Real))) *
            (1 + (p : Real) / X) ^ E <=
        ((2 : Real) ^ ((k : Real) ^ 2) *
          (X : Real) ^ (q / (k : Real))) * Real.exp 1 :=
    mul_le_mul_of_nonneg_left hresidual (by positivity)
  have hprime := hfirst.trans hsecond
  have hpow :
      (X : Real) ^ (k : Real) * (X : Real) ^ E *
          (X : Real) ^ (q / (k : Real)) =
        (X : Real) ^ linnikVMVTExponent k (s + 1) := by
    calc
      (X : Real) ^ (k : Real) * (X : Real) ^ E *
          (X : Real) ^ (q / (k : Real)) =
        (X : Real) ^ ((k : Real) + E) *
          (X : Real) ^ (q / (k : Real)) := by
            rw [Real.rpow_add hXReal]
      _ = (X : Real) ^ ((k : Real) + E + q / (k : Real)) :=
        (Real.rpow_add hXReal _ _).symm
      _ = (X : Real) ^ linnikVMVTExponent k (s + 1) := by
        congr 1
        exact linnikVMVTExponent_step k s hkPos
  calc
    (X : Real) ^ (k : Real) *
        ((p : Real) ^
            (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) *
          (1 + (X : Real) / p) ^ E) =
      ((X : Real) ^ (k : Real) * (X : Real) ^ E) *
        ((p : Real) ^ q * (1 + (p : Real) / X) ^ E) := by
          rw [hfactor]
          ring
    _ <= ((X : Real) ^ (k : Real) * (X : Real) ^ E) *
        (((2 : Real) ^ ((k : Real) ^ 2) *
          (X : Real) ^ (q / (k : Real))) * Real.exp 1) :=
      mul_le_mul_of_nonneg_left hprime (by positivity)
    _ = Real.exp 1 * (2 : Real) ^ ((k : Real) ^ 2) *
        (X : Real) ^ linnikVMVTExponent k (s + 1) := by
      calc
        ((X : Real) ^ (k : Real) * (X : Real) ^ E) *
            (((2 : Real) ^ ((k : Real) ^ 2) *
              (X : Real) ^ (q / (k : Real))) * Real.exp 1) =
          Real.exp 1 * (2 : Real) ^ ((k : Real) ^ 2) *
            ((X : Real) ^ (k : Real) * (X : Real) ^ E *
              (X : Real) ^ (q / (k : Real))) := by ring
        _ = Real.exp 1 * (2 : Real) ^ ((k : Real) ^ 2) *
            (X : Real) ^ linnikVMVTExponent k (s + 1) := by
          rw [hpow]

/-- Substitute a lower-level VMVT envelope into one complete prime term. -/
theorem linnikVMVT_prime_term_with_induction_le
    (k s X p J : Nat) (A : Real)
    (hk : 2 <= k) (hs : 0 < s) (hpPos : 0 < p) (hA : 0 <= A)
    (hthreshold : (4 * s * k) ^ k <= X)
    (hp : p <= 2 * Nat.nthRoot k X)
    (hJ : (J : Real) <=
      A * (1 + (X : Real) / p) ^ linnikVMVTExponent k s) :
    (X : Real) ^ (k : Real) *
        (p : Real) ^
          (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) * J <=
      A * Real.exp 1 * (2 : Real) ^ ((k : Real) ^ 2) *
        (X : Real) ^ linnikVMVTExponent k (s + 1) := by
  have hterm := linnikVMVT_joint_prime_term_le
    k s X p hk hs hpPos hthreshold hp
  have hnonneg :
      0 <= (X : Real) ^ (k : Real) *
        (p : Real) ^
          (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) := by
    positivity
  calc
    (X : Real) ^ (k : Real) *
        (p : Real) ^
          (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) * J <=
      ((X : Real) ^ (k : Real) *
        (p : Real) ^
          (2 * (k : Real) * s + (k : Real) * (k - 1) / 2)) *
            (A * (1 + (X : Real) / p) ^ linnikVMVTExponent k s) :=
      mul_le_mul_of_nonneg_left hJ hnonneg
    _ = A * ((X : Real) ^ (k : Real) *
        ((p : Real) ^
            (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) *
          (1 + (X : Real) / p) ^ linnikVMVTExponent k s)) := by ring
    _ <= A * (Real.exp 1 * (2 : Real) ^ ((k : Real) ^ 2) *
        (X : Real) ^ linnikVMVTExponent k (s + 1)) :=
      mul_le_mul_of_nonneg_left hterm hA
    _ = A * Real.exp 1 * (2 : Real) ^ ((k : Real) ^ 2) *
        (X : Real) ^ linnikVMVTExponent k (s + 1) := by ring

/-- Cast the exact natural modulus exponent to its real source exponent. -/
theorem natCast_linnik_modulus_power (k s p : Nat) :
    ((p ^ (2 * (k * s) + k * (k - 1) / 2) : Nat) : Real) =
      (p : Real) ^
        (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) := by
  calc
    ((p ^ (2 * (k * s) + k * (k - 1) / 2) : Nat) : Real) =
        (p : Real) ^ (2 * (k * s) + k * (k - 1) / 2) := by
      norm_cast
    _ = (p : Real) ^
        ((2 * (k * s) + k * (k - 1) / 2 : Nat) : Real) :=
      (Real.rpow_natCast _ _).symm
    _ = (p : Real) ^
        (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) := by
      congr 1
      rw [Nat.cast_add, natCast_mul_sub_one_div_two]
      push_cast
      ring

/-- Bound the literal natural summand occurring in the exact recurrence. -/
theorem linnikVMVT_nat_prime_term_with_induction_le
    (k s X p J : Nat) (A : Real)
    (hk : 2 <= k) (hs : 0 < s) (hpPos : 0 < p) (hA : 0 <= A)
    (hthreshold : (4 * s * k) ^ k <= X)
    (hp : p <= 2 * Nat.nthRoot k X)
    (hJ : (J : Real) <=
      A * (1 + (X : Real) / p) ^ linnikVMVTExponent k s) :
    ((p ^ (2 * (k * s)) *
      ((X ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) * J) : Nat) : Real) <=
      (k.factorial : Real) * A * Real.exp 1 *
        (2 : Real) ^ ((k : Real) ^ 2) *
          (X : Real) ^ linnikVMVTExponent k (s + 1) := by
  have hterm := linnikVMVT_prime_term_with_induction_le
    k s X p J A hk hs hpPos hA hthreshold hp hJ
  have hleft :
      ((p ^ (2 * (k * s)) *
        ((X ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) * J) : Nat) : Real) =
        (k.factorial : Real) *
          ((X : Real) ^ (k : Real) *
            (p : Real) ^
              (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) * J) := by
    rw [show ((X : Real) ^ (k : Real)) = (X : Real) ^ k from
      Real.rpow_natCast _ _]
    rw [show (p : Real) ^
        (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) =
      ((p ^ (2 * (k * s) + k * (k - 1) / 2) : Nat) : Real) from
        (natCast_linnik_modulus_power k s p).symm]
    push_cast
    rw [pow_add]
    ring
  rw [hleft]
  calc
    (k.factorial : Real) *
        ((X : Real) ^ (k : Real) *
          (p : Real) ^
            (2 * (k : Real) * s + (k : Real) * (k - 1) / 2) * J) <=
      (k.factorial : Real) *
        (A * Real.exp 1 * (2 : Real) ^ ((k : Real) ^ 2) *
          (X : Real) ^ linnikVMVTExponent k (s + 1)) :=
      mul_le_mul_of_nonneg_left hterm (by positivity)
    _ = (k.factorial : Real) * A * Real.exp 1 *
        (2 : Real) ^ ((k : Real) ^ 2) *
          (X : Real) ^ linnikVMVTExponent k (s + 1) := by ring
