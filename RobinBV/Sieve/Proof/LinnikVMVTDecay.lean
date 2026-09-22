/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMVTNormalized

/-!
# Uniform decay of the residual VMVT exponent

The normalized Vinogradov mean-value factor contains the residual power
`(1 - 1 / k) ^ r`.  Theorem 24.12 takes `r` to be a sufficiently large
multiple of `k`.  This module verifies that choice uniformly in `k`: at
`r = k * m` the residual power is at most `exp (-m)`, and one value of `m`
works for every degree `k >= 2` at any prescribed positive tolerance.
-/

theorem linnikVMVT_one_sub_inv_pow_mul_le_exp_neg
    (k m : Nat) (hk : 2 <= k) :
    (1 - 1 / (k : Real)) ^ (k * m) <= Real.exp (-(m : Real)) := by
  have hkPos : 0 < (k : Real) := by positivity
  have hbaseNonneg : 0 <= 1 - 1 / (k : Real) := by
    have hkOne : (1 : Real) <= k := by exact_mod_cast (show 1 <= k by omega)
    have hinv : 1 / (k : Real) <= 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hkOne
    linarith
  have hbase : 1 - 1 / (k : Real) <= Real.exp (-(1 / (k : Real))) := by
    simpa [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-(1 / (k : Real)))
  calc
    (1 - 1 / (k : Real)) ^ (k * m) <=
        (Real.exp (-(1 / (k : Real)))) ^ (k * m) := by gcongr
    _ = Real.exp (((k * m : Nat) : Real) * (-(1 / (k : Real)))) :=
      (Real.exp_nat_mul _ _).symm
    _ = Real.exp (-(m : Real)) := by
      congr 1
      push_cast
      field_simp

theorem exists_linnikVMVT_decay_multiple (delta : Real) (hdelta : 0 < delta) :
    exists m : Nat, And (0 < m) (forall k : Nat, 2 <= k ->
      (1 - 1 / (k : Real)) ^ (k * m) < delta / 4) := by
  choose m hm using exists_nat_gt (4 / delta)
  have hmPosReal : 0 < (m : Real) := lt_trans (by positivity : (0 : Real) < 4 / delta) hm
  have hmPos : 0 < m := by exact_mod_cast hmPosReal
  refine Exists.intro m (And.intro hmPos ?_)
  intro k hk
  have hpow := linnikVMVT_one_sub_inv_pow_mul_le_exp_neg k m hk
  have hmExp : (m : Real) <= Real.exp (m : Real) := by
    calc
      (m : Real) <= (m : Real) + 1 := by linarith
      _ <= Real.exp (m : Real) := by
        simpa [add_comm] using Real.add_one_le_exp (m : Real)
  have hinv : 1 / Real.exp (m : Real) <= 1 / (m : Real) :=
    one_div_le_one_div_of_le hmPosReal hmExp
  have hfour : 4 < delta * (m : Real) := by
    have hscaled := mul_lt_mul_of_pos_left hm hdelta
    have hcancel : delta * (4 / delta) = 4 := by
      field_simp
    rw [hcancel] at hscaled
    exact hscaled
  have hrec : 1 / (m : Real) < delta / 4 := by
    have hid : delta / 4 - 1 / (m : Real) =
        (delta * (m : Real) - 4) / (4 * (m : Real)) := by
      field_simp
    apply sub_pos.mp
    rw [hid]
    exact div_pos (sub_pos.mpr hfour) (mul_pos (by norm_num) hmPosReal)
  calc
    (1 - 1 / (k : Real)) ^ (k * m) <= Real.exp (-(m : Real)) := hpow
    _ = 1 / Real.exp (m : Real) := by simpa [one_div] using Real.exp_neg (m : Real)
    _ <= 1 / (m : Real) := hinv
    _ < delta / 4 := hrec

/-- After choosing the VMVT level as `r = k * m`, the entire normalized
mean-value factor has residual base exponent at most
`delta / (32 * (k*m)^2)`.  The same positive coefficient constant works for
every tolerance, degree, and scale. -/
theorem exists_linnikVMVT_normalized_decay_bound :
    exists C : Real, And (0 < C) (forall delta : Real, 0 < delta ->
      exists m : Nat, And (0 < m) (forall k Q : Nat,
        2 <= k -> 0 < Q ->
        ((Finset.vinogradovMeanValue k (k * (k * m)) (2 * Q) : Real) /
            ((2 * Q : Nat) : Real) ^
              (2 * ((k * m : Nat) : Real) * k -
                (k : Real) * (k + 1) / 2)) ^
            (1 / (4 * (k : Real) ^ 2 * ((k * m : Nat) : Real) ^ 2)) <=
          Real.exp (C * Real.log k / (4 * ((k * m : Nat) : Real))) *
            (((2 * Q : Nat) : Real) ^
              (delta / (32 * ((k * m : Nat) : Real) ^ 2))))) := by
  choose C hC hnormalized using exists_linnikVMVT_normalized_root_bound
  refine Exists.intro C (And.intro hC ?_)
  intro delta hdelta
  choose m hm hdecay using exists_linnikVMVT_decay_multiple delta hdelta
  refine Exists.intro m (And.intro hm ?_)
  intro k Q hk hQ
  have hkPos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hr : 0 < k * m := Nat.mul_pos hkPos hm
  have hsource := hnormalized k (k * m) Q hk hr hQ
  have hbase : (1 : Real) <= ((2 * Q : Nat) : Real) := by
    exact_mod_cast (show 1 <= 2 * Q by omega)
  have hexponent :
      (1 - 1 / (k : Real)) ^ (k * m) /
          (8 * ((k * m : Nat) : Real) ^ 2) <=
        delta / (32 * ((k * m : Nat) : Real) ^ 2) := by
    calc
      (1 - 1 / (k : Real)) ^ (k * m) /
          (8 * ((k * m : Nat) : Real) ^ 2) <=
          (delta / 4) / (8 * ((k * m : Nat) : Real) ^ 2) := by
            gcongr
            exact (hdecay k hk).le
      _ = delta / (32 * ((k * m : Nat) : Real) ^ 2) := by
        field_simp
        ring
  have hrpow := Real.rpow_le_rpow_of_exponent_le hbase hexponent
  exact hsource.trans (mul_le_mul_of_nonneg_left hrpow (Real.exp_pos _).le)

/-- The signed Theorem 24.12 exponent packet.  A good-denominator contribution
of `-delta^3 / (16*r^2)` absorbs the complete residual VMVT exponent and leaves
the strictly negative power `-lambda / k^2`, with `lambda > 0`. -/
theorem exists_linnikVMVT_signed_decay_bound :
    exists C : Real, 0 < C /\ forall delta : Real, 0 < delta ->
      exists m : Nat, 0 < m /\ exists lambda : Real, 0 < lambda /\
        forall k Q : Nat, 2 <= k -> 0 < Q ->
          ((Finset.vinogradovMeanValue k (k * (k * m)) (2 * Q) : Real) /
              ((2 * Q : Nat) : Real) ^
                (2 * ((k * m : Nat) : Real) * k -
                  (k : Real) * (k + 1) / 2)) ^
              (1 / (4 * (k : Real) ^ 2 * ((k * m : Nat) : Real) ^ 2)) *
            (((2 * Q : Nat) : Real) ^
              (-(delta ^ 3) / (16 * ((k * m : Nat) : Real) ^ 2))) <=
            Real.exp (C * Real.log k / (4 * ((k * m : Nat) : Real))) *
              (((2 * Q : Nat) : Real) ^
                (-lambda / (k : Real) ^ 2)) := by
  choose C hC hnormalized using exists_linnikVMVT_normalized_decay_bound
  refine Exists.intro C (And.intro hC ?_)
  intro delta hdelta
  choose m hm hbound using hnormalized (delta ^ 3) (pow_pos hdelta 3)
  let lambda : Real := delta ^ 3 / (32 * (m : Real) ^ 2)
  have hlambda : 0 < lambda := by
    simp only [lambda]
    positivity
  refine Exists.intro m (And.intro hm (Exists.intro lambda (And.intro hlambda ?_)))
  intro k Q hk hQ
  have hsource := hbound k Q hk hQ
  have hXPos : 0 < ((2 * Q : Nat) : Real) := by
    exact_mod_cast (show 0 < 2 * Q by omega)
  have hmul := mul_le_mul_of_nonneg_right hsource
    (Real.rpow_nonneg hXPos.le (-(delta ^ 3) /
      (16 * ((k * m : Nat) : Real) ^ 2)))
  calc
    ((Finset.vinogradovMeanValue k (k * (k * m)) (2 * Q) : Real) /
          ((2 * Q : Nat) : Real) ^
            (2 * ((k * m : Nat) : Real) * k -
              (k : Real) * (k + 1) / 2)) ^
          (1 / (4 * (k : Real) ^ 2 * ((k * m : Nat) : Real) ^ 2)) *
        (((2 * Q : Nat) : Real) ^
          (-(delta ^ 3) / (16 * ((k * m : Nat) : Real) ^ 2))) <=
        (Real.exp (C * Real.log k / (4 * ((k * m : Nat) : Real))) *
          (((2 * Q : Nat) : Real) ^
            (delta ^ 3 / (32 * ((k * m : Nat) : Real) ^ 2)))) *
          (((2 * Q : Nat) : Real) ^
            (-(delta ^ 3) / (16 * ((k * m : Nat) : Real) ^ 2))) := hmul
    _ = Real.exp (C * Real.log k / (4 * ((k * m : Nat) : Real))) *
        (((2 * Q : Nat) : Real) ^
          (delta ^ 3 / (32 * ((k * m : Nat) : Real) ^ 2) +
            (-(delta ^ 3) / (16 * ((k * m : Nat) : Real) ^ 2)))) := by
      rw [mul_assoc, Real.rpow_add hXPos]
    _ = Real.exp (C * Real.log k / (4 * ((k * m : Nat) : Real))) *
        (((2 * Q : Nat) : Real) ^ (-lambda / (k : Real) ^ 2)) := by
      congr 2
      simp only [lambda]
      have hkPos : 0 < (k : Real) := by positivity
      have hmPos : 0 < (m : Real) := by exact_mod_cast hm
      push_cast
      field_simp
      ring
