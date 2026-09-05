/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimeChebyshev

/-!
# Complete higher prime-power remainders with character weights

All powers above a selected layer are retained. Their support lies below
the corresponding root cutoff, and every admitted prime contributes at
most the logarithm of the original cutoff. No prime distribution estimate
or restriction on the character modulus is required.
-/

set_option autoImplicit false

namespace DirichletCharacter

noncomputable section

/-- The full logarithmic prime sum has the elementary uniform theta majorant. -/
theorem norm_primeChebyshevSum_le_theta
    {N : Nat} (chi : DirichletCharacter Complex N) (P : Nat) :
    norm (chi.primeChebyshevSum P) <= Chebyshev.theta (P : Real) := by
  unfold primeChebyshevSum
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  calc
    _ <= Finset.sum (Nat.primesLE P) (fun p => norm ((Real.log p : Complex) * chi (p : ZMod N))) :=
      norm_sum_le _ _
    _ <= _ := by
      apply Finset.sum_le_sum
      intro p hp
      have hLog : 0 <= Real.log p := Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLog]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (chi.norm_le_one _) hLog

/-- The complete admitted contribution from powers strictly greater than k. -/
def primePowerHigherStep
    {N : Nat} (chi : DirichletCharacter Complex N) (p k : Nat) (t : Real) : Complex :=
  (Real.log p : Complex) * Finset.sum (Finset.Icc (k + 1) (Nat.log p (Nat.floor t)))
    (fun j => chi (p : ZMod N) ^ j)

/-- Each prime's entire higher-power remainder contributes at most log(t). -/
theorem norm_primePowerHigherStep_le_log
    {N : Nat} (chi : DirichletCharacter Complex N) {p : Nat} (hp : Nat.Prime p)
    (k : Nat) {t : Real} (ht : 1 <= t) :
    norm (chi.primePowerHigherStep p k t) <= Real.log t := by
  let K := Nat.log p (Nat.floor t)
  have hLog : 0 <= Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hCard : (Finset.Icc (k + 1) K).card <= K := by rw [Nat.card_Icc]; omega
  have hSum : norm (Finset.sum (Finset.Icc (k + 1) K) (fun j => chi (p : ZMod N) ^ j)) <=
      (K : Real) := by
    calc
      _ <= Finset.sum (Finset.Icc (k + 1) K) (fun j => norm (chi (p : ZMod N) ^ j)) := norm_sum_le _ _
      _ <= Finset.sum (Finset.Icc (k + 1) K) (fun _ => (1 : Real)) := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [map_pow] using chi.norm_le_one ((p : ZMod N) ^ j)
      _ = ((Finset.Icc (k + 1) K).card : Real) := by simp
      _ <= _ := Nat.cast_le.mpr hCard
  unfold primePowerHigherStep
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLog]
  have hGap := (Nat.log_sub_log_floor_mul_log_bounds hp.one_lt ht).1
  calc
    _ <= Real.log p * (K : Real) := mul_le_mul_of_nonneg_left hSum hLog
    _ <= _ := by dsimp only [K]; nlinarith

/-- No higher power contributes before the first possible admission time. -/
theorem primePowerHigherStep_eq_zero_of_lt
    {N : Nat} (chi : DirichletCharacter Complex N) {p : Nat} (hp : Nat.Prime p)
    {k : Nat} {t : Real} (ht : 1 <= t) (hPow : Nat.floor t < p ^ (k + 1)) :
    chi.primePowerHigherStep p k t = 0 := by
  have hFloor : 1 <= Nat.floor t := Nat.le_floor (by simpa only [Nat.cast_one] using ht)
  have hK : Nat.log p (Nat.floor t) < k + 1 :=
    (Nat.log_lt_iff_lt_pow hp.one_lt (by omega)).2 hPow
  simp [primePowerHigherStep, Finset.Icc_eq_empty_of_lt hK]

/-- All higher prime powers together have a root-log bound, uniformly
over the prime cap and every complex character of every modulus. -/
theorem norm_sum_primePowerHigherStep_le_root_log
    {N : Nat} (chi : DirichletCharacter Complex N) (P k : Nat)
    {t : Real} (ht : 1 <= t) :
    norm (Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p k t)) <=
      t ^ (Inv.inv ((k + 1 : Nat) : Real)) * Real.log t := by
  classical
  let S := Finset.filter (fun p => p ^ (k + 1) <= Nat.floor t) (Nat.primesLE P)
  let R : Real := t ^ (Inv.inv ((k + 1 : Nat) : Real))
  have htNonneg : 0 <= t := by linarith
  have hLog : 0 <= Real.log t := Real.log_nonneg ht
  have hSub : S <= Finset.Icc 1 (Nat.floor R) := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    have hpPrime := (Nat.mem_primesLE.mp h.1).2
    have hPower : (p : Real) ^ ((k + 1 : Nat) : Real) <= t := by
      rw [Real.rpow_natCast]
      have hCast : (p : Real) ^ (k + 1) <= (Nat.floor t : Real) := by exact_mod_cast h.2
      exact hCast.trans (Nat.floor_le htNonneg)
    have hRoot : (p : Real) <= R :=
      (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg p) htNonneg
        (by exact_mod_cast Nat.succ_pos k)).2 hPower
    exact Finset.mem_Icc.mpr (And.intro hpPrime.one_le (Nat.le_floor hRoot))
  have hCard : (S.card : Real) <= R := by
    have hNat := Finset.card_le_card hSub
    simp only [Nat.card_Icc] at hNat
    have hNat' : S.card <= Nat.floor R := by omega
    exact (Nat.cast_le.mpr hNat').trans (Nat.floor_le (Real.rpow_nonneg htNonneg _))
  calc
    _ <= Finset.sum (Nat.primesLE P) (fun p => norm (chi.primePowerHigherStep p k t)) := norm_sum_le _ _
    _ <= Finset.sum (Nat.primesLE P) (fun p =>
        if p ^ (k + 1) <= Nat.floor t then Real.log t else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime := (Nat.mem_primesLE.mp hp).2
      by_cases hPow : p ^ (k + 1) <= Nat.floor t
      case pos =>
        rw [if_pos hPow]
        exact chi.norm_primePowerHigherStep_le_log hpPrime k ht
      case neg =>
        rw [if_neg hPow, chi.primePowerHigherStep_eq_zero_of_lt hpPrime ht (by omega), norm_zero]
    _ = (S.card : Real) * Real.log t := by simp only [S, <- Finset.sum_filter]; simp
    _ <= _ := mul_le_mul_of_nonneg_right hCard hLog

/-- Removing an admitted prefix is an exact decomposition into that
prefix and all higher powers, including every power still below the cutoff. -/
theorem primePowerChebyshevStep_eq_prefix_add_higher
    {N : Nat} (chi : DirichletCharacter Complex N) (p k : Nat) (t : Real)
    (hk : k <= Nat.log p (Nat.floor t)) :
    chi.primePowerChebyshevStep p t =
      (Real.log p : Complex) * Finset.sum (Finset.Icc 1 k) (fun j => chi (p : ZMod N) ^ j) +
        chi.primePowerHigherStep p k t := by
  classical
  let K := Nat.log p (Nat.floor t)
  have hSub : Finset.Icc 1 k <= Finset.Icc 1 K := by
    intro j hj
    have h := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr (And.intro h.1 (h.2.trans hk))
  have hSet : SDiff.sdiff (Finset.Icc 1 K) (Finset.Icc 1 k) = Finset.Icc (k + 1) K := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_Icc]
    omega
  have hSum := Finset.sum_sdiff (f := fun j => chi (p : ZMod N) ^ j) hSub
  rw [hSet] at hSum
  unfold primePowerChebyshevStep primePowerHigherStep
  change (Real.log p : Complex) * Finset.sum (Finset.Icc 1 K) (fun j => chi (p : ZMod N) ^ j) = _
  rw [<- hSum]
  ring

/-- The first remaining layer splits off exactly; the complete remainder
above it is retained. The indicator uses the actual admission exponent. -/
theorem primePowerHigherStep_eq_first_add_higher
    {N : Nat} (chi : DirichletCharacter Complex N) (p k : Nat) (t : Real) :
    chi.primePowerHigherStep p k t =
      (if k + 1 <= Nat.log p (Nat.floor t) then
        (Real.log p : Complex) * chi (p : ZMod N) ^ (k + 1) else 0) +
          chi.primePowerHigherStep p (k + 1) t := by
  classical
  let K := Nat.log p (Nat.floor t)
  by_cases hK : k + 1 <= K
  case pos =>
    have hSet : Finset.Icc (k + 1) K =
        Insert.insert (k + 1) (Finset.Icc (k + 1 + 1) K) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hNot : Not (Membership.mem (Finset.Icc (k + 1 + 1) K) (k + 1)) := by
      simp only [Finset.mem_Icc]
      omega
    change _ = (if k + 1 <= K then _ else _) + _
    rw [if_pos hK]
    unfold primePowerHigherStep
    change (Real.log p : Complex) * Finset.sum (Finset.Icc (k + 1) K) _ = _
    rw [hSet, Finset.sum_insert hNot]
    ring
  case neg =>
    have hLt : K < k + 1 := by omega
    have hLtNext : K < k + 1 + 1 := by omega
    change _ = (if k + 1 <= K then _ else _) + _
    rw [if_neg hK]
    unfold primePowerHigherStep
    change (Real.log p : Complex) * Finset.sum (Finset.Icc (k + 1) K) _ =
      0 + (Real.log p : Complex) * Finset.sum (Finset.Icc (k + 1 + 1) K) _
    rw [Finset.Icc_eq_empty_of_lt hLt, Finset.Icc_eq_empty_of_lt hLtNext]
    simp

/-- The first remaining power layer is exactly the prime Chebyshev sum
of the positive character power at the capped real-root frontier. -/
theorem sum_first_power_layer_eq_primeChebyshevSum_min
    {N : Nat} (chi : DirichletCharacter Complex N) (P k : Nat)
    {t : Real} (ht : 1 <= t) :
    Finset.sum (Nat.primesLE P) (fun p =>
      if k + 1 <= Nat.log p (Nat.floor t) then
        (Real.log p : Complex) * chi (p : ZMod N) ^ (k + 1) else 0) =
      (chi ^ (k + 1)).primeChebyshevSum
        (min P (Nat.floor (t ^ (Inv.inv ((k + 1 : Nat) : Real))))) := by
  classical
  let R := Nat.floor (t ^ (Inv.inv ((k + 1 : Nat) : Real)))
  have hSet : Nat.primesLE (min P R) = Finset.filter (fun p => p <= R) (Nat.primesLE P) := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_filter, le_min_iff]
    constructor
    next =>
      intro h
      exact And.intro (And.intro h.1.1 h.2) h.1.2
    next =>
      intro h
      exact And.intro (And.intro h.1.1 h.2) h.1.2
  have hFloor : 1 <= Nat.floor t := Nat.le_floor (by simpa only [Nat.cast_one] using ht)
  unfold primeChebyshevSum
  change _ = Finset.sum (Nat.primesLE (min P R)) _
  rw [hSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime := (Nat.mem_primesLE.mp hp).2
  have hAdmission : k + 1 <= Nat.log p (Nat.floor t) <-> p <= R := by
    constructor
    next =>
      intro h
      exact (Nat.pow_le_floor_iff_le_floor_root (p := p) (t := t) (Nat.succ_pos k) (by linarith)).mp
        (Nat.pow_le_of_le_log (by omega : Not (Nat.floor t = 0)) h)
    next =>
      intro h
      exact Nat.le_log_of_pow_le hpPrime.one_lt
        ((Nat.pow_le_floor_iff_le_floor_root (p := p) (t := t) (Nat.succ_pos k) (by linarith)).mpr h)
  simp only [hAdmission, MulChar.pow_apply' chi (Nat.succ_ne_zero k)]

/-- The complete sum of higher prime powers is its exact first remaining
capped prime moment plus the entire sum above the next layer. -/
theorem sum_primePowerHigherStep_eq_primeMoment_add_higher
    {N : Nat} (chi : DirichletCharacter Complex N) (P k : Nat)
    {t : Real} (ht : 1 <= t) :
    Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p k t) =
      (chi ^ (k + 1)).primeChebyshevSum
        (min P (Nat.floor (t ^ (Inv.inv ((k + 1 : Nat) : Real))))) +
          Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p (k + 1) t) := by
  have hSum : Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p k t) =
      Finset.sum (Nat.primesLE P) (fun p =>
        (if k + 1 <= Nat.log p (Nat.floor t) then
          (Real.log p : Complex) * chi (p : ZMod N) ^ (k + 1) else 0) +
            chi.primePowerHigherStep p (k + 1) t) := by
    apply Finset.sum_congr rfl
    intro p _
    exact chi.primePowerHigherStep_eq_first_add_higher p k t
  rw [hSum, Finset.sum_add_distrib, chi.sum_first_power_layer_eq_primeChebyshevSum_min P k ht]

end

end DirichletCharacter
