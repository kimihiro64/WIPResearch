/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMVTExponent

/-!
# Finite prime-band summation for the Linnik VMVT recurrence

This module bounds the exact natural summand over the complete finite prime
packet. It is the direct consumer of the pointwise modulus-elimination bound.
-/

/-- Sum the literal natural recurrence term over a finite positive modulus packet. -/
theorem linnikVMVT_nat_prime_sum_with_induction_le
    (k s X : Nat) (P : Finset {p : Nat // 0 < p}) (A : Real)
    (hk : 2 <= k) (hs : 0 < s) (hA : 0 <= A)
    (hthreshold : (4 * s * k) ^ k <= X)
    (hp : forall (p : {p : Nat // 0 < p}),
      Membership.mem P p -> p.val <= 2 * Nat.nthRoot k X)
    (hJ : forall (p : {p : Nat // 0 < p}), Membership.mem P p ->
      (Finset.vinogradovMeanValue k (k * s) (1 + X / p.val) : Real) <=
        A * (1 + (X : Real) / p.val) ^ linnikVMVTExponent k s) :
    ((P.sum (fun p =>
      p.val ^ (2 * (k * s)) *
        ((X ^ k * (k.factorial * p.val ^ (k * (k - 1) / 2))) *
          Finset.vinogradovMeanValue k (k * s) (1 + X / p.val))) : Nat) : Real) <=
      (P.card : Real) *
        ((k.factorial : Real) * A * Real.exp 1 *
          (2 : Real) ^ ((k : Real) ^ 2) *
            (X : Real) ^ linnikVMVTExponent k (s + 1)) := by
  rw [Nat.cast_sum]
  calc
    P.sum (fun p =>
        ((p.val ^ (2 * (k * s)) *
          ((X ^ k * (k.factorial * p.val ^ (k * (k - 1) / 2))) *
            Finset.vinogradovMeanValue k (k * s) (1 + X / p.val)) : Nat) : Real)) <=
      P.sum (fun _ =>
        (k.factorial : Real) * A * Real.exp 1 *
          (2 : Real) ^ ((k : Real) ^ 2) *
            (X : Real) ^ linnikVMVTExponent k (s + 1)) := by
      apply Finset.sum_le_sum
      intro p hpMem
      exact linnikVMVT_nat_prime_term_with_induction_le
        k s X p.val (Finset.vinogradovMeanValue k (k * s) (1 + X / p.val)) A
        hk hs p.property hA hthreshold (hp p hpMem) (hJ p hpMem)
    _ = (P.card : Real) *
        ((k.factorial : Real) * A * Real.exp 1 *
          (2 : Real) ^ ((k : Real) ^ 2) *
            (X : Real) ^ linnikVMVTExponent k (s + 1)) := by
      simp

/-- Consume the exact dense prime-band recurrence with the explicit packet sum. -/
theorem exists_linnikVMVT_explicit_step :
    exists Y0 : Nat, forall k s X : Nat, forall A : Real,
      2 <= k -> 0 < s -> 0 <= A ->
      (max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)) ^ k <= X ->
      (4 * s * k) ^ k <= X ->
      (forall p : Nat, 0 < p -> p <= 2 * Nat.nthRoot k X ->
        (Finset.vinogradovMeanValue k (k * s) (1 + X / p) : Real) <=
          A * (1 + (X : Real) / p) ^ linnikVMVTExponent k s) ->
      (Finset.vinogradovMeanValue k (k * (s + 1)) X : Real) <=
        max
          (4 * ((k ^ 3 + 1 : Nat) : Real) ^ 2 *
            ((k.factorial : Real) * A * Real.exp 1 *
              (2 : Real) ^ ((k : Real) ^ 2) *
                (X : Real) ^ linnikVMVTExponent k (s + 1)))
          ((4 ^ (k * (s + 1)) * k ^ (4 * (k * (s + 1))) : Nat) : Real) := by
  choose Y0 hY0 using
    Finset.exists_uniform_vinogradovMeanValue_dense_sum_recurrence
  refine Exists.intro Y0 ?_
  intro k s X A hk hs hA hband hscale hJ
  have hkPos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hr : 1 < s + 1 := by omega
  have hkr : 2 <= k * (s + 1) := by nlinarith
  choose P hcard hpPacket hrec using
    hY0 k (s + 1) X hkPos hr hkr hband
  let S := P.sum (fun p =>
    p.val ^ (2 * (k * s)) *
      ((X ^ k * (k.factorial * p.val ^ (k * (k - 1) / 2))) *
        Finset.vinogradovMeanValue k (k * s) (1 + X / p.val)))
  let C := (k.factorial : Real) * A * Real.exp 1 *
    (2 : Real) ^ ((k : Real) ^ 2) *
      (X : Real) ^ linnikVMVTExponent k (s + 1)
  have hsum : (S : Real) <= (P.card : Real) * C := by
    exact linnikVMVT_nat_prime_sum_with_induction_le
      k s X P A hk hs hA hscale
        (fun p hpMem => (hpPacket p hpMem).2.2)
        (fun p hpMem => hJ p.val p.property (hpPacket p hpMem).2.2)
  have hmain : ((4 * (P.card * S) : Nat) : Real) <=
      4 * (P.card : Real) ^ 2 * C := by
    push_cast
    calc
      4 * ((P.card : Real) * (S : Real)) <=
          4 * ((P.card : Real) * ((P.card : Real) * C)) := by
        gcongr
      _ = 4 * (P.card : Real) ^ 2 * C := by ring
  have hrecReal :
      (Finset.vinogradovMeanValue k (k * (s + 1)) X : Real) <=
        max ((4 * (P.card * S) : Nat) : Real)
          ((4 ^ (k * (s + 1)) * k ^ (4 * (k * (s + 1))) : Nat) : Real) := by
    exact_mod_cast hrec
  calc
    (Finset.vinogradovMeanValue k (k * (s + 1)) X : Real) <=
        max ((4 * (P.card * S) : Nat) : Real)
          ((4 ^ (k * (s + 1)) * k ^ (4 * (k * (s + 1))) : Nat) : Real) :=
      hrecReal
    _ <= max (4 * (P.card : Real) ^ 2 * C)
        ((4 ^ (k * (s + 1)) * k ^ (4 * (k * (s + 1))) : Nat) : Real) :=
      max_le_max hmain le_rfl
    _ = max
        (4 * ((k ^ 3 + 1 : Nat) : Real) ^ 2 *
          ((k.factorial : Real) * A * Real.exp 1 *
            (2 : Real) ^ ((k : Real) ^ 2) *
              (X : Real) ^ linnikVMVTExponent k (s + 1)))
        ((4 ^ (k * (s + 1)) * k ^ (4 * (k * (s + 1))) : Nat) : Real) := by
      simp only [C, hcard]

/-- The collision branch is absorbed by every nonnegative VMVT power of `X`. -/
theorem linnikVMVT_collision_branch_le
    (k r X : Nat) (hk : 0 < k) (hr : 0 < r) (hX : 0 < X) :
    ((4 ^ (k * r) * k ^ (4 * (k * r)) : Nat) : Real) <=
      ((4 ^ (k * r) * k ^ (4 * (k * r)) : Nat) : Real) *
        (X : Real) ^ linnikVMVTExponent k r := by
  have hXReal : 1 <= (X : Real) := by exact_mod_cast hX
  have hpow : 1 <= (X : Real) ^ linnikVMVTExponent k r :=
    Real.one_le_rpow hXReal (linnikVMVTExponent_nonneg k r hk hr)
  calc
    ((4 ^ (k * r) * k ^ (4 * (k * r)) : Nat) : Real) =
        ((4 ^ (k * r) * k ^ (4 * (k * r)) : Nat) : Real) * 1 := by ring
    _ <= ((4 ^ (k * r) * k ^ (4 * (k * r)) : Nat) : Real) *
        (X : Real) ^ linnikVMVTExponent k r :=
      mul_le_mul_of_nonneg_left hpow (by positivity)

/-- A complete one-step VMVT envelope with no packet or auxiliary modulus. -/
theorem exists_linnikVMVT_explicit_coefficient_step :
    exists Y0 : Nat, forall k s X : Nat, forall A : Real,
      2 <= k -> 0 < s -> 0 <= A ->
      (max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)) ^ k <= X ->
      (4 * s * k) ^ k <= X ->
      (forall p : Nat, 0 < p -> p <= 2 * Nat.nthRoot k X ->
        (Finset.vinogradovMeanValue k (k * s) (1 + X / p) : Real) <=
          A * (1 + (X : Real) / p) ^ linnikVMVTExponent k s) ->
      (Finset.vinogradovMeanValue k (k * (s + 1)) X : Real) <=
        (4 * ((k ^ 3 + 1 : Nat) : Real) ^ 2 *
            (k.factorial : Real) * A * Real.exp 1 *
              (2 : Real) ^ ((k : Real) ^ 2) +
          ((4 ^ (k * (s + 1)) * k ^ (4 * (k * (s + 1))) : Nat) : Real)) *
            (X : Real) ^ linnikVMVTExponent k (s + 1) := by
  choose Y0 hY0 using exists_linnikVMVT_explicit_step
  refine Exists.intro Y0 ?_
  intro k s X A hk hs hA hband hscale hJ
  have hstep := hY0 k s X A hk hs hA hband hscale hJ
  have hkPos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hrPos : 0 < s + 1 := by omega
  have hbasePos : 0 < max (max k Y0) (32 * (k ^ 3 + 1) ^ 2) := by
    exact lt_of_lt_of_le hkPos (le_max_of_le_left (le_max_left _ _))
  have hX : 0 < X := lt_of_lt_of_le (pow_pos hbasePos k) hband
  have hcollision := linnikVMVT_collision_branch_le k (s + 1) X hkPos hrPos hX
  let a := 4 * ((k ^ 3 + 1 : Nat) : Real) ^ 2 *
    (k.factorial : Real) * A * Real.exp 1 * (2 : Real) ^ ((k : Real) ^ 2)
  let b := ((4 ^ (k * (s + 1)) * k ^ (4 * (k * (s + 1))) : Nat) : Real)
  let x := (X : Real) ^ linnikVMVTExponent k (s + 1)
  have ha : 0 <= a := by
    simp only [a]
    positivity
  have hb : 0 <= b := by positivity
  have hx : 0 <= x := by positivity
  have hmain :
      4 * ((k ^ 3 + 1 : Nat) : Real) ^ 2 *
          ((k.factorial : Real) * A * Real.exp 1 *
            (2 : Real) ^ ((k : Real) ^ 2) * x) = a * x := by
    simp only [a]
    ring
  calc
    (Finset.vinogradovMeanValue k (k * (s + 1)) X : Real) <=
        max (a * x) b := by
      simpa only [a, b, x, hmain] using hstep
    _ <= max (a * x) (b * x) := max_le_max le_rfl hcollision
    _ <= (a + b) * x := by
      apply max_le
      next => nlinarith [mul_nonneg hb hx]
      next => nlinarith [mul_nonneg ha hx]
    _ = (4 * ((k ^ 3 + 1 : Nat) : Real) ^ 2 *
            (k.factorial : Real) * A * Real.exp 1 *
              (2 : Real) ^ ((k : Real) ^ 2) +
          ((4 ^ (k * (s + 1)) * k ^ (4 * (k * (s + 1))) : Nat) : Real)) *
            (X : Real) ^ linnikVMVTExponent k (s + 1) := by
      rfl
