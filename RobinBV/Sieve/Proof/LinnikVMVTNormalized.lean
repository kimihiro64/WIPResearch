/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMVTSourceTheorem

/-!
# Normalized VMVT factor for Vinogradov's method

This module converts the unconditional source-form VMVT estimate into the
normalized root factor used in the proof of Theorem 24.12. Both the exponential
coefficient cost and the residual eta power are simplified completely.
-/

theorem exists_linnikVMVT_normalized_root_bound :
    exists C : Real, And (0 < C) (forall k r Q : Nat,
      2 <= k -> 0 < r -> 0 < Q ->
      ((Finset.vinogradovMeanValue k (k * r) (2 * Q) : Real) /
          ((2 * Q : Nat) : Real) ^
            (2 * (r : Real) * k - (k : Real) * (k + 1) / 2)) ^
          (1 / (4 * (k : Real) ^ 2 * (r : Real) ^ 2)) <=
        Real.exp (C * Real.log k / (4 * (r : Real))) *
          (((2 * Q : Nat) : Real) ^
            ((1 - 1 / (k : Real)) ^ r / (8 * (r : Real) ^ 2)))) := by
  choose C hC hvmvt using exists_linnikVMVT_source_bound
  refine Exists.intro C (And.intro hC ?_)
  intro k r Q hk hr hQ
  have hkPos : 0 < k := by omega
  have hXNat : 0 < 2 * Q := by omega
  let X : Real := ((2 * Q : Nat) : Real)
  let B : Real := 2 * (r : Real) * k - (k : Real) * (k + 1) / 2
  let eta : Real := linnikVMVTEta k r
  let theta : Real := 1 / (4 * (k : Real) ^ 2 * (r : Real) ^ 2)
  let A : Real := C * (r : Real) * (k : Real) ^ 2 * Real.log k
  have hX : 0 < X := by
    simp only [X]
    exact_mod_cast hXNat
  have htheta : 0 <= theta := by
    simp only [theta]
    positivity
  have hE : linnikVMVTExponent k r = B + eta := by
    simp only [linnikVMVTExponent, linnikVMVTEta, B, eta]
  have hsplit : X ^ linnikVMVTExponent k r = X ^ B * X ^ eta := by
    rw [hE, Real.rpow_add hX]
  have hsource := hvmvt r k (2 * Q) hr hk hXNat
  have hsource' : (Finset.vinogradovMeanValue k (k * r) (2 * Q) : Real) <=
      Real.exp A * (X ^ B * X ^ eta) := by
    simpa only [A, X, hsplit] using hsource
  have hdenPos : 0 < X ^ B := Real.rpow_pos_of_pos hX B
  have hratio : (Finset.vinogradovMeanValue k (k * r) (2 * Q) : Real) /
      X ^ B <= Real.exp A * X ^ eta := by
    apply le_of_mul_le_mul_right _ hdenPos
    have hcancel :
        ((Finset.vinogradovMeanValue k (k * r) (2 * Q) : Real) / X ^ B) *
          X ^ B = (Finset.vinogradovMeanValue k (k * r) (2 * Q) : Real) := by
      field_simp [ne_of_gt hdenPos]
    rw [hcancel]
    calc
      (Finset.vinogradovMeanValue k (k * r) (2 * Q) : Real) <=
          Real.exp A * (X ^ B * X ^ eta) := hsource'
      _ = (Real.exp A * X ^ eta) * X ^ B := by ring
  have hroot := Real.rpow_le_rpow
    (div_nonneg (by positivity) hdenPos.le) hratio htheta
  have hAroot : A * theta = C * Real.log k / (4 * (r : Real)) := by
    simp only [A, theta]
    field_simp
  have hetaRoot : eta * theta =
      (1 - 1 / (k : Real)) ^ r / (8 * (r : Real) ^ 2) := by
    simp only [eta, linnikVMVTEta, theta]
    field_simp
    ring
  calc
    (((Finset.vinogradovMeanValue k (k * r) (2 * Q) : Real) / X ^ B) ^ theta) <=
        (Real.exp A * X ^ eta) ^ theta := hroot
    _ = (Real.exp A) ^ theta * (X ^ eta) ^ theta := by
      rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hX.le _)]
    _ = Real.exp (A * theta) * X ^ (eta * theta) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      rw [Real.rpow_mul hX.le]
    _ = Real.exp (C * Real.log k / (4 * (r : Real))) *
        X ^ ((1 - 1 / (k : Real)) ^ r / (8 * (r : Real) ^ 2)) := by
      rw [hAroot, hetaRoot]
    _ = Real.exp (C * Real.log k / (4 * (r : Real))) *
        (((2 * Q : Nat) : Real) ^
          ((1 - 1 / (k : Real)) ^ r / (8 * (r : Real) ^ 2))) := by rfl
