/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LinnikPrimeBand

/-!
# Recursive Linnik bound for Vinogradov mean values

This module packages the fully instantiated prime-band recurrence into an
explicit natural-valued bound and proves that the actual Vinogradov solution
count is bounded by it.  The recursion has no free modulus, prime set, packet
count, Fourier integral, or compatible-tail parameter.
-/

set_option autoImplicit false

namespace Finset

/-- One explicit root-scale recurrence step for Linnik's VMVT induction. -/
def linnikVMVTStep (k r X M : Nat) : Nat :=
  max
    (4 * ((k ^ 3 + 1) ^ 2 *
      ((2 ^ (k ^ 3 + 1) * Nat.nthRoot k X) ^
          (2 * (k * (r - 1))) *
        ((X ^ k * (k.factorial *
            (2 ^ (k ^ 3 + 1) * Nat.nthRoot k X) ^
              (k * (k - 1) / 2))) * M))))
    (4 ^ (k * r) * k ^ (4 * (k * r)))

/-- The recurrence step is monotone in its lower-level mean-value input. -/
theorem linnikVMVTStep_mono
    (k r X M N : Nat) (hMN : M <= N) :
    linnikVMVTStep k r X M <= linnikVMVTStep k r X N := by
  unfold linnikVMVTStep
  apply max_le_max
  next => gcongr
  next => rfl

/-- Explicit recursive upper bound.  Small `X` uses the trivial count; the
large branch uses the root-scale Linnik recurrence. -/
def linnikVMVTRecursiveBound (k : Nat) : Nat -> Nat -> Nat
  | 0, _X => 1
  | 1, X => X ^ k * k.factorial
  | r + 2, X =>
      if k ^ k <= X then
        linnikVMVTStep k (r + 2) X
          (linnikVMVTRecursiveBound k (r + 1)
            (1 + X / (Nat.nthRoot k X + 1)))
      else
        X ^ (2 * k * (r + 2))
termination_by r _X => r

/-- The actual Vinogradov mean value is bounded by the explicit recursive
Linnik envelope for every positive moment multiplier and interval length. -/
theorem vinogradovMeanValue_le_linnikVMVTRecursiveBound
    (k r X : Nat) (hk : 2 <= k) (hr : 0 < r) (hX : 0 < X) :
    vinogradovMeanValue k (k * r) X <=
      linnikVMVTRecursiveBound k r X := by
  induction r generalizing X with
  | zero => omega
  | succ r ih =>
      cases r with
      | zero =>
          simpa [linnikVMVTRecursiveBound] using
            vinogradovMeanValue_le_diagonal_factorial k X
      | succ r =>
          rw [linnikVMVTRecursiveBound]
          by_cases hlarge : k ^ k <= X
          next =>
            rw [if_pos hlarge]
            unfold linnikVMVTStep
            have hlow : 0 < 1 + X / (Nat.nthRoot k X + 1) := by
              simpa [Nat.add_comm] using
                (Nat.zero_lt_succ (X / (Nat.nthRoot k X + 1)))
            exact vinogradovMeanValue_le_nthRoot_recurrence
              k (r + 2) X (by omega) (by omega) (by nlinarith) hX hlarge
              |>.trans (linnikVMVTStep_mono k (r + 2) X _ _
                (ih (1 + X / (Nat.nthRoot k X + 1)) (by omega) hlow))
          next =>
            rw [if_neg hlarge]
            exact vinogradovMeanValue_le_trivial_kr k (r + 2) X

end Finset
