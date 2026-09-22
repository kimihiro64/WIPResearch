/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LogPhaseStepIdentity
import RobinBV.Mathlib.Analysis.Complex.LogPhaseTransfer

/-!
# Forward D-spaced logarithmic phase transfer

This theorem composes the exact D-spaced phase identity with the stepped norm
transfer.  The forward order `k < h` is explicit; the swapped branch is a
separate finite symmetry consumer.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Complex

theorem log_phase_step_forward_transfer
    (Y P Q : Real) (N H D k h : Nat)
    (hY : 0 < Y) (hP : 0 < P) (hD : 0 < D)
    (horder : k < h)
    (hsmallL : Y * (((h-k)*D : Nat) : Real) <=
      Real.pi * (P + (k*D : Nat))^2)
    (hnum : P + (k*D : Nat) + (N : Real) + ((h-k)*D : Nat) + 1 <= Q)
    (hden : Y * (D : Real) <= Y * (((h-k)*D : Nat) : Real)) :
    norm ((Finset.range N).sum (fun j =>
      logPhaseCorrelationTerm Y P j (h*D) (k*D))) <=
      3 * Real.pi * Q^2 / (Y * D) := by
  let L : Nat := (h-k)*D
  let K : Nat := k*D
  have hL : 0 < L := by dsimp [L]; exact Nat.mul_pos (Nat.sub_pos_of_lt horder) hD
  have hform (j : Nat) : logPhaseCorrelationTerm Y P j (h*D) (k*D) =
      exp (I * ((-Y *
        (Real.log (P + (K : Real) + (j : Real) + (L : Real)) -
          Real.log (P + (K : Real) + (j : Real))) : Real) : Complex)) := by
    simpa [K, L] using log_phase_step_identity Y P j h k D horder
  have hsum :
      (Finset.range N).sum (fun j => logPhaseCorrelationTerm Y P j (h*D) (k*D)) =
        (Finset.range N).sum (fun j =>
          exp (I * ((-Y *
            (Real.log (P + (K : Real) + (j : Real) + (L : Real)) -
              Real.log (P + (K : Real) + (j : Real))) : Real) : Complex))) := by
    apply Finset.sum_congr rfl
    intro j _
    exact hform j
  rw [hsum]
  exact log_difference_norm_transfer Y (P + (K : Real)) Q N L D hY
    (by positivity) hL hD hsmallL (by simpa [K, L] using hnum) hden

theorem log_phase_step_swap_transfer
    (Y P Q : Real) (N H D k h : Nat)
    (hY : 0 < Y) (hP : 0 < P) (hD : 0 < D)
    (horder : h < k)
    (hsmallL : Y * (((k-h)*D : Nat) : Real) <=
      Real.pi * (P + (h*D : Nat))^2)
    (hnum : P + (h*D : Nat) + (N : Real) + ((k-h)*D : Nat) + 1 <= Q)
    (hden : Y * (D : Real) <= Y * (((k-h)*D : Nat) : Real)) :
    norm ((Finset.range N).sum (fun j =>
      logPhaseCorrelationTerm Y P j (h*D) (k*D))) <=
      3 * Real.pi * Q^2 / (Y * D) := by
  have hterm (j : Nat) :
      logPhaseCorrelationTerm Y P j (h*D) (k*D) =
        star (logPhaseCorrelationTerm Y P j (k*D) (h*D)) := by
    simp only [logPhaseCorrelationTerm]
    rw [star_mul, star_star]
  have hsum_aux : forall M : Nat,
      norm ((Finset.range M).sum (fun j =>
        logPhaseCorrelationTerm Y P j (h*D) (k*D))) =
      norm ((Finset.range M).sum (fun j =>
        logPhaseCorrelationTerm Y P j (k*D) (h*D))) := by
    intro M
    have hs :
        (Finset.range M).sum (fun j =>
          logPhaseCorrelationTerm Y P j (h*D) (k*D)) =
        star ((Finset.range M).sum (fun j =>
          logPhaseCorrelationTerm Y P j (k*D) (h*D))) := by
      induction M with
      | zero => simp
      | succ M ih =>
          rw [Finset.sum_range_succ, Finset.sum_range_succ, star_add]
          calc
            (Finset.range M).sum (fun j =>
                logPhaseCorrelationTerm Y P j (h*D) (k*D)) +
                logPhaseCorrelationTerm Y P M (h*D) (k*D) =
              star ((Finset.range M).sum (fun j =>
                logPhaseCorrelationTerm Y P j (k*D) (h*D))) +
                logPhaseCorrelationTerm Y P M (h*D) (k*D) := by rw [ih]
            _ = star ((Finset.range M).sum (fun j =>
                logPhaseCorrelationTerm Y P j (k*D) (h*D))) +
                star (logPhaseCorrelationTerm Y P M (k*D) (h*D)) := by
                  rw [hterm]
    rw [hs, norm_star]
  rw [hsum_aux N]
  exact log_phase_step_forward_transfer Y P Q N H D h k hY hP hD horder
    hsmallL hnum hden

end Complex
