/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LogPhaseStepVanDerCorput

/-!
# Explicit logarithmic Type-II input for the Korobov--Vinogradov route

This file records the strongest currently proved finite exponential-sum
ingredient needed by a Korobov--Vinogradov construction. It is an explicit
unit-coefficient logarithmic phase estimate with an arbitrary integral shift,
followed by its unit-shift specialization. It is not itself a zero-free-region
or zero-density theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace RobinBV.Sieve

theorem korobov_vinogradov_typeII_log_phase_bound_of_spacing
    (Y P Q : Real) (N H D : Nat) (hY : 0 < Y) (hP : 0 < P)
    (hH : 0 < H) (hD : 0 < D)
    (hsmall : Y * (((H * D : Nat) : Real)) <= Real.pi * P^2)
    (hQ : P + (N : Real) + ((H * D : Nat) : Real) + 1 <= Q) :
    (H : Real) * norm (Finset.sum (Finset.range N) (fun j =>
      Complex.exp (Complex.I * ((-Y * Real.log (P + (j : Real)) : Real) : Complex)))) <=
      Real.sqrt ((N : Real) *
        ((H : Real) * N + ((H : Real)^2 - H) *
          (3 * Real.pi * Q^2 / (Y * D)))) +
        (D : Real) * H * (H - 1) := by
  have hmain := Complex.log_phase_step_van_der_corput_global
    Y P Q N H D hY hP hH hD (by simpa using hsmall) (by simpa using hQ)
  simpa using hmain

theorem korobov_vinogradov_typeII_log_phase_bound
    (Y P Q : Real) (N H : Nat) (hY : 0 < Y) (hP : 0 < P)
    (hH : 0 < H) (hsmall : Y * ((H : Real) : Real) <= Real.pi * P^2)
    (hQ : P + (N : Real) + (H : Real) + 1 <= Q) :
    (H : Real) * norm (Finset.sum (Finset.range N) (fun j =>
      Complex.exp (Complex.I * ((-Y * Real.log (P + (j : Real)) : Real) : Complex)))) <=
      Real.sqrt ((N : Real) *
        ((H : Real) * N + ((H : Real)^2 - H) *
          (3 * Real.pi * Q^2 / Y))) +
        (H : Real) * (H - 1) := by
  have hmain := korobov_vinogradov_typeII_log_phase_bound_of_spacing
    Y P Q N H 1 hY hP hH (by norm_num) (by simpa using hsmall) (by simpa using hQ)
  simpa using hmain

theorem korobov_vinogradov_typeII_log_phase_growth
    (Y P Q : Real) (N H : Nat) (hY : 0 < Y) (hP : 0 < P)
    (hH : 0 < H) (hsmall : Y * ((H : Real) : Real) <= Real.pi * P^2)
    (hQ : P + (N : Real) + (H : Real) + 1 <= Q) :
    norm (Finset.sum (Finset.range N) (fun j =>
      Complex.exp (Complex.I * ((-Y * Real.log (P + (j : Real)) : Real) : Complex)))) <=
      Real.sqrt ((N : Real) *
        ((H : Real) * N + ((H : Real)^2 - H) *
          (3 * Real.pi * Q^2 / Y))) / (H : Real) + (H : Real) - 1 := by
  have hmain := korobov_vinogradov_typeII_log_phase_bound
    Y P Q N H hY hP hH hsmall hQ
  have hHr : 0 < (H : Real) := by exact_mod_cast hH
  have hmul : (H : Real) * norm (Finset.sum (Finset.range N) (fun j =>
      Complex.exp (Complex.I * ((-Y * Real.log (P + (j : Real)) : Real) : Complex)))) <=
      (H : Real) * (Real.sqrt ((N : Real) *
        ((H : Real) * N + ((H : Real)^2 - H) *
          (3 * Real.pi * Q^2 / Y))) / (H : Real) + (H : Real) - 1) := by
    calc
      _ <= Real.sqrt ((N : Real) *
          ((H : Real) * N + ((H : Real)^2 - H) *
            (3 * Real.pi * Q^2 / Y))) + (H : Real) * (H - 1) := hmain
      _ = (H : Real) * (Real.sqrt ((N : Real) *
          ((H : Real) * N + ((H : Real)^2 - H) *
            (3 * Real.pi * Q^2 / Y))) / (H : Real) + (H : Real) - 1) := by
        field_simp
        ring
  exact le_of_mul_le_mul_left hmul hHr

end RobinBV.Sieve
