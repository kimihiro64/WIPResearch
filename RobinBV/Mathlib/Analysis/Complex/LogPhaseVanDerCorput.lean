/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import RobinBV.Mathlib.Analysis.Complex.LogPhaseCorrelationUniform
import RobinBV.Mathlib.Analysis.Complex.UniformVanDerCorput

/-!
# Finite logarithmic-phase van der Corput bound

This module connects the uniform logarithmic Type-II correlations to the
finite Gram consumer.  It proves an explicit shifted logarithmic Dirichlet
bound with all height, shift, diagonal, off-diagonal, and endpoint costs
visible.  It is a finite analytic input, not the full Korobov--Vinogradov
saving or a prime-count theorem.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Complex

theorem log_phase_van_der_corput_bound
    (Y P : Real) (N H : Nat) (hY : 0 < Y) (hP : 0 < P)
    (hH : 0 < H) (hsmall : Y * (H : Real) <= Real.pi * P^2) :
    (H : Real) * norm ((Finset.range N).sum (fun j =>
      exp (I * ((-Y * Real.log (P + (j : Real)) : Real) : Complex)))) <=
      Real.sqrt ((N : Real) *
        ((H : Real) * N + ((H : Real)^2 - H) *
          (3 * Real.pi * (P + N + H + 1)^2 / Y))) +
        (H : Real) * (H - 1) := by
  let b : Nat -> Complex := fun j =>
    exp (I * ((-Y * Real.log (P + (j : Real)) : Real) : Complex))
  let a : Nat -> Nat -> Complex := fun j h => b (j+h)
  have ha : forall j, norm (b j) <= 1 := by
    intro j
    dsimp [b]
    rw [mul_comm I]
    exact (norm_exp_ofReal_mul_I _).le
  have ha_shift : forall j h, a j h = b (j+h) := by
    intro j h
    rfl
  have hdiag : forall h, Membership.mem (Finset.range H) h ->
      ((Finset.range N).sum (fun j => a j h * star (a j h))).re <= (N : Real) := by
    intro h _
    have hterm (j : Nat) : (a j h * star (a j h)).re = 1 := by
      dsimp [a, b]
      have hz : norm (exp (I * ((-Y * Real.log
          (P + (j + h : Nat)) : Real) : Complex))) = 1 := by
        rw [mul_comm I]
        exact norm_exp_ofReal_mul_I _
      calc
        _ = norm (exp (I * ((-Y * Real.log
            (P + (j + h : Nat)) : Real) : Complex))) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [mul_re, star_def, conj_re, conj_im]
        _ = 1 := by rw [hz]; norm_num
    calc
      _ = (Finset.range N).sum (fun j =>
          (a j h * star (a j h)).re) := by
        exact map_sum reAddGroupHom (fun j => a j h * star (a j h)) _
      _ = (Finset.range N).sum (fun _ => (1 : Real)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hterm j
      _ = (N : Real) := by simp
      _ <= (N : Real) := le_rfl
  have hoff : forall h, Membership.mem (Finset.range H) h ->
      forall k, Membership.mem (Finset.range H) k -> Not (h = k) ->
        ((Finset.range N).sum (fun j => a j h * star (a j k))).re <=
          3 * Real.pi * (P + (N : Real) + H + 1)^2 / Y := by
    intro h hh k hk hne
    have hc := log_shift_correlation_uniform Y P N H hY hP hsmall
      h (Finset.mem_range.mp hh) k (Finset.mem_range.mp hk) hne
    simpa [a, b, logPhaseCorrelationTerm] using hc
  have hH1 : 1 <= (H : Real) := by exact_mod_cast (Nat.succ_le_iff.mp hH)
  have hE : 0 <= (N : Real) *
      ((H : Real) * N + ((H : Real)^2 - H) *
        (3 * Real.pi * (P + N + H + 1)^2 / Y)) := by
    have hquad : 0 <= (H : Real)^2 - H := by nlinarith
    positivity
  have hmain := norm_sum_mul_shift_le_of_uniform_correlation
    b a N H (N : Real) (3 * Real.pi * (P + (N : Real) + H + 1)^2 / Y)
    ha ha_shift hdiag hoff hE
  simpa [a, b] using hmain

end Complex
