/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import RobinBV.Mathlib.Analysis.Complex.LogPhaseCorrelation
import RobinBV.Mathlib.Analysis.Complex.ReciprocalSum

/-!
# Uniform logarithmic Type-II correlations

This module makes the off-diagonal correlation constant uniform over a finite
shift window, including the swapped-index symmetry and all small-increment
conditions.  It is the analytic input for the finite Gram consumer; it is not
yet the full Korobov--Vinogradov saving.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Complex

theorem log_phase_product_identity
    (Y P : Real) (j h k : Nat) :
    exp (I * ((-Y * Real.log (P + (j + h : Nat)) : Real) : Complex)) *
      star (exp (I * ((-Y * Real.log (P + (j + k : Nat)) : Real) : Complex))) =
    exp (I * ((-Y *
      (Real.log (P + (j + h : Nat)) - Real.log (P + (j + k : Nat))) : Real) : Complex)) := by
  have hprod := exp_phase_mul_star
    (-Y * Real.log (P + (j + h : Nat)))
    (-Y * Real.log (P + (j + k : Nat)))
  rw [hprod]
  congr 1
  push_cast
  ring

noncomputable def logPhaseCorrelationTerm (Y P : Real) (j h k : Nat) : Complex :=
  exp (I * ((-Y * Real.log (P + (j + h : Nat)) : Real) : Complex)) *
    star (exp (I * ((-Y * Real.log (P + (j + k : Nat)) : Real) : Complex)))

theorem log_shift_correlation_uniform
    (Y P : Real) (N H : Nat) (hY : 0 < Y) (hP : 0 < P)
    (hsmall : Y * (H : Real) <= Real.pi * P^2) :
    forall h, h < H -> forall k, k < H -> Not (h = k) ->
      ((Finset.range N).sum (fun j => logPhaseCorrelationTerm Y P j h k)).re <=
        3 * Real.pi * (P + (N : Real) + H + 1)^2 / Y := by
  let C : Real := 3 * Real.pi * (P + (N : Real) + H + 1)^2 / Y
  have hforward : forall (k h : Nat), k < H -> h < H -> k < h ->
      ((Finset.range N).sum (fun j => logPhaseCorrelationTerm Y P j h k)).re <= C := by
    intro k h hk hh horder
    let L : Nat := h-k
    have hL : 0 < L := by dsimp [L]; omega
    have hLH : L <= H := by dsimp [L]; omega
    have hsmallL : Y * (L : Real) <= Real.pi * (P + (k : Real))^2 := by
      have hLr : (L : Real) <= (H : Real) := by exact_mod_cast hLH
      have hbase : P^2 <= (P + (k : Real))^2 := by
        have hk0 : 0 <= (k : Real) := by positivity
        nlinarith [mul_nonneg hP.le hk0, sq_nonneg (k : Real)]
      have hleft := mul_le_mul_of_nonneg_left hLr hY.le
      have hright := mul_le_mul_of_nonneg_right hbase Real.pi_pos.le
      nlinarith [hsmall]
    have hform (j : Nat) : logPhaseCorrelationTerm Y P j h k =
        exp (I * ((-Y *
          (Real.log (P + (k : Real) + (j : Real) + (L : Real)) -
            Real.log (P + (k : Real) + (j : Real))) : Real) : Complex)) := by
      rw [show logPhaseCorrelationTerm Y P j h k =
        exp (I * ((-Y *
          (Real.log (P + (j + h : Nat)) - Real.log (P + (j + k : Nat))) : Real) : Complex)) by
            dsimp [logPhaseCorrelationTerm]
            exact log_phase_product_identity Y P j h k]
      congr 1
      have hidx : j + h = k + j + (h - k) := by omega
      rw [hidx]
      dsimp [L]
      push_cast
      ring
    simp_rw [hform]
    have hc := norm_sum_exp_log_difference_le Y (P + (k : Real)) N L
      hY (by positivity) hL hsmallL
    have hnum : P + (k : Real) + (N : Real) + L + 1 <=
        P + (N : Real) + H + 1 := by
      have hkR : (k : Real) <= (H : Real) := by exact_mod_cast (Nat.le_of_lt hk)
      have hLR : (L : Real) <= (H : Real) := by exact_mod_cast hLH
      have hsum : k + L = h := by dsimp [L]; omega
      have hsumR : (k : Real) + (L : Real) = (h : Real) := by exact_mod_cast hsum
      have hhR : (h : Real) <= (H : Real) := by exact_mod_cast (Nat.le_of_lt hh)
      linarith
    have hnum' : 3 * Real.pi * (P + (k : Real) + (N : Real) + L + 1)^2 <=
        3 * Real.pi * (P + (N : Real) + H + 1)^2 := by gcongr
    have hden : Y <= Y * (L : Real) := by
      have hL1 : 1 <= (L : Real) := by exact_mod_cast (Nat.succ_le_iff.mp hL)
      nlinarith
    dsimp [C]
    exact (re_le_norm _).trans (calc
      _ <= 3 * Real.pi * (P + (k : Real) + (N : Real) + L + 1)^2 /
          (Y * (L : Real)) := hc
      _ <= 3 * Real.pi * (P + (N : Real) + H + 1)^2 /
          (Y * (L : Real)) := div_le_div_of_nonneg_right hnum' (by positivity)
      _ <= 3 * Real.pi * (P + (N : Real) + H + 1)^2 / Y :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
  intro h hh k hk hne
  by_cases horder : k < h
  next => exact hforward k h hk hh horder
  next =>
    have horder' : h < k := by omega
    have hsymmetric :
        ((Finset.range N).sum (fun j => logPhaseCorrelationTerm Y P j h k)).re =
        ((Finset.range N).sum (fun j => logPhaseCorrelationTerm Y P j k h)).re := by
      have hr (f : Nat -> Complex) : ((Finset.range N).sum f).re =
          (Finset.range N).sum (fun j => (f j).re) := map_sum reAddGroupHom f _
      rw [hr, hr]
      apply Finset.sum_congr rfl
      intro j _
      simp only [logPhaseCorrelationTerm, mul_re, star_def, conj_re, conj_im]
      ring
    rw [hsymmetric]
    exact hforward h k hh hk horder'

end Complex
