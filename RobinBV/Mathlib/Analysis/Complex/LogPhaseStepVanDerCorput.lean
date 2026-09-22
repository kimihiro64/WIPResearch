/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import RobinBV.Mathlib.Analysis.Complex.LogPhaseStepForwardTransfer
import RobinBV.Mathlib.Analysis.Complex.UniformVanDerCorput

/-!
# D-spaced logarithmic-phase van der Corput bound
-/

set_option autoImplicit false
open scoped BigOperators

namespace Complex

theorem log_phase_step_van_der_corput_bound
    (Y P Q : Real) (N H D : Nat) (hY : 0 < Y) (hP : 0 < P)
    (hD : 0 < D)
    (hlocal : forall lo hi : Nat, lo < H -> hi < H -> lo < hi ->
      Y * (((hi-lo)*D : Nat) : Real) <=
        Real.pi * (P + (lo*D : Nat))^2 /\
      P + (lo*D : Nat) + (N : Real) + ((hi-lo)*D : Nat) + 1 <= Q /\
      Y * (D : Real) <= Y * (((hi-lo)*D : Nat) : Real)) :
    (H : Real) * norm ((Finset.range N).sum (fun j =>
      exp (I * ((-Y * Real.log (P + (j : Real)) : Real) : Complex)))) <=
      Real.sqrt ((N : Real) *
        ((H : Real) * N + ((H : Real)^2 - H) *
          (3 * Real.pi * Q^2 / (Y * D)))) +
        (D : Real) * H * (H - 1) := by
  let b : Nat -> Complex := fun j =>
    exp (I * ((-Y * Real.log (P + (j : Real)) : Real) : Complex))
  let a : Nat -> Nat -> Complex := fun j h => b (j+h*D)
  have ha : forall j, norm (b j) <= 1 := by
    intro j
    dsimp [b]
    rw [mul_comm I]
    exact (norm_exp_ofReal_mul_I _).le
  have ha_shift : forall j h, a j h = b (j+h*D) := by
    intro j h
    rfl
  have hdiag : forall h, Membership.mem (Finset.range H) h ->
      ((Finset.range N).sum (fun j => a j h * star (a j h))).re <= (N : Real) := by
    intro h _
    have hterm (j : Nat) : (a j h * star (a j h)).re = 1 := by
      dsimp [a, b]
      have hz : norm (exp (I * ((-Y * Real.log
          (P + (j + h*D : Nat)) : Real) : Complex))) = 1 := by
        rw [mul_comm I]
        exact norm_exp_ofReal_mul_I _
      calc
        _ = norm (exp (I * ((-Y * Real.log
            (P + (j + h*D : Nat)) : Real) : Complex))) ^ 2 := by
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
          3 * Real.pi * Q^2 / (Y * D) := by
    intro h hh k hk hne
    have hhk : Or (h < k) (k < h) := by omega
    rcases hhk with hlt | hgt
    case inl =>
      have hl := hlocal h k (Finset.mem_range.mp hh) (Finset.mem_range.mp hk) hlt
      have hc := log_phase_step_swap_transfer Y P Q N H D k h hY hP hD hlt
        hl.1 hl.2.1 hl.2.2
      have hsum :
          ((Finset.range N).sum (fun j => a j h * star (a j k))).re =
          ((Finset.range N).sum (fun j =>
            logPhaseCorrelationTerm Y P j (h*D) (k*D))).re := by
        apply congrArg Complex.re
        apply Finset.sum_congr rfl
        intro j _
        rfl
      rw [hsum]
      exact le_trans (re_le_norm _) hc
    case inr =>
      have hl := hlocal k h (Finset.mem_range.mp hk) (Finset.mem_range.mp hh) hgt
      have hc := log_phase_step_forward_transfer Y P Q N H D k h hY hP hD hgt
        hl.1 hl.2.1 hl.2.2
      have hsum :
          ((Finset.range N).sum (fun j => a j h * star (a j k))).re =
          ((Finset.range N).sum (fun j =>
            logPhaseCorrelationTerm Y P j (h*D) (k*D))).re := by
        apply congrArg Complex.re
        apply Finset.sum_congr rfl
        intro j _
        rfl
      rw [hsum]
      exact le_trans (re_le_norm _) hc
  have hE : 0 <= (N : Real) *
      ((H : Real) * N + ((H : Real)^2 - H) *
        (3 * Real.pi * Q^2 / (Y * D))) := by
    have hquad : 0 <= (H : Real)^2 - H := by
      cases H with
      | zero => norm_num
      | succ H =>
          have hH1 : (1 : Real) <= (Nat.succ H : Nat) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le H)
          nlinarith
    have hden : 0 < Y * (D : Real) := by
      exact mul_pos hY (by exact_mod_cast hD)
    positivity
  have hmain := norm_sum_mul_step_shift_le_of_uniform_correlation
    b a N H D (N : Real) (3 * Real.pi * Q^2 / (Y * D))
    ha ha_shift hdiag hoff hE
  simpa [a, b] using hmain

theorem log_phase_step_van_der_corput_global
    (Y P Q : Real) (N H D : Nat) (hY : 0 < Y) (hP : 0 < P)
    (hH : 0 < H) (hD : 0 < D)
    (hsmall : Y * ((H*D : Nat) : Real) <= Real.pi * P^2)
    (hQ : P + (N : Real) + ((H*D : Nat) : Real) + 1 <= Q) :
    (H : Real) * norm ((Finset.range N).sum (fun j =>
      exp (I * ((-Y * Real.log (P + (j : Real)) : Real) : Complex)))) <=
      Real.sqrt ((N : Real) *
        ((H : Real) * N + ((H : Real)^2 - H) *
          (3 * Real.pi * Q^2 / (Y * D)))) +
        (D : Real) * H * (H - 1) := by
  apply log_phase_step_van_der_corput_bound Y P Q N H D hY hP hD
  intro lo hi hlo hhi hord
  have hgap : (hi-lo)*D <= H*D := by
    apply Nat.mul_le_mul_right
    have hsub : hi-lo <= H := by omega
    exact hsub
  have hgapR : (((hi-lo)*D : Nat) : Real) <= ((H*D : Nat) : Real) := by
    exact_mod_cast hgap
  have hbase : (P : Real) <= P + (lo*D : Nat) := by
    have hnonneg : (0 : Real) <= (lo*D : Nat) := by positivity
    linarith
  have hsq : P^2 <= (P + (lo*D : Nat))^2 := by nlinarith
  have hsmall' : Y * (((hi-lo)*D : Nat) : Real) <=
      Real.pi * (P + (lo*D : Nat))^2 := by
    calc
      Y * (((hi-lo)*D : Nat) : Real) <= Y * ((H*D : Nat) : Real) := by
        exact mul_le_mul_of_nonneg_left hgapR (le_of_lt hY)
      _ <= Real.pi * P^2 := hsmall
      _ <= Real.pi * (P + (lo*D : Nat))^2 := by
        exact mul_le_mul_of_nonneg_left hsq (le_of_lt Real.pi_pos)
  have hnum' : P + (lo*D : Nat) + (N : Real) +
      ((hi-lo)*D : Nat) + 1 <= Q := by
    have hsumNat : lo*D + (hi-lo)*D = hi*D := by
      rw [<- Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt hord)]
    have hsumR : ((lo*D : Nat) : Real) + (((hi-lo)*D : Nat) : Real) =
        ((hi*D : Nat) : Real) := by
      exact_mod_cast hsumNat
    have hhiD : hi*D <= H*D := Nat.mul_le_mul_right D (Nat.le_of_lt hhi)
    have hhiDR : ((hi*D : Nat) : Real) <= ((H*D : Nat) : Real) := by
      exact_mod_cast hhiD
    linarith
  have hone : 1 <= hi-lo := Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hord)
  have hdenNat : D <= (hi-lo)*D := by
    have ht := Nat.mul_le_mul_right D hone
    simpa using ht
  have hdenR : (D : Real) <= (((hi-lo)*D : Nat) : Real) := by
    exact_mod_cast hdenNat
  have hden' : Y * (D : Real) <= Y * (((hi-lo)*D : Nat) : Real) := by
    exact mul_le_mul_of_nonneg_left hdenR (le_of_lt hY)
  exact And.intro hsmall' (And.intro hnum' hden')

end Complex
