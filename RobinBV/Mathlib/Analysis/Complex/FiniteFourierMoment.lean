/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import RobinBV.Mathlib.Analysis.Complex.DifferenceSecondMoment

/-!
# Finite Fourier second and fourth moments

An explicit oscillatory integral bound retains the zero-frequency case and
the full finite pair or quadruple domain. The fourth-moment estimate is the
second-moment estimate applied to the pair-sum frequencies, with no spacing,
coefficient sign, or arithmetic assumptions. This supplies a Fourier
reduction only; it does not estimate additive energy of zeta zeros.
-/

set_option autoImplicit false

open ComplexConjugate

namespace Complex

noncomputable def finiteFourierWindow (a b d : Real) : Real := by
  classical
  exact if d = 0 then b-a else min (b-a) (2 / abs d)


theorem norm_integral_phase_le_window (a b d : Real) (hab : a <= b) :
    norm (intervalIntegral (fun t : Real => exp (I*(d : Complex)*(t : Complex)))
      a b MeasureTheory.volume) <= finiteFourierWindow a b d := by
  classical
  have hl : norm (intervalIntegral
      (fun t : Real => exp (I*(d : Complex)*(t : Complex)))
      a b MeasureTheory.volume) <= b-a := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b)
      (fun t ht => (finite_fourier_phase_norm d t).le)
    simpa only [one_mul, abs_of_nonneg (sub_nonneg.mpr hab)] using h
  by_cases hd : d = 0
  next => simpa only [finiteFourierWindow, if_pos hd] using hl
  next =>
    simp only [finiteFourierWindow, if_neg hd]
    apply le_min hl
    have hn : Not (I*(d : Complex) = 0) :=
      mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hd)
    rw [integral_exp_mul_complex hn, norm_div]
    have htop : norm (exp (I*(d : Complex)*(b : Complex)) -
        exp (I*(d : Complex)*(a : Complex))) <= 2 := by
      calc
        _ <= norm (exp (I*(d : Complex)*(b : Complex))) +
            norm (exp (I*(d : Complex)*(a : Complex))) := norm_sub_le _ _
        _ = 2 := by rw [finite_fourier_phase_norm, finite_fourier_phase_norm]; norm_num
    calc
      _ <= 2 / norm (I*(d : Complex)) :=
        div_le_div_of_nonneg_right htop (norm_nonneg _)
      _ = 2 / abs d := by simp [norm_real, Real.norm_eq_abs]



theorem integral_norm_sq_exp_sum_le_window {v : Type*} (s : Finset v)
    (c : v -> Complex) (g : v -> Real) (a b : Real) (hab : a <= b) :
    intervalIntegral (fun t : Real =>
      norm (s.sum (fun i => c i * exp (I*(g i : Complex)*(t : Complex)))) ^ 2)
      a b MeasureTheory.volume <=
      s.sum (fun i => s.sum (fun j =>
        norm (c i) * norm (c j) * finiteFourierWindow a b (g i-g j))) := by
  let q : v -> v -> Real -> Complex := fun i j t =>
    (c i * conj (c j)) * exp (I*((g i-g j : Real) : Complex)*(t : Complex))
  have hc (i j : v) : Continuous (q i j) := by unfold q; fun_prop
  have he : ((intervalIntegral (fun t : Real =>
      norm (s.sum (fun i => c i * exp (I*(g i : Complex)*(t : Complex)))) ^ 2)
      a b MeasureTheory.volume : Real) : Complex) =
      s.sum (fun i => s.sum (fun j => (c i * conj (c j)) *
        intervalIntegral (fun t : Real =>
          exp (I*((g i-g j : Real) : Complex)*(t : Complex)))
          a b MeasureTheory.volume)) := by
    rw [<- intervalIntegral.integral_ofReal]
    simp_rw [finite_fourier_norm_sq_expansion]
    change intervalIntegral (fun t => s.sum (fun i => s.sum (fun j => q i j t)))
      a b MeasureTheory.volume = _
    rw [intervalIntegral.integral_finsetSum (fun i hi =>
      (continuous_finsetSum _ (fun j hj => hc i j)).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum (fun j hj => (hc i j).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl
    intro j hj
    exact intervalIntegral.integral_const_mul _ _
  have hn : 0 <= intervalIntegral (fun t : Real =>
      norm (s.sum (fun i => c i * exp (I*(g i : Complex)*(t : Complex)))) ^ 2)
      a b MeasureTheory.volume :=
    intervalIntegral.integral_nonneg hab (fun t ht => sq_nonneg _)
  calc
    _ = norm ((intervalIntegral (fun t : Real =>
        norm (s.sum (fun i => c i * exp (I*(g i : Complex)*(t : Complex)))) ^ 2)
        a b MeasureTheory.volume : Real) : Complex) := by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
    _ = _ := congrArg norm he
    _ <= _ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul, norm_conj]
      exact mul_le_mul_of_nonneg_left (norm_integral_phase_le_window a b (g i-g j) hab)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem integral_norm_fourth_exp_sum_le_window {v : Type*} (s : Finset v)
    (c : v -> Complex) (g : v -> Real) (a b : Real) (hab : a <= b) :
    intervalIntegral (fun t : Real =>
      norm (s.sum (fun i => c i * exp (I*(g i : Complex)*(t : Complex)))) ^ 4)
      a b MeasureTheory.volume <=
      s.sum (fun i => s.sum (fun j => s.sum (fun k => s.sum (fun l =>
        (norm (c i) * norm (c j)) * (norm (c k) * norm (c l)) *
          finiteFourierWindow a b (g i+g j-g k-g l))))) := by
  classical
  have hsum (t : Real) :
      (SProd.sprod s s : Finset (Prod v v)).sum (fun p =>
        (c p.1*c p.2)*exp (I*((g p.1+g p.2 : Real) : Complex)*(t : Complex))) =
      (s.sum (fun i => c i*exp (I*(g i : Complex)*(t : Complex)))) ^ 2 := by
    rw [Finset.sum_product, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [show I*((g i+g j : Real) : Complex)*(t : Complex) =
        I*(g i : Complex)*(t : Complex)+I*(g j : Complex)*(t : Complex) by
      push_cast
      ring, exp_add]
    ring
  have h := integral_norm_sq_exp_sum_le_window (SProd.sprod s s : Finset (Prod v v))
    (fun p => c p.1*c p.2) (fun p => g p.1+g p.2) a b hab
  simp_rw [hsum, norm_pow] at h
  simpa only [<- pow_mul, Finset.sum_product, norm_mul, sub_add_eq_sub_sub] using h

end Complex
