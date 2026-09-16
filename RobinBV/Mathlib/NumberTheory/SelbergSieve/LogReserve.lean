/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.SelbergSieve.IntervalBound

/-!
# A positive reserve in the finite Selberg denominator

The harmonic sum-integral comparison retains 1-log(2) beyond log(Q+1).
The resulting interval sieve uses the actual constructed Selberg optimizer
and its complete unit-remainder budget, with no distribution hypothesis.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat

theorem selberg_log_reserve_pos : 0 < 1-Real.log 2 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    (by norm_num : Not ((2 : Real) = 1))
  linarith only [h]

theorem harmonic_log_succ_reserve {Q : Nat} (hQ : 1 <= Q) :
    Real.log ((Q : Real)+1)+(1-Real.log 2) <= (harmonic Q : Real) := by
  have hab : (2 : Real) <= ((Q+1 : Nat) : Real) := by exact_mod_cast (show 2 <= Q+1 by omega)
  have hmono : AntitoneOn (fun x : Real => Inv.inv x)
      (Set.Icc ((2 : Nat) : Real) ((Q+1 : Nat) : Real)) :=
    inv_antitoneOn_Icc_right (by norm_num)
  have hsum := hmono.integral_le_sum_Ico (show 2 <= Q+1 by omega)
  norm_num only [Nat.cast_ofNat] at hsum
  have hzero : Not (Membership.mem (Set.uIcc (2 : Real) ((Q+1 : Nat) : Real)) 0) := by
    rw [Set.uIcc_of_le hab]
    intro h
    have hh := h.1
    norm_num at hh
  rw [integral_inv hzero] at hsum
  rw [Real.log_div (by positivity) (by norm_num)] at hsum
  have hhar : (harmonic Q : Real) =
      1+(Finset.Ico 2 (Q+1)).sum (fun d : Nat => Inv.inv (d : Real)) := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [<- Finset.sum_erase_add (Finset.Icc 1 Q) _ (Finset.left_mem_Icc.mpr hQ),
      add_comm, Nat.cast_one, inv_one, Finset.Icc_erase_left]
    have hsets : Finset.Ioc 1 Q = Finset.Ico 2 (Q+1) := by
      ext d
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hsets]
  simp only [Nat.cast_add, Nat.cast_one] at hsum
  linarith only [hsum, hhar]

theorem log_succ_add_reserve_le_squarefreeReciprocalTotientSum
    {Q : Nat} (hQ : 1 <= Q) :
    Real.log ((Q : Real)+1)+(1-Real.log 2) <= squarefreeReciprocalTotientSum Q :=
  (harmonic_log_succ_reserve hQ).trans (harmonic_le_squarefreeReciprocalTotientSum Q)

theorem card_sifted_interval_le_log_reserve {L U Q : Nat} (hLU : L <= U)
    (hQ : 1 <= Q) :
    (((Finset.Ioc L U).filter (fun m => Nat.Coprime (selbergPrimeProduct Q) m)).card : Real) <=
      ((U : Real)-L)/(Real.log ((Q : Real)+1)+(1-Real.log 2))+(Q : Real)^2 := by
  have hs := (intervalReciprocalSieve L U Q).siftedSum_le_finiteSelbergDenominator_add_card_sq
    (selbergDivisorSupport Q)
    (fun e he => selbergDivisorSupport_dvd he)
    (fun e he k hk => selbergDivisorSupport_down he hk)
    (one_mem_selbergDivisorSupport hQ)
    (fun d hd => intervalReciprocalSieve_unit_remainder hLU Q hd)
  rw [intervalReciprocalSieve_siftedSum, intervalReciprocalSieve_denominator] at hs
  have hmass : (0 : Real) <= (U : Real)-L := sub_nonneg.mpr (by exact_mod_cast hLU)
  have hQpos : (1 : Real) < (Q : Real)+1 := by
    have hQr : (1 : Real) <= Q := by exact_mod_cast hQ
    linarith
  have hlog := Real.log_pos hQpos
  have hdenpos : 0 < Real.log ((Q : Real)+1)+(1-Real.log 2) := by
    linarith only [hlog, selberg_log_reserve_pos]
  have hdenom := log_succ_add_reserve_le_squarefreeReciprocalTotientSum hQ
  have hratio : ((U : Real)-L)/squarefreeReciprocalTotientSum Q <=
      ((U : Real)-L)/(Real.log ((Q : Real)+1)+(1-Real.log 2)) :=
    _root_.div_le_div_of_nonneg_left hmass hdenpos hdenom
  have hc : ((selbergDivisorSupport Q).card : Real) <= Q := by
    exact_mod_cast card_selbergDivisorSupport_le Q
  have hsq : ((selbergDivisorSupport Q).card : Real)^2 <= (Q : Real)^2 := by
    have h := _root_.mul_le_mul hc hc
      (by positivity : (0 : Real) <= (selbergDivisorSupport Q).card)
      (by positivity : (0 : Real) <= Q)
    simpa only [pow_two] using h
  exact hs.trans (_root_.add_le_add hratio hsq)

end Nat
