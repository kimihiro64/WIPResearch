/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.IntervalDivisorError
import RobinBV.Mathlib.NumberTheory.SelbergSieve.IntervalSetup

/-!
# IntervalBound

Finite Selberg sieve input, proved from Mathlib primitives.
The classical sieve argument follows D. R. Heath-Brown, Lectures on sieves,
Sections 2-3 (https://arxiv.org/abs/math/0209360).
No prime-distribution or unproved analytic hypothesis is introduced.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat

theorem intervalReciprocalSieve_multSum (L U Q d : Nat) :
    (intervalReciprocalSieve L U Q).multSum d =
      (((Finset.Ioc L U).filter (fun m => Dvd.dvd d m)).card : Real) := by
  change (Finset.Ioc L U).sum (fun m => if Dvd.dvd d m then (1 : Real) else 0) = _
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]

theorem intervalReciprocalSieve_unit_remainder {L U : Nat} (hLU : L <= U)
    (Q : Nat) {d : Nat} (hd : Membership.mem (intervalReciprocalSieve L U Q).prodPrimes.divisors d) :
    abs ((intervalReciprocalSieve L U Q).rem d) <= 1 := by
  have hd0 := Nat.pos_of_mem_divisors hd
  have he := Nat.Ioc_filter_dvd_abs_unit_error hLU hd0
  have hrem : (intervalReciprocalSieve L U Q).rem d =
      (((Finset.Ioc L U).filter (fun m => Dvd.dvd d m)).card : Real) -
        ((U : Real)-L)/(d : Real) := by
    unfold BoundingSieve.rem
    rw [intervalReciprocalSieve_multSum]
    change _ - Inv.inv (d : Real)*((U : Real)-L) =
      _ - ((U : Real)-L)/(d : Real)
    ring
  rw [hrem]
  exact le_of_lt he

theorem intervalReciprocalSieve_siftedSum (L U Q : Nat) :
    (intervalReciprocalSieve L U Q).siftedSum =
      (((Finset.Ioc L U).filter (fun m => Nat.Coprime (selbergPrimeProduct Q) m)).card : Real) := by
  change (Finset.Ioc L U).sum (fun m =>
    if Nat.Coprime (selbergPrimeProduct Q) m then (1 : Real) else 0) = _
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]

/-- Complete interval sieve estimate, with the actual interval remainders
proved above and the actual optimizer already constructed and checked. -/
theorem card_sifted_interval_le_log_sieve {L U Q : Nat} (hLU : L <= U)
    (hQ : 1 <= Q) :
    (((Finset.Ioc L U).filter (fun m => Nat.Coprime (selbergPrimeProduct Q) m)).card : Real) <=
      ((U : Real)-L)/Real.log ((Q : Real)+1)+(Q : Real)^2 := by
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
  have hdenom := log_succ_le_squarefreeReciprocalTotientSum Q
  have hratio : ((U : Real)-L)/squarefreeReciprocalTotientSum Q <=
      ((U : Real)-L)/Real.log ((Q : Real)+1) :=
    _root_.div_le_div_of_nonneg_left hmass hlog hdenom
  have hc : ((selbergDivisorSupport Q).card : Real) <= Q := by
    exact_mod_cast card_selbergDivisorSupport_le Q
  have hsq : ((selbergDivisorSupport Q).card : Real)^2 <= (Q : Real)^2 := by
    have h := _root_.mul_le_mul hc hc
      (by positivity : (0 : Real) <= (selbergDivisorSupport Q).card)
      (by positivity : (0 : Real) <= Q)
    simpa only [pow_two] using h
  exact hs.trans (_root_.add_le_add hratio hsq)

end Nat
