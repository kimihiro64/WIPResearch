/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.SpecialFunctions.Log.SieveCutoff
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalRoughAllowance
import RobinBV.Mathlib.NumberTheory.SelbergSieve.IntervalBound

/-!
# SquareIntervalRoughLogBound

Explicit finite interval estimates used in signed prime-candidate accounting.
All constants and endpoint conditions are retained; no prime-existence result
is claimed by a negative lower envelope.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

theorem squareRoughSurvivors_subset_sifted_interval {n Q : Nat}
    (hQ : Q*Q <= n) :
    squareRoughSurvivors n <= (Finset.Ioc (n*n) (n*n+2*n)).filter
      (fun m => Nat.Coprime (Nat.selbergPrimeProduct Q) m) := by
  intro m hm
  have hd := Finset.mem_filter.mp hm
  have hhi := Finset.mem_range.mp hd.1
  have hlo := hd.2.2.1
  have hrough := hd.2.2.2.2
  apply Finset.mem_filter.mpr
  refine And.intro (Finset.mem_Ioc.mpr (And.intro hlo (by nlinarith))) ?_
  apply Nat.coprime_of_dvd
  intro p hp hpP hpm
  have hpQ := (Nat.prime_dvd_selbergPrimeProduct_iff hp).mp hpP
  have hs := Nat.mul_le_mul hpQ hpQ
  have hb := hrough p hp hpm
  omega

theorem card_squareRoughSurvivors_le_log_sieve {n Q : Nat}
    (hQ1 : 1 <= Q) (hQ : Q*Q <= n) :
    ((squareRoughSurvivors n).card : Real) <=
      2*(n : Real)/Real.log ((Q : Real)+1)+(Q : Real)^2 := by
  have hc : ((squareRoughSurvivors n).card : Real) <=
      (((Finset.Ioc (n*n) (n*n+2*n)).filter
        (fun m => Nat.Coprime (Nat.selbergPrimeProduct Q) m)).card : Real) := by
    exact_mod_cast Finset.card_le_card (squareRoughSurvivors_subset_sifted_interval hQ)
  have hs := Nat.card_sifted_interval_le_log_sieve
    (L := n*n) (U := n*n+2*n) (by omega) hQ1
  push_cast at hs
  have he : (n : Real)*n+2*n-n*n = 2*n := by ring
  rw [he] at hs
  exact hc.trans hs

/-- Fully explicit rough-survivor estimate, with no unestimated sieve error. -/
theorem card_squareRoughSurvivors_le_explicit_log {n : Nat} (hn : 4 <= n) :
    ((squareRoughSurvivors n).card : Real) <=
      4*(n : Real)/Real.squareSieveDenominator n+
        (n : Real)/(Real.log n)^2 := by
  have hn4 : (4 : Real) <= n := by exact_mod_cast hn
  have hn1 : (1 : Real) < n := by linarith
  let Q := Real.squareSieveCutoff (n : Real)
  have hQ1 : 1 <= Q := Real.one_le_squareSieveCutoff hn1
  have hQsq := Real.squareSieveCutoff_sq_le_self hn4
  have hQ : Q*Q <= n := by
    have hQr : (Q : Real)*(Q : Real) <= n := by simpa only [pow_two] using hQsq
    exact_mod_cast hQr
  have hs := card_squareRoughSurvivors_le_log_sieve hQ1 hQ
  have hD := Real.squareSieveDenominator_pos hn1
  have hlog := Real.squareSieveCutoff_log_lower hn1
  have hmain : 2*(n : Real)/Real.log ((Q : Real)+1) <=
      2*(n : Real)/(Real.squareSieveDenominator n/2) :=
    _root_.div_le_div_of_nonneg_left (by positivity)
      (_root_.div_pos hD (by norm_num)) hlog
  have herr := Real.squareSieveCutoff_sq_bound hn1
  have he : 2*(n : Real)/(Real.squareSieveDenominator n/2) =
      4*(n : Real)/Real.squareSieveDenominator n := by ring
  rw [he] at hmain
  exact hs.trans (_root_.add_le_add hmain herr)

end Nat.PrimeSieve
