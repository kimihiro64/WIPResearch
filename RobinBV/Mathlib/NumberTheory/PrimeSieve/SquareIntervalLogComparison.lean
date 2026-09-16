/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalLogAllowance

/-!
# SquareIntervalLogComparison

Explicit finite interval estimates used in signed prime-candidate accounting.
All constants and endpoint conditions are retained; no prime-existence result
is claimed by a negative lower envelope.
-/

set_option autoImplicit false
namespace Real

theorem log_le_quarter_of_sixteen_le {x : Real} (hx : 16 <= x) :
    Real.log x <= x/4 := by
  have hx0 : 0 < x := by linarith
  have hh := Real.log_le_sub_one_of_pos
    (_root_.div_pos hx0 (by norm_num : (0 : Real) < 8))
  rw [Real.log_div (ne_of_gt hx0) (by norm_num : Not ((8 : Real) = 0))] at hh
  have htwo := Real.log_lt_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    (by norm_num : Not ((2 : Real) = 1))
  have he : Real.log (8 : Real) = 3*Real.log 2 := by
    have h8 : (8 : Real) = 2^3 := by norm_num
    rw [h8, Real.log_pow]
    norm_num
  rw [he] at hh
  linarith

theorem half_log_le_squareSieveDenominator {x : Real} (hx : 16 <= Real.log x) :
    Real.log x/2 <= squareSieveDenominator x := by
  have h := log_le_quarter_of_sixteen_le hx
  unfold squareSieveDenominator
  linarith

end Real

namespace Nat.PrimeSieve

theorem roughLogAllowance_pos {n : Nat} (hn : 4 <= n) : 0 < roughLogAllowance n := by
  have hn4 : (4 : Real) <= n := by exact_mod_cast hn
  have hn1 : (1 : Real) < n := by linarith
  have hD := Real.squareSieveDenominator_pos hn1
  have ht := Real.log_pos hn1
  unfold roughLogAllowance
  positivity

theorem roughLogAllowance_le_linear_of_log_ge_sixteen {n : Nat}
    (hn : 16 <= Real.log (n : Real)) : roughLogAllowance n <= (129/128 : Real)*n := by
  have hD := Real.half_log_le_squareSieveDenominator hn
  have hD8 : (8 : Real) <= Real.squareSieveDenominator n := by linarith
  have ht2 : (256 : Real) <= (Real.log (n : Real))^2 := by nlinarith
  have hmain := _root_.div_le_div_of_nonneg_left
    (by positivity : (0 : Real) <= 8*n) (by norm_num : (0 : Real) < 8) hD8
  have herr := _root_.div_le_div_of_nonneg_left
    (by positivity : (0 : Real) <= 2*n) (by norm_num : (0 : Real) < 256) ht2
  have he : 8*(n : Real)/8+2*(n : Real)/256 = (129/128 : Real)*n := by ring
  unfold roughLogAllowance
  rw [<- he]
  exact _root_.add_le_add hmain herr

theorem log_lower_envelope_strictly_improves_reference {n : Nat}
    (hn : 16 <= Real.log (n : Real)) :
    -((1618*(n : Real)+7654)/1001) < -roughLogAllowance n := by
  have h := roughLogAllowance_le_linear_of_log_ge_sixteen hn
  have hn0 : (0 : Real) <= n := Nat.cast_nonneg n
  linarith only [h, hn0]

theorem promised_log_envelope_strictly_improves_reference {n : Nat}
    (hn : 169 <= n) (ht : 16 <= Real.log (n : Real)) :
    -((1618*(n : Real)+7654)/1001) <
      -roughLogAllowance n-(36683/1001 : Real) := by
  have h := roughLogAllowance_le_linear_of_log_ge_sixteen ht
  have hn169 : (169 : Real) <= n := by exact_mod_cast hn
  linarith only [h, hn169]

/-- Exact baseline gain; no n is instantiated or experimentally evaluated. -/
theorem log_lower_envelope_gain (n : Nat) :
    -roughLogAllowance n-(-((1618*(n : Real)+7654)/1001)) =
      (1618/1001 : Real)*n+(7654/1001 : Real)-
        8*(n : Real)/(Real.log n-2*Real.log (Real.log n))-
        2*(n : Real)/(Real.log n)^2 := by
  unfold roughLogAllowance Real.squareSieveDenominator
  ring

theorem log_lower_envelope_negative {n : Nat} (hn : 4 <= n) :
    -roughLogAllowance n < 0 := neg_neg_of_pos (roughLogAllowance_pos hn)

end Nat.PrimeSieve
