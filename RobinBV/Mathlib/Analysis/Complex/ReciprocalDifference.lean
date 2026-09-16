/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.ReciprocalShift

/-!
# Exact reciprocal-phase increments

Positive finite reciprocal packets give monotonicity and explicit endpoint bounds.
These finite estimates do not assume a prime-distribution theorem.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Real

noncomputable def reciprocalPhaseDifference (Y t : Real) (h : Nat) : Real :=
  Y/(t+h)-Y/t

theorem reciprocalPhaseDifference_increment (Y t : Real) (ht : 0 < t) (h : Nat) :
    reciprocalPhaseDifference Y (t+1) h - reciprocalPhaseDifference Y t h =
      (Finset.range h).sum (fun j => 2*Y/((t+j)*(t+j+1)*(t+j+2))) := by
  induction h with
  | zero => simp [reciprocalPhaseDifference]
  | succ h ih =>
    rw [Finset.sum_range_succ, <- ih]
    dsimp [reciprocalPhaseDifference]
    have hh : 0 < t+(h : Real) := by positivity
    have hh1 : 0 < t+(h : Real)+1 := by positivity
    have hh2 : 0 < t+(h : Real)+2 := by positivity
    have ht1 : 0 < t+1 := by positivity
    push_cast
    field_simp
    ring

theorem reciprocalPhaseDifference_increment_antitone (Y : Real) (hY : 0 <= Y)
    (h : Nat) {t u : Real} (ht : 0 < t) (htu : t <= u) :
    reciprocalPhaseDifference Y (u+1) h-reciprocalPhaseDifference Y u h <=
      reciprocalPhaseDifference Y (t+1) h-reciprocalPhaseDifference Y t h := by
  rw [reciprocalPhaseDifference_increment Y t ht,
    reciprocalPhaseDifference_increment Y u (lt_of_lt_of_le ht htu)]
  apply Finset.sum_le_sum
  intro j _hj
  have htj : 0 < t+(j : Real) := by positivity
  have huj : 0 < u+(j : Real) := lt_of_lt_of_le htj (by linarith)
  have hd : (t+j)*(t+j+1)*(t+j+2) <= (u+j)*(u+j+1)*(u+j+2) := by
    apply mul_le_mul
    next => exact mul_le_mul (by linarith) (by linarith) (by positivity) huj.le
    next => linarith
    next => positivity
    next => positivity
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hd

theorem reciprocalPhaseDifference_increment_bounds (Y : Real) (hY : 0 <= Y)
    (h : Nat) {P t Q : Real} (hP : 0 < P) (hPt : P <= t)
    (hQ : t+(h : Real)+1 <= Q) :
    And (2*Y*h/Q^3 <= reciprocalPhaseDifference Y (t+1) h-reciprocalPhaseDifference Y t h)
      (reciprocalPhaseDifference Y (t+1) h-reciprocalPhaseDifference Y t h <=
        2*Y*h/P^3) := by
  have ht : 0 < t := lt_of_lt_of_le hP hPt
  have hQpos : 0 < Q := by have hh : 0 <= (h : Real) := Nat.cast_nonneg h; linarith
  rw [reciprocalPhaseDifference_increment Y t ht]
  have lower (j : Nat) (hj : j < h) :
      2*Y/Q^3 <= 2*Y/((t+j)*(t+j+1)*(t+j+2)) := by
    have hjR : (j : Real)+1 <= h := by exact_mod_cast (show j+1 <= h by omega)
    have htop : t+(j : Real)+2 <= Q := by linarith
    have hd : (t+j)*(t+j+1)*(t+j+2) <= Q^3 := by
      calc
        _ <= Q*Q*Q := mul_le_mul
          (mul_le_mul (by linarith) (by linarith) (by positivity) hQpos.le)
          htop (by positivity) (by positivity)
        _ = Q^3 := by ring
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hd
  have upper (j : Nat) : 2*Y/((t+j)*(t+j+1)*(t+j+2)) <= 2*Y/P^3 := by
    have hjR : 0 <= (j : Real) := Nat.cast_nonneg j
    have hd : P^3 <= (t+j)*(t+j+1)*(t+j+2) := by
      calc
        _ = P*P*P := by ring
        _ <= _ := mul_le_mul
          (mul_le_mul (by linarith) (by linarith) hP.le (by positivity))
          (by linarith) hP.le (by positivity)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hd
  constructor
  next =>
    have hh := Finset.sum_le_sum (s := Finset.range h)
      (fun j hj => lower j (Finset.mem_range.mp hj))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
    have he : (h : Real)*(2*Y/Q^3) = 2*Y*h/Q^3 := by ring
    rw [he] at hh
    exact hh
  next =>
    have hh := Finset.sum_le_sum (s := Finset.range h) (fun j _ => upper j)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
    have he : (h : Real)*(2*Y/P^3) = 2*Y*h/P^3 := by ring
    rw [he] at hh
    exact hh

end Real
