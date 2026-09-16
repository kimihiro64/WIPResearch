/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import RobinBV.Mathlib.Analysis.Complex.ReciprocalSum

/-!
# A concrete reciprocal-sum parameter bound

The finite correlation cap, complete Gram energy and exact shift endpoints
give an explicit bound with rational constants. Every parameter is quantified
and all scale conditions are visible. This is a phase estimate, not a bound
on the number of primes or composites in a square interval.
-/

set_option autoImplicit false
open scoped Classical
namespace Complex

/-- The explicit Gram cap simplifies in a quantified square-scale regime. -/
theorem reciprocal_shift_correlation_coarse {Y P : Real} {N m : Nat}
    (hP : 0 < P) (hm : 1 <= m) (hN : (N : Real) <= P)
    (hmP : (m : Real)^2 <= P) (hY : P^2 <= Y) :
    (m : Real)*(3*Real.pi*(P+N+(m : Real)*m)^3/(2*Y*m)) <= 162*P := by
  have hmR : 0 < (m : Real) := by exact_mod_cast (by omega : 0 < m)
  have hYP : 0 < Y := lt_of_lt_of_le (sq_pos_of_pos hP) hY
  have htop : P+(N : Real)+(m : Real)*m <= 3*P := by nlinarith only [hN, hmP]
  have hpi : Real.pi <= 4 := Real.pi_le_four
  have hnum : 3*Real.pi*(P+N+(m : Real)*m)^3 <= 324*P^3 := by
    calc
      _ <= 3*4*(3*P)^3 := by gcongr
      _ = _ := by ring
  have hden : 2*P^2*(m : Real) <= 2*Y*m := by gcongr
  have hC : 3*Real.pi*(P+N+(m : Real)*m)^3/(2*Y*m) <= 162*P/(m : Real) := by
    calc
      _ <= 324*P^3/(2*Y*m) := _root_.div_le_div_of_nonneg_right hnum (by positivity)
      _ <= 324*P^3/(2*P^2*m) :=
        _root_.div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by field_simp; ring
  have h := _root_.mul_le_mul_of_nonneg_left hC hmR.le
  have he : (m : Real)*(162*P/m) = 162*P := by field_simp
  rwa [he] at h

/-- A nonnegative Gram cap gives the complete polynomial energy allowance. -/
theorem finite_shift_energy_coarse {P C : Real} {N m : Nat}
    (hm : 1 <= m) (hN : (N : Real) <= P) (hC : 0 <= C)
    (hMC : (m : Real)*C <= 162*P) :
    (N : Real)*((m : Real)*N+((m : Real)^2-m)*C) <= 163*P^2*(m : Real) := by
  have hm1 : (1 : Real) <= m := by exact_mod_cast hm
  have hP : 0 <= P := (Nat.cast_nonneg N).trans hN
  calc
    _ = (N : Real)*((m : Real)*N+((m : Real)-1)*((m : Real)*C)) := by ring
    _ <= P*((m : Real)*P+((m : Real)-1)*(162*P)) := by gcongr
    _ <= _ := by nlinarith [sq_nonneg P]

/-- A rational constant bounds the square root of the full energy allowance. -/
theorem sqrt_shift_energy_coarse {E P : Real} {m : Nat}
    (hE0 : 0 <= E) (hP : 0 <= P) (hE : E <= 163*P^2*(m : Real)) :
    Real.sqrt E <= 13*P*Real.sqrt (m : Real) := by
  have hsq : (13*P*Real.sqrt (m : Real))^2 = 169*P^2*(m : Real) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    norm_num
  have hpos : 0 <= 13*P*Real.sqrt (m : Real) := by positivity
  have hbig : 163*P^2*(m : Real) <= 169*P^2*m := by gcongr; norm_num
  nlinarith only [hE, hbig, hsq, hpos, Real.sq_sqrt hE0, Real.sqrt_nonneg E]

/-- Exact normalization by the positive square root of a natural parameter. -/
theorem nat_mul_div_sqrt_cancel (P : Real) {m : Nat} (hm : 1 <= m) :
    (m : Real)*(13*P/Real.sqrt (m : Real)) = 13*P*Real.sqrt (m : Real) := by
  have hmR : 0 < (m : Real) := by exact_mod_cast (by omega : 0 < m)
  have hr : 0 < Real.sqrt (m : Real) := Real.sqrt_pos.mpr hmR
  calc
    _ = (Real.sqrt (m : Real))^2*(13*P/Real.sqrt (m : Real)) := by
      rw [Real.sq_sqrt hmR.le]
    _ = 13*P*(Real.sqrt (m : Real)*
        (Real.sqrt (m : Real)/Real.sqrt (m : Real))) := by ring
    _ = _ := by simp [ne_of_gt hr]

/-- Explicit power-saving parameter regime with every budget discharged. -/
theorem norm_reciprocal_sum_le_explicit_shift {Y P : Real} {N m : Nat}
    (hP : 0 < P) (hm : 1 <= m) (hN : (N : Real) <= P)
    (hmP : (m : Real)^2 <= P) (hY : P^2 <= Y)
    (hsmall : 2*Y*((m*m : Nat) : Real) <= Real.pi*P^3) :
    norm ((Finset.range N).sum (fun j =>
      exp (I*((Y/(P+j) : Real) : Complex)))) <=
        13*P/Real.sqrt (m : Real)+(m : Real)^2 := by
  have hmR : 0 < (m : Real) := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : Real) <= m := by exact_mod_cast hm
  have hYP : 0 < Y := lt_of_lt_of_le (sq_pos_of_pos hP) hY
  let C := 3*Real.pi*(P+N+(m : Real)*m)^3/(2*Y*m)
  let E := (N : Real)*((m : Real)*N+((m : Real)^2-m)*C)
  have hm2 : 0 <= (m : Real)^2-m := by nlinarith only [hm1]
  have hC0 : 0 <= C := by dsimp only [C]; positivity
  have hE0 : 0 <= E := by
    dsimp only [E]
    exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (by positivity) (mul_nonneg hm2 hC0))
  have hMC : (m : Real)*C <= 162*P :=
    reciprocal_shift_correlation_coarse hP hm hN hmP hY
  have hE : E <= 163*P^2*(m : Real) := finite_shift_energy_coarse hm hN hC0 hMC
  have hsqrt := sqrt_shift_energy_coarse hE0 hP.le hE
  have hb := norm_reciprocal_sum_mul_shift_le (N := N) (H := m) (D := m) hYP hP
    (by omega : 0 < m) hsmall
  change (m : Real)*norm ((Finset.range N).sum (fun j =>
    exp (I*((Y/(P+j) : Real) : Complex)))) <= Real.sqrt E+(m : Real)*m*(m-1) at hb
  have hid := nat_mul_div_sqrt_cancel P hm
  have hmul : (m : Real)*norm ((Finset.range N).sum (fun j =>
      exp (I*((Y/(P+j) : Real) : Complex)))) <=
        (m : Real)*(13*P/Real.sqrt (m : Real)+(m : Real)^2) := by
    rw [mul_add, hid]
    nlinarith only [hb, hsqrt, sq_nonneg (m : Real)]
  nlinarith only [hmR, hmul]

end Complex
