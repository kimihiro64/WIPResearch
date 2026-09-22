/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
/-
# Half-divisor phase estimates

This module supplies the half-divisor phase inequalities used in the owner
packet and square-interval sieve calculations.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal-phase parameters for half-interval divisor rows

Exact integer row endpoints and polynomial size conditions imply the
reciprocal-phase domain used by square-interval factor-pair counts.
No prime-distribution assumption or positivity claim is introduced.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

theorem half_divisor_row_shape (n a : Nat) :
    n/a-n/(2*a)<=n/(2*a)+1 /\
    n/(2*a)+1<=n/a-n/(2*a)+1 := by
  have he : (n/a)/2=n/(2*a) := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    ring
  have hlow := Nat.div_mul_le_self (n/a) 2
  have hupp := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mp
    (Nat.lt_succ_self ((n/a)/2))
  have hsub := Nat.div_le_self (n/a) 2
  rw [he] at hlow hupp hsub
  omega

theorem half_divisor_row_real_bounds {n a : Nat} (ha : 0<a) (hn : 2*a<=n) :
    (n:Real) < (n/(2*a)+1:Nat)*(2*(a:Real)) /\
      ((n/(2*a)+1:Nat):Real)*a <= n := by
  have h2a : 0<2*a := by omega
  have hlo : n<(n/(2*a)+1)*(2*a) :=
    (Nat.div_lt_iff_lt_mul h2a).mp (by omega)
  have hdiv : 1<=n/(2*a) := Nat.div_pos hn h2a
  have hmul : n/(2*a)*(2*a)<=n := Nat.div_mul_le_self n (2*a)
  have hhi : (n/(2*a)+1)*a<=n := by nlinarith
  exact And.intro (by exact_mod_cast hlo) (by exact_mod_cast hhi)

theorem half_divisor_phase_conditions {n a b t : Nat}
    (hn : 2<=n) (ha : 0<a) (hb : 0<b) (hba : b<=a) (ht : 2<=t)
    (hnscale : 2*a*t^15<=n) (hbudget : 64*a^2*t^14<=n*b) :
    (t:Real)^15 <= (n/(2*a)+1:Nat) /\
    ((n/(2*a)+1:Nat):Real)^2 <=
      2*Real.pi*((n:Real)^2/((a:Real)*b)) /\
    4*(((n:Real)^2+2*n)/((a:Real)*b))*(t:Real)^14 <=
      ((n/(2*a)+1:Nat):Real)^3 := by
  have htpos : 0<t := by omega
  have ht15 := pow_pos htpos 15
  have hna : 2*a<=n := by nlinarith
  have hr := half_divisor_row_real_bounds ha hna
  let P : Real := (n/(2*a)+1:Nat)
  have hpl : (n:Real)<P*(2*a) := hr.1
  have hpu : P*a<=n := hr.2
  have hp : 0<P := by dsimp [P]; positivity
  have haR : (0:Real)<a := by exact_mod_cast ha
  have hbR : (0:Real)<b := by exact_mod_cast hb
  have hd : (0:Real)<(a:Real)*b := mul_pos haR hbR
  have hdn : Not ((a:Real)*b=0) := ne_of_gt hd
  have hnR : (2:Real)<=n := by exact_mod_cast hn
  have hbaR : (b:Real)<=a := by exact_mod_cast hba
  have hscR : 2*(a:Real)*(t:Real)^15<=n := by exact_mod_cast hnscale
  have hscale : (t:Real)^15<=P := by nlinarith
  have hsq := _root_.mul_le_mul hpu hpu (by positivity) (by positivity)
  have hsq2 := mul_le_mul_of_nonneg_left hbaR
    (show 0<=P^2*(a:Real) by positivity)
  have hsq3 : P^2*((a:Real)*b)<=(n:Real)^2 := by nlinarith
  have hlow : P^2<=2*Real.pi*((n:Real)^2/((a:Real)*b)) := by
    calc
      P^2 = (P^2*((a:Real)*b))/((a:Real)*b) := by field_simp
      _ <= (n:Real)^2/((a:Real)*b) :=
        div_le_div_of_nonneg_right hsq3 hd.le
      _ <= 2*Real.pi*((n:Real)^2/((a:Real)*b)) := by
        have hpi : (1:Real)<=2*Real.pi := by linarith [Real.two_le_pi]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi
          (div_nonneg (sq_nonneg (n:Real)) hd.le)
  have hBR : (n:Real)^2+2*n<=2*(n:Real)^2 := by nlinarith
  have hcub : (n:Real)^3 <= (P*(2*a))^3 := by
    gcongr
  have hbRng : 64*(a:Real)^2*(t:Real)^14 <= (n:Real)*b := by
    exact_mod_cast hbudget
  have hbs := mul_le_mul_of_nonneg_right hbRng (sq_nonneg (n:Real))
  have hcs := mul_le_mul_of_nonneg_right hcub hbR.le
  have hcomp : (8*(a:Real)^2)*(8*(n:Real)^2*(t:Real)^14) <=
      (8*(a:Real)^2)*(P^3*((a:Real)*b)) := by nlinarith
  have hpoly : 8*(n:Real)^2*(t:Real)^14<=P^3*((a:Real)*b) := by
    by_contra h
    have hpos := mul_pos (show (0:Real)<8*(a:Real)^2 by positivity)
      (show 0<8*(n:Real)^2*(t:Real)^14-P^3*((a:Real)*b) by linarith)
    nlinarith
  have hbmul := mul_le_mul_of_nonneg_right hBR
    (show 0<=4*(t:Real)^14 by positivity)
  have hpoly2 : 4*((n:Real)^2+2*n)*(t:Real)^14<=P^3*((a:Real)*b) := by
    nlinarith
  have hfreq : 4*(((n:Real)^2+2*n)/((a:Real)*b))*(t:Real)^14<=P^3 := by
    calc
      _ = (4*((n:Real)^2+2*n)*(t:Real)^14)/((a:Real)*b) := by ring
      _ <= (P^3*((a:Real)*b))/((a:Real)*b) :=
        div_le_div_of_nonneg_right hpoly2 hd.le
      _ = P^3 := by field_simp
  exact And.intro hscale (And.intro hlow hfreq)

end Nat.PrimeSieve
