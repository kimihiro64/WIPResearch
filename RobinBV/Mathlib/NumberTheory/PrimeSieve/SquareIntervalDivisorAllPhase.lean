/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.ReciprocalAllPhase
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalDivisorRows

/-!
# Balanced divisor rows in both modulus orderings

The same exact square-interval row count now has an explicit error for all
positive divisor moduli. The old stronger estimate is retained when the
second modulus does not exceed the first.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

set_option maxHeartbeats 400000 in
theorem balancedDivisorRows_abs_error_all_moduli {n a b t : Nat}
    (hn : 2<=n) (ha : 0<a) (hb : 0<b) (ht : 2<=t)
    (hnscale : 2*a*t^15<=n) (hbudget : 64*a^2*t^14<=n) :
    abs (((balancedDivisorRows n a b).card:Real) -
      (2*(n:Real)/((a:Real)*b))*Real.log 2) <=
      40*(n:Real)/((a:Real)*t)+4/(b:Real)+20*((t:Real)^2-1)*(b:Real)/a := by
  let P : Nat := n/(2*a)+1
  let N : Nat := n/a-n/(2*a)
  let Xa : Real := ((n*n:Nat):Real)/((a:Real)*b)
  let Xb : Real := ((n*n+2*n:Nat):Real)/((a:Real)*b)
  let C : Real := (balancedDivisorRows n a b).card
  let S : Real := (Finset.range N).sum (fun i => 1/((P:Real)+i))
  have hn0 : (0:Real)<n := by exact_mod_cast (show 0<n by omega)
  have haR : (0:Real)<a := by exact_mod_cast ha
  have hbR : (0:Real)<b := by exact_mod_cast hb
  have ht0 : 0<t := by omega
  have htR : (0:Real)<t := by exact_mod_cast ht0
  have htr : (2:Real)<=t := by exact_mod_cast ht
  have hP : 1<=P := Nat.succ_le_succ (Nat.zero_le _)
  have hpR : (0:Real)<P := by exact_mod_cast (show 0<P by omega)
  have han : Not ((a:Real)=0) := ne_of_gt haR
  have hbn : Not ((b:Real)=0) := ne_of_gt hbR
  have htn : Not ((t:Real)=0) := ne_of_gt htR
  have hpn : Not ((P:Real)=0) := ne_of_gt hpR
  have hnn : Not ((n:Real)=0) := ne_of_gt hn0
  have hshape := half_divisor_row_shape n a
  have hphase := half_divisor_phase_conditions (b:=1) hn ha (by decide)
    (by omega) ht hnscale (by simpa only [Nat.mul_one] using hbudget)
  have hXaEq : Xa=(n:Real)^2/((a:Real)*b) := by dsimp [Xa]; push_cast; ring
  have hXbEq : Xb=((n:Real)^2+2*n)/((a:Real)*b) := by dsimp [Xb]; push_cast; ring
  have hdelta : Xb-Xa=2*(n:Real)/((a:Real)*b) := by dsimp [Xa, Xb]; push_cast; ring
  have hXa : 0<Xa := by rw [hXaEq]; positivity
  have hdelta0 : 0<=Xb-Xa := by rw [hdelta]; positivity
  have hXab : Xa<=Xb := by linarith only [hdelta0]
  have hb1 : (1:Real)<=b := by exact_mod_cast (show 1<=b by omega)
  have hden : (a:Real)<=(a:Real)*b := by nlinarith
  have hxb : ((n:Real)^2+2*n)/((a:Real)*b)<=((n:Real)^2+2*n)/(a:Real) :=
    div_le_div_of_nonneg_left (by positivity) haR hden
  have hs : 4*Xb*(t:Real)^14<=(P:Real)^3 := by
    rw [hXbEq]
    calc
      _ <= 4*(((n:Real)^2+2*n)/(a:Real))*(t:Real)^14 :=
        _root_.mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxb (by norm_num)) (by positivity)
      _ <= _ := by simpa only [Nat.cast_one, mul_one] using hphase.2.2
  have hf := Complex.reciprocal_floor_interval_error_power_all_phase_simple ht
    (show (N:Real)<=P by exact_mod_cast hshape.1) hphase.1 hXa hXab hs
  have hcard := divisorProductRows_card_floor (A:=n*n) (B:=n*n+2*n)
    (a:=a) (b:=b) (P:=P) (N:=N) (by omega) ha hb
  change C=(Finset.range N).sum (fun i =>
    (Int.floor (Xb/((P:Real)+i)):Real)-(Int.floor (Xa/((P:Real)+i)):Real)) at hcard
  rw [<- hcard] at hf
  change abs (C-(Xb-Xa)*S)<=40*(P:Real)/t+20*((t:Real)^2-1)*(P:Real)^2/Xa at hf
  have hh := Real.dyadic_harmonic_abs_error hP hshape.1 hshape.2
  change abs (S-Real.log 2)<=1/(P:Real) at hh
  have hharm : abs ((Xb-Xa)*S-(Xb-Xa)*Real.log 2)<=(Xb-Xa)/(P:Real) := by
    rw [<- mul_sub, abs_mul, abs_of_nonneg hdelta0]
    calc
      _ <= (Xb-Xa)*(1/(P:Real)) := mul_le_mul_of_nonneg_left hh hdelta0
      _ = _ := by ring
  have hlog : abs (C-(Xb-Xa)*Real.log 2) <=
      (40*(P:Real)/t+20*((t:Real)^2-1)*(P:Real)^2/Xa)+(Xb-Xa)/(P:Real) := by
    calc
      _ = abs ((C-(Xb-Xa)*S)+((Xb-Xa)*S-(Xb-Xa)*Real.log 2)) := by congr 1; ring
      _ <= _ := (abs_add_le _ _).trans (_root_.add_le_add hf hharm)
  have ht15 := pow_pos ht0 15
  have hna : 2*a<=n := by nlinarith
  have hr := half_divisor_row_real_bounds ha hna
  have hmain : 40*(P:Real)/t<=40*(n:Real)/((a:Real)*t) := by
    calc
      _ = (40*((P:Real)*a))/((a:Real)*t) := by field_simp <;> ring
      _ <= _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr.2 (by norm_num)) (by positivity)
  have herr : (Xb-Xa)/(P:Real)<=4/(b:Real) := by
    rw [hdelta]
    calc
      _ = (2*(n:Real))/((a:Real)*b*P) := by rw [div_div]
      _ <= (4*(a:Real)*P)/((a:Real)*b*P) :=
        div_le_div_of_nonneg_right (by nlinarith [hr.1]) (by positivity)
      _ = _ := by field_simp <;> ring
  have hsq0 := _root_.mul_le_mul hr.2 hr.2 (by positivity) (by positivity)
  have hsq : (P:Real)^2*(a:Real)^2<=(n:Real)^2 := by nlinarith
  have hxratio : (P:Real)^2/Xa<=(b:Real)/a := by
    rw [hXaEq]
    calc
      _ = ((P:Real)^2*(a:Real)^2*b)/((a:Real)*(n:Real)^2) := by field_simp <;> ring
      _ <= ((n:Real)^2*b)/((a:Real)*(n:Real)^2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hbR.le) (by positivity)
      _ = _ := by field_simp <;> ring
  have hcoef : 0<=20*((t:Real)^2-1) := by nlinarith
  have hexcess : 20*((t:Real)^2-1)*(P:Real)^2/Xa <=
      20*((t:Real)^2-1)*(b:Real)/a := by
    calc
      _ = (20*((t:Real)^2-1))*((P:Real)^2/Xa) := by ring
      _ <= (20*((t:Real)^2-1))*((b:Real)/a) :=
        mul_le_mul_of_nonneg_left hxratio hcoef
      _ = _ := by ring
  change abs (C-(2*(n:Real)/((a:Real)*b))*Real.log 2) <= _
  rw [<- hdelta]
  calc
    _ <= (40*(P:Real)/t+20*((t:Real)^2-1)*(P:Real)^2/Xa)+(Xb-Xa)/(P:Real) := hlog
    _ <= (40*(n:Real)/((a:Real)*t)+20*((t:Real)^2-1)*(b:Real)/a)+4/(b:Real) :=
      _root_.add_le_add (_root_.add_le_add hmain hexcess) herr
    _ = _ := by ring

theorem balancedDivisorRows_abs_error_best_moduli {n a b t : Nat}
    (hn : 2<=n) (ha : 0<a) (hb : 0<b) (ht : 2<=t)
    (hnscale : 2*a*t^15<=n) (hbudget : 64*a^2*t^14<=n) :
    abs (((balancedDivisorRows n a b).card:Real) -
      (2*(n:Real)/((a:Real)*b))*Real.log 2) <=
      40*(n:Real)/((a:Real)*t)+4/(b:Real)+
        if a<b then 20*((t:Real)^2-1)*(b:Real)/a else 0 := by
  by_cases hab : a<b
  next =>
    simpa only [if_pos hab] using balancedDivisorRows_abs_error_all_moduli hn ha hb ht hnscale hbudget
  next =>
    have hba : b<=a := by omega
    have hnb : n<=n*b := by nlinarith
    have h := balancedDivisorRows_abs_error hn ha hb hba ht hnscale (hbudget.trans hnb)
    simpa only [if_neg hab, add_zero] using h

end Nat.PrimeSieve
