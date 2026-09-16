/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalDivisorAllPhase

/-!
# Divisor rows for skew square-interval factor bands

The row endpoint M varies independently of the fixed quadratic interval.
Exact pair membership and the complete all-moduli discrepancy retain every
M-dependent error and every polynomial phase condition.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

def skewDivisorRows (n M a b : Nat) : Finset (Prod Nat Nat) :=
  divisorProductRows (n*n) (n*n+2*n) a b
    (M/(2*a)+1) (M/a-M/(2*a))

theorem skew_divisor_phase_conditions {n M a t : Nat}
    (hn : 2 <= n) (ha : 0 < a) (ht : 2 <= t)
    (hscale : 2*a*t^15 <= M)
    (hbudget : 64*a^2*n^2*t^14 <= M^3) :
    (t:Real)^15 <= (M/(2*a)+1:Nat) /\
      4*(((n:Real)^2+2*n)/(a:Real))*(t:Real)^14 <=
        ((M/(2*a)+1:Nat):Real)^3 := by
  have ht0 : 0 < t := by omega
  have ht15 := pow_pos ht0 15
  have hMa : 2*a <= M := by nlinarith
  have hr := half_divisor_row_real_bounds ha hMa
  let P : Real := (M/(2*a)+1:Nat)
  have hpl : (M:Real) < P*(2*a) := hr.1
  have hp : 0 < P := by dsimp [P]; positivity
  have haR : (0:Real) < a := by exact_mod_cast ha
  have han : Not ((a:Real)=0) := ne_of_gt haR
  have hnR : (2:Real) <= n := by exact_mod_cast hn
  have hsc : 2*(a:Real)*(t:Real)^15 <= M := by exact_mod_cast hscale
  have hscP : (t:Real)^15 <= P := by nlinarith
  have hcub : (M:Real)^3 <= (P*(2*a))^3 := by gcongr
  have hBR : (n:Real)^2+2*n <= 2*(n:Real)^2 := by nlinarith
  have hbR : 64*(a:Real)^2*(n:Real)^2*(t:Real)^14 <= (M:Real)^3 := by
    exact_mod_cast hbudget
  have hcomp : (8*(a:Real)^2)*(8*(n:Real)^2*(t:Real)^14) <=
      (8*(a:Real)^2)*(P^3*(a:Real)) := by nlinarith only [hbR, hcub]
  have hpoly : 8*(n:Real)^2*(t:Real)^14 <= P^3*(a:Real) := by
    by_contra h
    have hpos := mul_pos (show (0:Real) < 8*(a:Real)^2 by positivity)
      (show 0 < 8*(n:Real)^2*(t:Real)^14-P^3*(a:Real) by linarith)
    nlinarith only [hpos, hcomp]
  have hmul := mul_le_mul_of_nonneg_right hBR
    (show 0 <= 4*(t:Real)^14 by positivity)
  have hpoly2 : 4*((n:Real)^2+2*n)*(t:Real)^14 <= P^3*(a:Real) := by
    nlinarith only [hmul, hpoly]
  have hfreq : 4*(((n:Real)^2+2*n)/(a:Real))*(t:Real)^14 <= P^3 := by
    calc
      _ = (4*((n:Real)^2+2*n)*(t:Real)^14)/(a:Real) := by ring
      _ <= (P^3*(a:Real))/(a:Real) :=
        div_le_div_of_nonneg_right hpoly2 haR.le
      _ = _ := by field_simp
  exact And.intro hscP hfreq

theorem mem_skewDivisorRows_iff {n M a b p q : Nat}
    (ha : 0<a) (hb : 0<b) :
    Membership.mem (skewDivisorRows n M a b) (Prod.mk p q) <->
      Dvd.dvd a p /\ Dvd.dvd b q /\ M<2*p /\ p<=M /\ n*n<p*q /\ p*q<=n*n+2*n := by
  have h2a : 0<2*a := by omega
  have he : (M/a)/2=M/(2*a) := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    ring
  have hsub : M/(2*a)<=M/a := by
    rw [<- he]
    exact Nat.div_le_self (M/a) 2
  unfold skewDivisorRows
  rw [mem_divisorProductRows_iff ha hb (Nat.zero_lt_succ (M/(2*a)))]
  constructor
  next =>
    intro h
    choose i hi using h
    choose v hv using hi.2
    have hrowlo : M/(2*a)<M/(2*a)+1+i := by omega
    have hrowhi : M/(2*a)+1+i<=M/a := by omega
    have hlo := (Nat.div_lt_iff_lt_mul h2a).mp hrowlo
    have hhi := (Nat.le_div_iff_mul_le ha).mp hrowhi
    have hpn : M<2*p := by nlinarith [hv.1]
    have hnp : p<=M := by nlinarith [hv.1]
    exact And.intro (Exists.intro (M/(2*a)+1+i) hv.1)
      (And.intro (Exists.intro v hv.2.1)
        (And.intro hpn (And.intro hnp hv.2.2)))
  next =>
    intro h
    choose u hu using h.1
    choose v hv using h.2.1
    have hrowlo : M/(2*a)<u := by
      apply (Nat.div_lt_iff_lt_mul h2a).mpr
      nlinarith [h.2.2.1]
    have hrowhi : u<=M/a := by
      apply (Nat.le_div_iff_mul_le ha).mpr
      nlinarith [h.2.2.2.1]
    let i := u-(M/(2*a)+1)
    have hi : i<M/a-M/(2*a) := by dsimp [i]; omega
    have heq : M/(2*a)+1+i=u := by dsimp [i]; omega
    exact Exists.intro i (And.intro hi (Exists.intro v
      (And.intro (by simpa only [heq] using hu)
        (And.intro hv h.2.2.2.2))))

set_option maxHeartbeats 400000 in
theorem skewDivisorRows_abs_error {n M a b t : Nat}
    (hn : 2<=n) (ha : 0<a) (hb : 0<b) (ht : 2<=t)
    (hnscale : 2*a*t^15<=M) (hbudget : 64*a^2*n^2*t^14<=M^3) :
    abs (((skewDivisorRows n M a b).card:Real) -
      (2*(n:Real)/((a:Real)*b))*Real.log 2) <=
      40*(M:Real)/((a:Real)*t)+4*(n:Real)/((b:Real)*M)+
        20*((t:Real)^2-1)*(M:Real)^2*b/((a:Real)*(n:Real)^2) := by
  let P : Nat := M/(2*a)+1
  let N : Nat := M/a-M/(2*a)
  let Xa : Real := ((n*n:Nat):Real)/((a:Real)*b)
  let Xb : Real := ((n*n+2*n:Nat):Real)/((a:Real)*b)
  let C : Real := (skewDivisorRows n M a b).card
  let S : Real := (Finset.range N).sum (fun i => 1/((P:Real)+i))
  have hn0 : (0:Real)<n := by exact_mod_cast (show 0<n by omega)
  have haR : (0:Real)<a := by exact_mod_cast ha
  have hbR : (0:Real)<b := by exact_mod_cast hb
  have ht0 : 0<t := by omega
  have htR : (0:Real)<t := by exact_mod_cast ht0
  have htr : (2:Real)<=t := by exact_mod_cast ht
  have ht15 := pow_pos ht0 15
  have hMa : 2*a<=M := by nlinarith
  have hM0 : (0:Real)<M := by exact_mod_cast (show 0<M by omega)
  have hP : 1<=P := Nat.succ_le_succ (Nat.zero_le _)
  have hpR : (0:Real)<P := by exact_mod_cast (show 0<P by omega)
  have han : Not ((a:Real)=0) := ne_of_gt haR
  have hbn : Not ((b:Real)=0) := ne_of_gt hbR
  have htn : Not ((t:Real)=0) := ne_of_gt htR
  have hpn : Not ((P:Real)=0) := ne_of_gt hpR
  have hnn : Not ((n:Real)=0) := ne_of_gt hn0
  have hMn : Not ((M:Real)=0) := ne_of_gt hM0
  have hshape := half_divisor_row_shape M a
  have hphase := skew_divisor_phase_conditions hn ha ht hnscale hbudget
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
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxb (by norm_num)) (by positivity)
      _ <= _ := hphase.2
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
  have hr := half_divisor_row_real_bounds ha hMa
  have hmain : 40*(P:Real)/t<=40*(M:Real)/((a:Real)*t) := by
    calc
      _ = (40*((P:Real)*a))/((a:Real)*t) := by field_simp <;> ring
      _ <= _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr.2 (by norm_num)) (by positivity)
  have herr : (Xb-Xa)/(P:Real)<=4*(n:Real)/((b:Real)*M) := by
    rw [hdelta]
    calc
      _ = 4*(n:Real)/((b:Real)*((P:Real)*(2*a))) := by field_simp <;> ring
      _ <= _ := div_le_div_of_nonneg_left (by positivity)
        (mul_pos hbR hM0) (mul_le_mul_of_nonneg_left hr.1.le hbR.le)
  have hsq0 := _root_.mul_le_mul hr.2 hr.2 (by positivity) (by positivity)
  have hsq : (P:Real)^2*(a:Real)^2<=(M:Real)^2 := by nlinarith only [hsq0]
  have hxratio : (P:Real)^2/Xa<=(M:Real)^2*b/((a:Real)*(n:Real)^2) := by
    rw [hXaEq]
    calc
      _ = ((P:Real)^2*(a:Real)^2*b)/((a:Real)*(n:Real)^2) := by field_simp <;> ring
      _ <= _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsq hbR.le) (by positivity)
  have hcoef : 0<=20*((t:Real)^2-1) := by nlinarith
  have hexcess : 20*((t:Real)^2-1)*(P:Real)^2/Xa <=
      20*((t:Real)^2-1)*(M:Real)^2*b/((a:Real)*(n:Real)^2) := by
    calc
      _ = (20*((t:Real)^2-1))*((P:Real)^2/Xa) := by ring
      _ <= (20*((t:Real)^2-1))*((M:Real)^2*b/((a:Real)*(n:Real)^2)) :=
        mul_le_mul_of_nonneg_left hxratio hcoef
      _ = _ := by ring
  change abs (C-(2*(n:Real)/((a:Real)*b))*Real.log 2) <= _
  rw [<- hdelta]
  calc
    _ <= (40*(P:Real)/t+20*((t:Real)^2-1)*(P:Real)^2/Xa)+(Xb-Xa)/(P:Real) := hlog
    _ <= (40*(M:Real)/((a:Real)*t)+
        20*((t:Real)^2-1)*(M:Real)^2*b/((a:Real)*(n:Real)^2))+4*(n:Real)/((b:Real)*M) :=
      _root_.add_le_add (_root_.add_le_add hmain hexcess) herr
    _ = _ := by ring

end Nat.PrimeSieve
