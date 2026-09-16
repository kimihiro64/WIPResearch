/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.KusminLandau
import RobinBV.Mathlib.Analysis.Complex.ReciprocalFloorError

/-!
# Reciprocal phase bounds without a lower phase restriction

Low and high phases are combined before the finite moment and paired-floor
estimates. The exact excess coefficient is retained before the explicit
power-budget relaxation. Every upper-frequency and length condition remains
in the theorem statements; no prime-distribution hypothesis is assumed.
-/

set_option autoImplicit false

namespace Complex

theorem norm_reciprocal_sum_le_low_phase {Y P : Real} {N : Nat}
    (hP : 0<P) (hY : 0<Y) (hN : (N:Real)<=P) (hsmall : Y<=P^2) :
    norm ((Finset.range N).sum (fun j =>
      exp (I*((Y/(P+j):Real):Complex)))) <= 12*Real.pi*P^2/Y := by
  let f : Nat -> Real := fun j => -(Y/(P+j))
  have hinc (j : Nat) :
      f (j+1)-f j = Y/((P+j)*(P+j+1)) := by
    have hpj : 0<P+(j:Real) := by positivity
    have hpj1 : 0<P+(j:Real)+1 := by positivity
    dsimp [f]
    push_cast
    field_simp
    <;> ring
  have hpos (j : Nat) : 0<f (j+1)-f j := by
    rw [hinc]
    positivity
  have hpi (j : Nat) : f (j+1)-f j<=Real.pi := by
    have hj : (0:Real)<=j := Nat.cast_nonneg j
    have hd : P^2<=(P+j)*(P+j+1) := by
      calc
        P^2=P*P := by ring
        _ <= _ := _root_.mul_le_mul (by linarith) (by linarith)
          hP.le (by positivity)
    calc
      _ = Y/((P+j)*(P+j+1)) := hinc j
      _ <= Y/P^2 := div_le_div_of_nonneg_left hY.le (by positivity) hd
      _ <= P^2/P^2 := div_le_div_of_nonneg_right hsmall (sq_nonneg P)
      _ = 1 := by field_simp
      _ <= Real.pi := by linarith [Real.two_le_pi]
  have hanti : Antitone (fun j => f (j+1)-f j) := by
    intro i j hij
    change f (j+1)-f j <= f (i+1)-f i
    rw [hinc, hinc]
    apply div_le_div_of_nonneg_left hY.le (by positivity)
    have hijR : (i:Real)<=j := by exact_mod_cast hij
    exact _root_.mul_le_mul (by linarith) (by linarith)
      (by positivity) (by positivity)
  have hspacing : 0<Y/(P+N)^2 := by positivity
  have hlower (j : Nat) (hj : j<N) :
      Y/(P+N)^2<=f (j+1)-f j := by
    rw [hinc]
    have hjR : (j:Real)+1<=N := by exact_mod_cast (show j+1<=N by omega)
    apply div_le_div_of_nonneg_left hY.le (by positivity)
    calc
      (P+j)*(P+j+1) <= (P+N)*(P+N) :=
        _root_.mul_le_mul (by linarith) (by linarith)
          (by positivity) (by positivity)
      _ = (P+N)^2 := by ring
  have hk := norm_sum_exp_le_of_antitone_increment f N hspacing hpos hpi hanti hlower
  have he : (Finset.range N).sum (fun j => exp (I*((f j:Real):Complex))) =
      (starRingEnd Complex) ((Finset.range N).sum (fun j =>
        exp (I*((Y/(P+j):Real):Complex)))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [<- exp_conj]
    congr 1
    dsimp [f]
    simp only [map_mul, conj_I, conj_ofReal, ofReal_neg]
    ring
  rw [he, norm_conj] at hk
  have hs : (P+N)^2<=(2*P)^2 := by
    gcongr <;> linarith
  calc
    _ <= 3*Real.pi/(Y/(P+N)^2) := hk
    _ = (3*Real.pi*(P+N)^2)/Y := by field_simp
    _ <= (3*Real.pi*(2*P)^2)/Y := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (by positivity)) hY.le
    _ = 12*Real.pi*P^2/Y := by ring

end Complex

namespace Complex

theorem norm_reciprocal_sum_le_all_phase {Y P : Real} {N m : Nat}
    (hP : 0<P) (hY : 0<Y) (hm : 1<=m) (hN : (N:Real)<=P)
    (hmP : (m:Real)^2<=P)
    (hsmall : 2*Y*((m*m:Nat):Real)<=Real.pi*P^3) :
    norm ((Finset.range N).sum (fun j =>
      exp (I*((Y/(P+j):Real):Complex)))) <=
      13*P/Real.sqrt (m:Real)+(m:Real)^2+12*Real.pi*P^2/Y := by
  by_cases hy : P^2<=Y
  next =>
    have h := norm_reciprocal_sum_le_explicit_shift hP hm hN hmP hy hsmall
    exact h.trans (le_add_of_nonneg_right (by positivity))
  next =>
    have h := norm_reciprocal_sum_le_low_phase hP hY hN (le_of_lt (lt_of_not_ge hy))
    have hb : 0<=13*P/Real.sqrt (m:Real)+(m:Real)^2 := by positivity
    linarith

theorem norm_reciprocal_nat_frequency_le_all_phase {Y P : Real} {N m H k : Nat}
    (hP : 0<P) (hY : 0<Y) (hm : 1<=m) (hN : (N:Real)<=P)
    (hmP : (m:Real)^2<=P)
    (hsmall : 2*Y*(H:Real)*((m*m:Nat):Real)<=Real.pi*P^3)
    (hk : 1<=k) (hkH : k<=H) :
    norm ((Finset.range N).sum (fun i =>
      exp (I*(k:Complex)*((Y/(P+i):Real):Complex)))) <=
      13*P/Real.sqrt (m:Real)+(m:Real)^2+12*Real.pi*P^2/Y := by
  have hk1 : (1:Real)<=k := by exact_mod_cast hk
  have hkHr : (k:Real)<=H := by exact_mod_cast hkH
  have hkY : 0<(k:Real)*Y := by positivity
  have hks : 2*((k:Real)*Y)*((m*m:Nat):Real)<=Real.pi*P^3 := by
    calc
      _ = (k:Real)*(2*Y*((m*m:Nat):Real)) := by ring
      _ <= (H:Real)*(2*Y*((m*m:Nat):Real)) := by gcongr
      _ <= _ := by nlinarith only [hsmall]
  have hb := norm_reciprocal_sum_le_all_phase hP hkY hm hN hmP hks
  have he : (Finset.range N).sum (fun i =>
      exp (I*(k:Complex)*((Y/(P+i):Real):Complex))) =
      (Finset.range N).sum (fun i =>
        exp (I*(((k:Real)*Y/(P+i):Real):Complex))) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    push_cast
    ring
  have hc : 12*Real.pi*P^2/((k:Real)*Y)<=12*Real.pi*P^2/Y :=
    div_le_div_of_nonneg_left (by positivity) hY (by nlinarith)
  rw [he]
  exact hb.trans (_root_.add_le_add (le_refl _) hc)

theorem norm_reciprocal_pair_frequency_le_all_phase {Y P : Real} {N m H : Nat}
    (hP : 0<P) (hY : 0<Y) (hm : 1<=m) (hN : (N:Real)<=P)
    (hmP : (m:Real)^2<=P)
    (hsmall : 2*Y*(H:Real)*((m*m:Nat):Real)<=Real.pi*P^3)
    (j k : Nat) (hj : j<H) (hk : k<H) (hjk : Not (j=k)) :
    norm ((Finset.range N).sum (fun i =>
      exp (I*(((j:Int)-k:Int):Complex)*((Y/(P+i):Real):Complex)))) <=
      13*P/Real.sqrt (m:Real)+(m:Real)^2+12*Real.pi*P^2/Y := by
  by_cases h : k<=j
  next =>
    have he : (j:Int)-k=((j-k:Nat):Int) := by omega
    rw [he]
    simpa only [Int.cast_natCast] using
      norm_reciprocal_nat_frequency_le_all_phase hP hY hm hN hmP hsmall
        (show 1<=j-k by omega) (show j-k<=H by omega)
  next =>
    have he : (j:Int)-k= -((k-j:Nat):Int) := by omega
    rw [he, norm_circle_frequency_neg]
    simpa only [Int.cast_natCast] using
      norm_reciprocal_nat_frequency_le_all_phase hP hY hm hN hmP hsmall
        (show 1<=k-j by omega) (show k-j<=H by omega)

end Complex

namespace Complex

theorem reciprocal_fractional_moment_bounds_all_phase {X0 X P : Real} {N m H : Nat}
    (hP : 0<P) (hX0 : 0<X0) (hX0X : X0<=X)
    (hm : 1<=m) (hH : 1<=H) (hN : (N:Real)<=P) (hmP : (m:Real)^2<=P)
    (hsmall : 4*X*(H:Real)*((m*m:Nat):Real)<=P^3)
    (d : Real) (hd : 0<d) (hdp : d<=Real.pi) (hgap : Real.pi<((H:Real)+1)*d) :
    let E : Real := 13*P/Real.sqrt (m:Real)+(m:Real)^2+6*P^2/X0
    let A : Real := 2*Real.pi-2*(Real.pi^2/(H:Real)*(1/d-1/Real.pi))
    let B : Real := (N:Real)+((H:Real)-1)*E
    (N:Real)-(Real.pi+4*d)*B/A <= (Finset.range N).sum (fun i => Int.fract (X/(P+i))) /\
      (Finset.range N).sum (fun i => Int.fract (X/(P+i))) <= (Real.pi+2*d)*B/A := by
  let x : Nat -> Real := fun i => circlePhaseRepresentative ((2*Real.pi*X)/(P+i))
  let E : Real := 13*P/Real.sqrt (m:Real)+(m:Real)^2+6*P^2/X0
  have hX : 0<X := lt_of_lt_of_le hX0 hX0X
  have hs : 2*(2*Real.pi*X)*(H:Real)*((m*m:Nat):Real)<=Real.pi*P^3 := by
    have hh := mul_le_mul_of_nonneg_left hsmall Real.pi_pos.le
    nlinarith only [hh]
  have hc : 12*Real.pi*P^2/(2*Real.pi*X)<=6*P^2/X0 := by
    calc
      _ = 6*P^2/X := by field_simp <;> ring
      _ <= _ := div_le_div_of_nonneg_left (by positivity) hX0 hX0X
  have he : forall j, j<H -> forall k, k<H -> Not (j=k) ->
      norm ((Finset.range N).sum (fun i =>
        exp (I*(((j:Int)-k:Int):Complex)*(x i:Complex)))) <= E := by
    intro j hj k hk hjk
    dsimp only [x, E]
    simp_rw [exp_circlePhaseRepresentative]
    have hf := norm_reciprocal_pair_frequency_le_all_phase hP
      (show 0<2*Real.pi*X by positivity) hm hN hmP hs j k hj hk hjk
    exact hf.trans (_root_.add_le_add (le_refl _) hc)
  have hx : forall i, Membership.mem (Finset.range N) i -> 0<=x i /\ x i<=2*Real.pi := by
    intro i hi
    exact And.intro (circlePhaseRepresentative_nonneg _) (circlePhaseRepresentative_lt _).le
  have hb := finite_phase_moment_bounds (Finset.range N) x H hH E d hd hdp hgap hx he
  have hsum : (Finset.range N).sum x/(2*Real.pi) =
      (Finset.range N).sum (fun i => Int.fract (X/(P+i))) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (2*Real.pi*X)/(P+i)=2*Real.pi*(X/(P+i)) by ring]
    exact circlePhaseRepresentative_scale _
  simp only [Finset.card_range, hsum] at hb
  exact hb

theorem reciprocal_floor_interval_error_all_phase {Xa Xb P : Real} {N m H : Nat}
    (hP : 0<P) (hXa : 0<Xa) (hXab : Xa<=Xb)
    (hm : 1<=m) (hH : 1<=H) (hN : (N:Real)<=P) (hmP : (m:Real)^2<=P)
    (hsmall : 4*Xb*(H:Real)*((m*m:Nat):Real)<=P^3)
    (d : Real) (hd : 0<d) (hdp : d<=Real.pi) (hgap : Real.pi<((H:Real)+1)*d) :
    let E : Real := 13*P/Real.sqrt (m:Real)+(m:Real)^2+6*P^2/Xa
    let A : Real := 2*Real.pi-2*(Real.pi^2/(H:Real)*(1/d-1/Real.pi))
    let B : Real := (N:Real)+((H:Real)-1)*E
    abs ((Finset.range N).sum (fun i =>
      (Int.floor (Xb/(P+i)):Real)-(Int.floor (Xa/(P+i)):Real))-
      (Xb-Xa)*(Finset.range N).sum (fun i => 1/(P+i))) <= (2*Real.pi+6*d)*B/A-N := by
  let E : Real := 13*P/Real.sqrt (m:Real)+(m:Real)^2+6*P^2/Xa
  let A : Real := 2*Real.pi-2*(Real.pi^2/(H:Real)*(1/d-1/Real.pi))
  let B : Real := (N:Real)+((H:Real)-1)*E
  let fa : Real := (Finset.range N).sum (fun i => Int.fract (Xa/(P+i)))
  let fb : Real := (Finset.range N).sum (fun i => Int.fract (Xb/(P+i)))
  have hsa : 4*Xa*(H:Real)*((m*m:Nat):Real)<=P^3 := by
    calc
      _ <= 4*Xb*(H:Real)*((m*m:Nat):Real) := by gcongr
      _ <= _ := hsmall
  have ha := reciprocal_fractional_moment_bounds_all_phase hP hXa (le_refl Xa)
    hm hH hN hmP hsa d hd hdp hgap
  have hb := reciprocal_fractional_moment_bounds_all_phase hP hXa hXab
    hm hH hN hmP hsmall d hd hdp hgap
  change (N:Real)-(Real.pi+4*d)*B/A<=fa /\ fa<=(Real.pi+2*d)*B/A at ha
  change (N:Real)-(Real.pi+4*d)*B/A<=fb /\ fb<=(Real.pi+2*d)*B/A at hb
  change abs (_-_)<=(2*Real.pi+6*d)*B/A-N
  rw [reciprocal_floor_interval_eq_fract, Finset.sum_sub_distrib]
  change abs (fa-fb)<=(2*Real.pi+6*d)*B/A-N
  have he : (2*Real.pi+6*d)*B/A-N =
      (Real.pi+2*d)*B/A-((N:Real)-(Real.pi+4*d)*B/A) := by ring
  rw [he]
  apply abs_le.mpr
  constructor <;> linarith only [ha.1, ha.2, hb.1, hb.2]

end Complex

namespace Complex

theorem paired_floor_parameter_budget_exact_excess {t P N L : Real}
    (ht : 2<=t) (hP : t^15<=P) (hNP : N<=P) :
    let A : Real := 2*Real.pi-2*(Real.pi^2/t^2*(1/(Real.pi/t)-1/Real.pi))
    (2*Real.pi+6*(Real.pi/t))*(N+(t^2-1)*(13*P/t^3+t^12+L))/A-N <=
      40*P/t+(t^2+3*t)/(t^2-t+1)*(t^2-1)*L := by
  let D : Real := t^2-t+1
  let A : Real := 2*Real.pi-2*(Real.pi^2/t^2*(1/(Real.pi/t)-1/Real.pi))
  have ht0 : 0<t := by linarith
  have hD : 0<D := by dsimp only [D]; nlinarith [sq_nonneg (t-1/2)]
  have heA : A=2*Real.pi*D/t^2 := by
    dsimp only [A, D]
    field_simp [ne_of_gt ht0, ne_of_gt Real.pi_pos]
    ring
  have heR : (2*Real.pi+6*(Real.pi/t))/A=(t^2+3*t)/D := by
    rw [heA]
    field_simp [ne_of_gt ht0, ne_of_gt Real.pi_pos, ne_of_gt hD]
    ring
  have hb := paired_floor_parameter_budget ht hP hNP
  change (2*Real.pi+6*(Real.pi/t))*(N+(t^2-1)*(13*P/t^3+t^12+L))/A-N <=
    40*P/t+(t^2+3*t)/D*(t^2-1)*L
  calc
    _ = ((2*Real.pi+6*(Real.pi/t))*(N+(t^2-1)*(13*P/t^3+t^12))/A-N) +
        (t^2+3*t)/D*(t^2-1)*L := by rw [<- heR]; ring
    _ <= _ := _root_.add_le_add hb (le_refl _)

theorem paired_floor_excess_coefficient_le {t : Real} (ht : 2<=t) :
    0 <= (t^2+3*t)/(t^2-t+1)*(t^2-1) /\
      (t^2+3*t)/(t^2-t+1)*(t^2-1) <= (10/3:Real)*(t^2-1) := by
  let D : Real := t^2-t+1
  have ht0 : 0<t := by linarith
  have hD : 0<D := by dsimp only [D]; nlinarith [sq_nonneg (t-1/2)]
  have hpow : 0<=t^2-1 := by nlinarith
  have hpoly : t^2+3*t<=(10/3:Real)*D := by
    have hh := mul_nonneg (show 0<=t-2 by linarith) (show 0<=7*t-5 by linarith)
    dsimp only [D]
    nlinarith
  have hr : (t^2+3*t)/D<=(10/3:Real) := by
    calc
      _ <= ((10/3:Real)*D)/D := div_le_div_of_nonneg_right hpoly hD.le
      _ = _ := by field_simp [ne_of_gt hD]
  exact And.intro (mul_nonneg (div_nonneg (by positivity) hD.le) hpow)
    (mul_le_mul_of_nonneg_right hr hpow)

theorem paired_floor_parameter_budget_excess {t P N L : Real}
    (ht : 2<=t) (hP : t^15<=P) (hNP : N<=P) (hL : 0<=L) :
    let A : Real := 2*Real.pi-2*(Real.pi^2/t^2*(1/(Real.pi/t)-1/Real.pi))
    (2*Real.pi+6*(Real.pi/t))*(N+(t^2-1)*(13*P/t^3+t^12+L))/A-N <=
      40*P/t+(10/3:Real)*(t^2-1)*L := by
  have hb := paired_floor_parameter_budget_exact_excess (L:=L) ht hP hNP
  have hc := mul_le_mul_of_nonneg_right (paired_floor_excess_coefficient_le ht).2 hL
  exact hb.trans (_root_.add_le_add (le_refl _) hc)

end Complex

namespace Complex

theorem reciprocal_floor_interval_error_power_all_phase {Xa Xb P : Real} {N t : Nat}
    (ht : 2<=t) (hN : (N:Real)<=P) (htP : (t:Real)^15<=P)
    (hXa : 0<Xa) (hXab : Xa<=Xb) (hsmall : 4*Xb*(t:Real)^14<=P^3) :
    abs ((Finset.range N).sum (fun i =>
      (Int.floor (Xb/(P+i)):Real)-(Int.floor (Xa/(P+i)):Real))-
      (Xb-Xa)*(Finset.range N).sum (fun i => 1/(P+i))) <=
      40*P/(t:Real)+((t:Real)^2+3*t)/((t:Real)^2-t+1)*((t:Real)^2-1)*(6*P^2/Xa) := by
  have ht0 : 0<t := by omega
  have htr : (2:Real)<=t := by exact_mod_cast ht
  have htr0 : 0<(t:Real) := by exact_mod_cast ht0
  have hP : 0<P := (pow_pos htr0 15).trans_le htP
  have hm : 1<=t^6 := by have h := pow_pos ht0 6; omega
  have hH : 1<=t^2 := by have h := pow_pos ht0 2; omega
  have ht3 : (1:Real)<=(t:Real)^3 := by
    calc
      1=(1:Real)^3 := by norm_num
      _ <= (t:Real)^3 := by gcongr <;> linarith
  have h12 : (t:Real)^12<=(t:Real)^15 := by
    calc
      _ = (t:Real)^12*1 := by ring
      _ <= (t:Real)^12*(t:Real)^3 :=
        mul_le_mul_of_nonneg_left ht3 (by positivity)
      _ = _ := by ring
  have hmP : ((t^6:Nat):Real)^2<=P := by
    calc
      _ = (t:Real)^12 := by push_cast; ring
      _ <= P := h12.trans htP
  have hs : 4*Xb*((t^2:Nat):Real)*((t^6*t^6:Nat):Real)<=P^3 := by
    calc
      _ = 4*Xb*(t:Real)^14 := by push_cast; ring
      _ <= _ := hsmall
  have hd : 0<Real.pi/(t:Real) := _root_.div_pos Real.pi_pos htr0
  have hdp : Real.pi/(t:Real)<=Real.pi := by
    calc
      _ <= Real.pi/1 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
      _ = _ := by ring
  have hgap : Real.pi<(((t^2:Nat):Real)+1)*(Real.pi/(t:Real)) := by
    have hD : 0<(t:Real)^2-(t:Real)+1 := by nlinarith [sq_nonneg ((t:Real)-1/2)]
    have he : (((t^2:Nat):Real)+1)*(Real.pi/(t:Real))-Real.pi =
        Real.pi*((t:Real)^2-(t:Real)+1)/(t:Real) := by
      push_cast
      field_simp [ne_of_gt htr0] <;> ring
    apply sub_pos.mp
    rw [he]
    exact _root_.div_pos (mul_pos Real.pi_pos hD) htr0
  have hf := reciprocal_floor_interval_error_all_phase (m:=t^6) (H:=t^2)
    hP hXa hXab hm hH hN hmP hs (Real.pi/(t:Real)) hd hdp hgap
  have hsqrt : Real.sqrt ((t:Real)^6)=(t:Real)^3 := by
    rw [show (t:Real)^6=((t:Real)^3)^2 by ring, Real.sqrt_sq (by positivity)]
  simp only [Nat.cast_pow, hsqrt] at hf
  rw [show ((t:Real)^6)^2=(t:Real)^12 by ring] at hf
  exact hf.trans (paired_floor_parameter_budget_exact_excess (L:=6*P^2/Xa) htr htP hN)

theorem reciprocal_floor_interval_error_power_all_phase_simple {Xa Xb P : Real} {N t : Nat}
    (ht : 2<=t) (hN : (N:Real)<=P) (htP : (t:Real)^15<=P)
    (hXa : 0<Xa) (hXab : Xa<=Xb) (hsmall : 4*Xb*(t:Real)^14<=P^3) :
    abs ((Finset.range N).sum (fun i =>
      (Int.floor (Xb/(P+i)):Real)-(Int.floor (Xa/(P+i)):Real))-
      (Xb-Xa)*(Finset.range N).sum (fun i => 1/(P+i))) <=
      40*P/(t:Real)+20*((t:Real)^2-1)*P^2/Xa := by
  have htr : (2:Real)<=t := by exact_mod_cast ht
  have hb := reciprocal_floor_interval_error_power_all_phase ht hN htP hXa hXab hsmall
  have hc := mul_le_mul_of_nonneg_right (paired_floor_excess_coefficient_le htr).2
    (show 0<=6*P^2/Xa by positivity)
  have he : ((t:Real)^2+3*t)/((t:Real)^2-t+1)*((t:Real)^2-1)*(6*P^2/Xa) <=
      20*((t:Real)^2-1)*P^2/Xa := by
    calc
      _ <= (10/3:Real)*((t:Real)^2-1)*(6*P^2/Xa) := hc
      _ = _ := by ring
  exact hb.trans (_root_.add_le_add (le_refl _) he)

end Complex
