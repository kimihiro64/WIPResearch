/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.FejerMoment
import RobinBV.Mathlib.Analysis.Complex.ReciprocalDistribution

/-!
# Explicit paired reciprocal floor-row errors

The exact paired floor identity cancels the common fractional-part main
terms before taking errors. The proved reciprocal phase moments yield an
explicit uniform row bound. A polynomial parameter choice gives error at
most 40P/t under the displayed scale restrictions, while the universal
unit-per-row baseline remains available on the same expression.
These are divisor-row source estimates; signed composite allowance and
prime-existence claims require a separate arithmetic application.
-/

set_option autoImplicit false

namespace Complex

theorem reciprocal_floor_interval_eq_fract {Xa Xb P : Real} (N : Nat) :
    (Finset.range N).sum (fun i =>
      (Int.floor (Xb/(P+i)) : Real)-(Int.floor (Xa/(P+i)) : Real))-
      (Xb-Xa)*(Finset.range N).sum (fun i => 1/(P+i)) =
    (Finset.range N).sum (fun i => Int.fract (Xa/(P+i))-Int.fract (Xb/(P+i))) := by
  calc
    _ = (Finset.range N).sum (fun i =>
        (Int.floor (Xb/(P+i)) : Real)-(Int.floor (Xa/(P+i)) : Real)-
          (Xb-Xa)*(1/(P+i))) := by simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold Int.fract
      ring

theorem reciprocal_floor_interval_error_le_card {Xa Xb P : Real} (N : Nat) :
    abs ((Finset.range N).sum (fun i =>
      (Int.floor (Xb/(P+i)) : Real)-(Int.floor (Xa/(P+i)) : Real))-
      (Xb-Xa)*(Finset.range N).sum (fun i => 1/(P+i))) <= (N : Real) := by
  rw [reciprocal_floor_interval_eq_fract]
  calc
    _ <= (Finset.range N).sum (fun i => abs (Int.fract (Xa/(P+i))-Int.fract (Xb/(P+i)))) := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.range N)
        (fun i => Int.fract (Xa/(P+i))-Int.fract (Xb/(P+i)))
    _ <= (Finset.range N).sum (fun _ => (1 : Real)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply le_of_lt
      apply abs_lt.mpr
      constructor <;> linarith only [Int.fract_nonneg (Xa/(P+i)), Int.fract_lt_one (Xa/(P+i)),
        Int.fract_nonneg (Xb/(P+i)), Int.fract_lt_one (Xb/(P+i))]
    _ = _ := by simp

theorem circlePhaseRepresentative_scale (t : Real) :
    circlePhaseRepresentative (2*Real.pi*t)/(2*Real.pi) = Int.fract t := by
  unfold circlePhaseRepresentative
  have he : (2*Real.pi*t)/(2*Real.pi) = t := by field_simp [ne_of_gt Real.pi_pos]
  rw [he]
  field_simp [ne_of_gt Real.pi_pos]

theorem reciprocal_fractional_moment_bounds {X P : Real} {N m H : Nat}
    (hP : 0 < P) (hm : 1 <= m) (hH : 1 <= H) (hN : (N : Real) <= P)
    (hmP : (m : Real)^2 <= P) (hX : P^2 <= 2*Real.pi*X)
    (hsmall : 4*X*(H : Real)*((m*m : Nat) : Real) <= P^3)
    (d : Real) (hd : 0 < d) (hdp : d <= Real.pi) (hgap : Real.pi < ((H : Real)+1)*d) :
    let E : Real := 13*P/Real.sqrt (m : Real)+(m : Real)^2
    let A : Real := 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi))
    let B : Real := (N : Real)+((H : Real)-1)*E
    (N : Real)-(Real.pi+4*d)*B/A <= (Finset.range N).sum (fun i => Int.fract (X/(P+i))) /\
      (Finset.range N).sum (fun i => Int.fract (X/(P+i))) <= (Real.pi+2*d)*B/A := by
  classical
  let x : Nat -> Real := fun i => circlePhaseRepresentative ((2*Real.pi*X)/(P+i))
  let E : Real := 13*P/Real.sqrt (m : Real)+(m : Real)^2
  have hs : 2*(2*Real.pi*X)*(H : Real)*((m*m : Nat) : Real) <= Real.pi*P^3 := by
    have hh := mul_le_mul_of_nonneg_left hsmall Real.pi_pos.le
    nlinarith only [hh]
  have he : forall j, j < H -> forall k, k < H -> Not (j=k) ->
      norm ((Finset.range N).sum (fun i =>
        exp (I*(((j : Int)-k : Int) : Complex)*(x i : Complex)))) <= E := by
    intro j hj k hk hjk
    dsimp only [x, E]
    simp_rw [exp_circlePhaseRepresentative]
    exact norm_reciprocal_pair_frequency_le hP hm hN hmP hX hs j k hj hk hjk
  have hx : forall i, Membership.mem (Finset.range N) i -> 0 <= x i /\ x i <= 2*Real.pi := by
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

theorem reciprocal_floor_interval_error {Xa Xb P : Real} {N m H : Nat}
    (hP : 0 < P) (hm : 1 <= m) (hH : 1 <= H) (hN : (N : Real) <= P)
    (hmP : (m : Real)^2 <= P) (hXa : P^2 <= 2*Real.pi*Xa) (hXab : Xa <= Xb)
    (hsmall : 4*Xb*(H : Real)*((m*m : Nat) : Real) <= P^3)
    (d : Real) (hd : 0 < d) (hdp : d <= Real.pi) (hgap : Real.pi < ((H : Real)+1)*d) :
    let E : Real := 13*P/Real.sqrt (m : Real)+(m : Real)^2
    let A : Real := 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi))
    let B : Real := (N : Real)+((H : Real)-1)*E
    abs ((Finset.range N).sum (fun i =>
      (Int.floor (Xb/(P+i)) : Real)-(Int.floor (Xa/(P+i)) : Real))-
      (Xb-Xa)*(Finset.range N).sum (fun i => 1/(P+i))) <=
        (2*Real.pi+6*d)*B/A-N := by
  classical
  let E : Real := 13*P/Real.sqrt (m : Real)+(m : Real)^2
  let A : Real := 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi))
  let B : Real := (N : Real)+((H : Real)-1)*E
  let fa : Real := (Finset.range N).sum (fun i => Int.fract (Xa/(P+i)))
  let fb : Real := (Finset.range N).sum (fun i => Int.fract (Xb/(P+i)))
  have hXb : P^2 <= 2*Real.pi*Xb :=
    hXa.trans (mul_le_mul_of_nonneg_left hXab (by positivity))
  have hsa : 4*Xa*(H : Real)*((m*m : Nat) : Real) <= P^3 := by
    calc
      _ <= 4*Xb*(H : Real)*((m*m : Nat) : Real) := by gcongr
      _ <= _ := hsmall
  have ha := reciprocal_fractional_moment_bounds hP hm hH hN hmP hXa hsa d hd hdp hgap
  have hb := reciprocal_fractional_moment_bounds hP hm hH hN hmP hXb hsmall d hd hdp hgap
  change (N : Real)-(Real.pi+4*d)*B/A <= fa /\ fa <= (Real.pi+2*d)*B/A at ha
  change (N : Real)-(Real.pi+4*d)*B/A <= fb /\ fb <= (Real.pi+2*d)*B/A at hb
  have he : (Finset.range N).sum (fun i =>
      (Int.floor (Xb/(P+i)) : Real)-(Int.floor (Xa/(P+i)) : Real))-
      (Xb-Xa)*(Finset.range N).sum (fun i => 1/(P+i)) = fa-fb := by
    calc
      _ = (Finset.range N).sum (fun i =>
          (Int.floor (Xb/(P+i)) : Real)-(Int.floor (Xa/(P+i)) : Real)-
          (Xb-Xa)*(1/(P+i))) := by simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by
        dsimp only [fa, fb]
        rw [<- Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        unfold Int.fract
        ring
  change abs (_-_) <= (2*Real.pi+6*d)*B/A-N
  rw [he]
  rw [show (2*Real.pi+6*d)*B/A-N =
    (Real.pi+2*d)*B/A-((N : Real)-(Real.pi+4*d)*B/A) by ring]
  apply abs_le.mpr
  constructor <;> linarith only [ha.1, ha.2, hb.1, hb.2]

theorem paired_floor_parameter_budget {t P N : Real}
    (ht : 2 <= t) (hP : t^15 <= P) (hNP : N <= P) :
    let A : Real := 2*Real.pi-2*(Real.pi^2/t^2*(1/(Real.pi/t)-1/Real.pi))
    (2*Real.pi+6*(Real.pi/t))*(N+(t^2-1)*(13*P/t^3+t^12))/A-N <= 40*P/t := by
  let D : Real := t^2-t+1
  let A : Real := 2*Real.pi-2*(Real.pi^2/t^2*(1/(Real.pi/t)-1/Real.pi))
  let K : Real := (t^2+3*t)/D
  have ht0 : 0 < t := by linarith
  have hP0 : 0 < P := (pow_pos ht0 15).trans_le hP
  have hD : 0 < D := by dsimp only [D]; nlinarith [sq_nonneg (t-1/2)]
  have heA : A = 2*Real.pi*D/t^2 := by
    dsimp only [A, D]
    field_simp [ne_of_gt ht0, ne_of_gt Real.pi_pos]
    ring
  have hA : 0 < A := by rw [heA]; positivity
  have heK : (2*Real.pi+6*(Real.pi/t))/A = K := by
    rw [heA]
    dsimp only [K]
    field_simp [ne_of_gt ht0, ne_of_gt Real.pi_pos, ne_of_gt hD]
    ring
  have hK1 : 1 <= K := by
    calc
      1 = D/D := by field_simp [ne_of_gt hD]
      _ <= (t^2+3*t)/D := div_le_div_of_nonneg_right (by dsimp only [D]; linarith) hD.le
      _ = K := rfl
  have hE : 13*P/t^3+t^12 <= 14*P/t^3 := by
    have hh := div_le_div_of_nonneg_right hP (show 0 <= t^3 by positivity)
    have he : t^15/t^3 = t^12 := by field_simp [ne_of_gt ht0]
    rw [he] at hh
    calc
      _ <= 13*P/t^3+P/t^3 := add_le_add (le_refl _) hh
      _ = _ := by ring
  have hpoly : 0 <= 22*t^3-81*t^2+54*t+42 := by
    have he : 22*t^3-81*t^2+54*t+42 =
        22*(t-2)^3+(3/17 : Real)*(17*(t-2)-1)^2+31/17 := by ring
    rw [he]
    have hnon : 0 <= t-2 := by linarith
    positivity
  have hscalar : K*(1+(t^2-1)*14/t^3)-1 <= 40/t := by
    have he : 40/t-(K*(1+(t^2-1)*14/t^3)-1) =
        (22*t^3-81*t^2+54*t+42)/(t^2*D) := by
      dsimp only [K]
      field_simp [ne_of_gt ht0, ne_of_gt hD]
      dsimp only [D]
      ring
    apply sub_nonneg.mp
    rw [he]
    exact div_nonneg hpoly (by positivity)
  have hcoef : 0 <= K*(t^2-1) := by
    have hk : 0 <= K := by linarith
    have ht2 : 0 <= t^2-1 := by nlinarith
    exact mul_nonneg hk ht2
  change (2*Real.pi+6*(Real.pi/t))*(N+(t^2-1)*(13*P/t^3+t^12))/A-N <= 40*P/t
  calc
    _ = (K-1)*N+(K*(t^2-1))*(13*P/t^3+t^12) := by rw [<- heK]; ring
    _ <= (K-1)*P+(K*(t^2-1))*(14*P/t^3) :=
      add_le_add (mul_le_mul_of_nonneg_left hNP (sub_nonneg.mpr hK1))
        (mul_le_mul_of_nonneg_left hE hcoef)
    _ = P*(K*(1+(t^2-1)*14/t^3)-1) := by ring
    _ <= P*(40/t) := mul_le_mul_of_nonneg_left hscalar hP0.le
    _ = _ := by ring

theorem reciprocal_floor_interval_error_power {Xa Xb P : Real} {N t : Nat}
    (ht : 2 <= t) (hN : (N : Real) <= P) (htP : (t : Real)^15 <= P)
    (hXa : P^2 <= 2*Real.pi*Xa) (hXab : Xa <= Xb)
    (hsmall : 4*Xb*(t : Real)^14 <= P^3) :
    abs ((Finset.range N).sum (fun i =>
      (Int.floor (Xb/(P+i)) : Real)-(Int.floor (Xa/(P+i)) : Real))-
      (Xb-Xa)*(Finset.range N).sum (fun i => 1/(P+i))) <= 40*P/(t : Real) := by
  have ht0 : 0 < t := by omega
  have htr : (2 : Real) <= t := by exact_mod_cast ht
  have htr0 : 0 < (t : Real) := by exact_mod_cast ht0
  have hP : 0 < P := (pow_pos htr0 15).trans_le htP
  have hm : 1 <= t^6 := by have h := pow_pos ht0 6; omega
  have hH : 1 <= t^2 := by have h := pow_pos ht0 2; omega
  have ht3 : (1 : Real) <= (t : Real)^3 := by
    calc
      1 = (1 : Real)^3 := by norm_num
      _ <= (t : Real)^3 := by gcongr <;> linarith
  have h12 : (t : Real)^12 <= (t : Real)^15 := by
    calc
      _ = (t : Real)^12*1 := by ring
      _ <= (t : Real)^12*(t : Real)^3 :=
        mul_le_mul_of_nonneg_left ht3 (by positivity)
      _ = _ := by ring
  have hmP : ((t^6 : Nat) : Real)^2 <= P := by
    calc
      _ = (t : Real)^12 := by push_cast; ring
      _ <= P := h12.trans htP
  have hs : 4*Xb*((t^2 : Nat) : Real)*(((t^6*t^6 : Nat)) : Real) <= P^3 := by
    calc
      _ = 4*Xb*(t : Real)^14 := by push_cast; ring
      _ <= _ := hsmall
  have hd : 0 < Real.pi/(t : Real) := _root_.div_pos Real.pi_pos htr0
  have hdp : Real.pi/(t : Real) <= Real.pi := by
    calc
      _ <= Real.pi/1 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
      _ = _ := by ring
  have hgap : Real.pi < (((t^2 : Nat) : Real)+1)*(Real.pi/(t : Real)) := by
    have hD : 0 < (t : Real)^2-(t : Real)+1 := by nlinarith [sq_nonneg ((t : Real)-1/2)]
    have he : (((t^2 : Nat) : Real)+1)*(Real.pi/(t : Real))-Real.pi =
        Real.pi*((t : Real)^2-(t : Real)+1)/(t : Real) := by
      push_cast
      field_simp [ne_of_gt htr0] <;> ring
    apply sub_pos.mp
    rw [he]
    exact _root_.div_pos (mul_pos Real.pi_pos hD) htr0
  have hf := reciprocal_floor_interval_error (m := t^6) (H := t^2)
    hP hm hH hN hmP hXa hXab hs (Real.pi/(t : Real)) hd hdp hgap
  have hsqrt : Real.sqrt ((t : Real)^6) = (t : Real)^3 := by
    rw [show (t : Real)^6=((t : Real)^3)^2 by ring, Real.sqrt_sq (by positivity)]
  simp only [Nat.cast_pow, hsqrt] at hf
  rw [show ((t : Real)^6)^2=(t : Real)^12 by ring] at hf
  exact hf.trans (paired_floor_parameter_budget htr htP hN)

end Complex
