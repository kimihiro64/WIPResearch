/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.Order.Floor.Ring
import RobinBV.Mathlib.Analysis.Complex.FejerCount
import RobinBV.Mathlib.Analysis.Complex.ReciprocalPowerBound

/-!
# Explicit finite distribution of reciprocal phases

The proved reciprocal-sum estimate controls every required integer frequency.
An exact circle representative preserves those frequencies. Two-sided finite
interval counting then gives explicit estimates for the actual fractional
reciprocal sequence, with all scale and positive-normalization conditions.
No additional distribution theorem is assumed. Divisor-lattice and signed
sieve applications require their own endpoint and coefficient accounting.
-/

set_option autoImplicit false

namespace Complex

theorem norm_reciprocal_nat_frequency_le {Y P : Real} {N m H k : Nat}
    (hP : 0 < P) (hm : 1 <= m) (hN : (N : Real) <= P)
    (hmP : (m : Real)^2 <= P) (hY : P^2 <= Y)
    (hsmall : 2*Y*(H : Real)*((m*m : Nat) : Real) <= Real.pi*P^3)
    (hk : 1 <= k) (hkH : k <= H) :
    norm ((Finset.range N).sum (fun i =>
      exp (I*(k : Complex)*((Y/(P+i) : Real) : Complex)))) <=
        13*P/Real.sqrt (m : Real)+(m : Real)^2 := by
  have hY0 : 0 < Y := (sq_pos_of_pos hP).trans_le hY
  have hk1 : (1 : Real) <= k := by exact_mod_cast hk
  have hkHr : (k : Real) <= H := by exact_mod_cast hkH
  have hYs : P^2 <= (k : Real)*Y := by nlinarith
  have hks : 2*((k : Real)*Y)*((m*m : Nat) : Real) <= Real.pi*P^3 := by
    calc
      _ = (k : Real)*(2*Y*((m*m : Nat) : Real)) := by ring
      _ <= (H : Real)*(2*Y*((m*m : Nat) : Real)) := by gcongr
      _ <= _ := by nlinarith only [hsmall]
  have hb := norm_reciprocal_sum_le_explicit_shift (N := N) hP hm hN hmP hYs hks
  have he : (Finset.range N).sum (fun i =>
      exp (I*(k : Complex)*((Y/(P+i) : Real) : Complex))) =
        (Finset.range N).sum (fun i => exp (I*(((k : Real)*Y/(P+i) : Real) : Complex))) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    push_cast
    ring
  rw [he]
  exact hb

theorem norm_circle_frequency_neg {v : Type*} (s : Finset v) (x : v -> Real) (k : Int) :
    norm (s.sum (fun i => exp (I*((-k : Int) : Complex)*(x i : Complex)))) =
      norm (s.sum (fun i => exp (I*(k : Complex)*(x i : Complex)))) := by
  have he : s.sum (fun i => exp (I*((-k : Int) : Complex)*(x i : Complex))) =
      (starRingEnd Complex) (s.sum (fun i => exp (I*(k : Complex)*(x i : Complex)))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [<- exp_conj]
    congr 1
    simp only [map_mul, conj_I, map_intCast, conj_ofReal, Int.cast_neg]
    ring
  rw [he, norm_conj]

theorem norm_reciprocal_pair_frequency_le {Y P : Real} {N m H : Nat}
    (hP : 0 < P) (hm : 1 <= m) (hN : (N : Real) <= P)
    (hmP : (m : Real)^2 <= P) (hY : P^2 <= Y)
    (hsmall : 2*Y*(H : Real)*((m*m : Nat) : Real) <= Real.pi*P^3)
    (j k : Nat) (hj : j < H) (hk : k < H) (hjk : Not (j=k)) :
    norm ((Finset.range N).sum (fun i =>
      exp (I*(((j : Int)-k : Int) : Complex)*((Y/(P+i) : Real) : Complex)))) <=
        13*P/Real.sqrt (m : Real)+(m : Real)^2 := by
  by_cases h : k <= j
  next =>
    have he : (j : Int)-k = ((j-k : Nat) : Int) := by omega
    rw [he]
    simpa only [Int.cast_natCast] using
      norm_reciprocal_nat_frequency_le hP hm hN hmP hY hsmall
        (show 1 <= j-k by omega) (show j-k <= H by omega)
  next =>
    have he : (j : Int)-k = -((k-j : Nat) : Int) := by omega
    rw [he, norm_circle_frequency_neg]
    simpa only [Int.cast_natCast] using
      norm_reciprocal_nat_frequency_le hP hm hN hmP hY hsmall
        (show 1 <= k-j by omega) (show k-j <= H by omega)

noncomputable def circlePhaseRepresentative (t : Real) : Real :=
  2*Real.pi*Int.fract (t/(2*Real.pi))

theorem circlePhaseRepresentative_nonneg (t : Real) :
    0 <= circlePhaseRepresentative t :=
  mul_nonneg (by positivity) (Int.fract_nonneg _)

theorem circlePhaseRepresentative_lt (t : Real) :
    circlePhaseRepresentative t < 2*Real.pi := by
  have h := mul_lt_mul_of_pos_left (Int.fract_lt_one (t/(2*Real.pi)))
    (show 0 < 2*Real.pi by positivity)
  simpa only [mul_one, circlePhaseRepresentative] using h

theorem circlePhaseRepresentative_eq (t : Real) :
    circlePhaseRepresentative t = t-2*Real.pi*(Int.floor (t/(2*Real.pi)) : Real) := by
  unfold circlePhaseRepresentative Int.fract
  field_simp [ne_of_gt Real.pi_pos]

theorem exp_circlePhaseRepresentative (k : Int) (t : Real) :
    exp (I*(k : Complex)*(circlePhaseRepresentative t : Complex)) =
      exp (I*(k : Complex)*(t : Complex)) := by
  have he : I*(k : Complex)*(circlePhaseRepresentative t : Complex) =
      I*(k : Complex)*(t : Complex)+
        (((-k*Int.floor (t/(2*Real.pi)) : Int) : Complex)*(2*Real.pi*I)) := by
    rw [circlePhaseRepresentative_eq]
    push_cast
    ring
  rw [he, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

theorem reciprocal_phase_count_bounds {Y P : Real} {N m H : Nat}
    (hP : 0 < P) (hm : 1 <= m) (hH : 1 <= H) (hN : (N : Real) <= P)
    (hmP : (m : Real)^2 <= P) (hY : P^2 <= Y)
    (hsmall : 2*Y*(H : Real)*((m*m : Nat) : Real) <= Real.pi*P^3)
    (a b d : Real) (ha : 0 <= a) (hab : a <= b) (hb : b <= 2*Real.pi)
    (hd : 0 < d) (hdp : d <= Real.pi) (hgap : Real.pi < ((H : Real)+1)*d) :
    let E : Real := 13*P/Real.sqrt (m : Real)+(m : Real)^2
    let A : Real := 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi))
    let C : Real := ((Finset.range N).filter (fun i : Nat =>
      a <= circlePhaseRepresentative (Y/(P+i)) /\
      circlePhaseRepresentative (Y/(P+i)) <= b)).card
    (N : Real)-((2*Real.pi-(b-a)+4*d)*((N : Real)+((H : Real)-1)*E))/A <= C /\
      C <= ((b-a+2*d)*((N : Real)+((H : Real)-1)*E))/A := by
  classical
  let E : Real := 13*P/Real.sqrt (m : Real)+(m : Real)^2
  let A : Real := 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi))
  let x : Nat -> Real := fun i => circlePhaseRepresentative (Y/(P+i))
  let C : Real := ((Finset.range N).filter (fun i => a <= x i /\ x i <= b)).card
  change (N : Real)-((2*Real.pi-(b-a)+4*d)*((N : Real)+((H : Real)-1)*E))/A <= C /\
    C <= ((b-a+2*d)*((N : Real)+((H : Real)-1)*E))/A
  have he : forall j, j < H -> forall k, k < H -> Not (j=k) ->
      norm ((Finset.range N).sum (fun i =>
        exp (I*(((j : Int)-k : Int) : Complex)*(x i : Complex)))) <= E := by
    intro j hj k hk hjk
    dsimp only [x, E]
    simp_rw [exp_circlePhaseRepresentative]
    exact norm_reciprocal_pair_frequency_le hP hm hN hmP hY hsmall j k hj hk hjk
  have hx : forall i, Membership.mem (Finset.range N) i -> 0 <= x i /\ x i <= 2*Real.pi := by
    intro i hi
    exact And.intro (circlePhaseRepresentative_nonneg _)
      (circlePhaseRepresentative_lt _).le
  have hA : 0 < A := finiteFejer_mass_factor_pos H hH d hd hgap
  have hupper := finiteFejer_arc_count_div_upper (Finset.range N) x H hH E a b d
    hab hd hdp hgap he
  have hlower := finiteFejer_arc_count_lower (Finset.range N) x H hH E a b d
    ha hab hb hd hdp hgap hx he
  simp only [Finset.card_range] at hupper hlower
  apply And.intro
  next =>
    change A*(N : Real)-_ <= A*C at hlower
    calc
      _ = (A*(N : Real)-(2*Real.pi-(b-a)+4*d)*((N : Real)+((H : Real)-1)*E))/A := by
        field_simp [ne_of_gt hA]
      _ <= (A*C)/A := div_le_div_of_nonneg_right hlower hA.le
      _ = C := by field_simp [ne_of_gt hA]
  next => exact hupper

end Complex
