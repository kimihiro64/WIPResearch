/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
/-
# Local zeta energy packets

This module packages the local zero-energy estimates consumed by the
almost-all square-interval argument.
-/
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zeta23.RvM.LocalCount
import Zeta23.RvM.NcountWindow

/-!
# Multiplicity-weighted local energy of actual zeta zeros

The audited actual local zero count gives a finite zero-mass bound and a
unit-scale additive-energy bound for both signs of the height. Integer-height
endpoints use ceiling bins. A closed length-two near-collision window is
covered by three disjoint half-open unit windows, preserving both endpoints.

The constant is existential: it is the witness of the actual local-count
theorem, not a numerically evaluated zero count. No zero-density or Riemann
Hypothesis assumption occurs in either public conclusion.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

private theorem zero_mult_sum_le_Ncount (A : Finset Complex) {a b : Real}
    (hA : forall rho, (A : Set Complex) rho -> Zeta23.zerosIn a b rho) :
    Finset.sum A (fun rho => (Zeta23.zeroMult rho : Real)) <= (Zeta23.Ncount a b : Real) := by
  classical
  have hn : Finset.sum A Zeta23.zeroMult <= Zeta23.Ncount a b := by
    rw [Zeta23.Ncount, finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite a b)]
    apply Finset.sum_le_sum_of_subset
    intro rho hrho
    exact (Set.Finite.mem_toFinset (Zeta23.zerosIn_finite a b)).mpr (hA rho hrho)
  exact_mod_cast hn

private theorem zero_mass_of_local_count {C T : Real} (hC : 0 <= C)
    (hlocal : forall t : Real, (Zeta23.Ncount t (t+1) : Real) <=
      C*Real.log (abs t+3))
    (hT : 1 <= T) (A : Finset Complex)
    (hA : forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho)
    (hheight : forall rho, (A : Set Complex) rho -> abs rho.im <= T) :
    Finset.sum A (fun rho => (Zeta23.zeroMult rho : Real)) <=
      C*(2*T+3)*Real.log (T+5) := by
  classical
  let R : Nat := Nat.ceil T
  let B : Finset Int := Finset.Icc (-(R : Int)) (R : Int)
  have hceil : T <= (R : Real) := Nat.le_ceil T
  have hceil2 : (R : Real) < T+1 := Nat.ceil_lt_add_one (by linarith : 0 <= T)
  have hmap : forall rho, (A : Set Complex) rho -> (B : Set Int) (Int.ceil rho.im) := by
    intro rho hrho
    have hh := abs_le.mp (hheight rho hrho)
    simp only [B, Finset.coe_Icc]
    change -(R : Int) <= Int.ceil rho.im /\ Int.ceil rho.im <= (R : Int)
    constructor
    next =>
      have hle : -(R : Real) <= (Int.ceil rho.im : Real) := by
        linarith [Int.le_ceil rho.im]
      exact_mod_cast hle
    next =>
      apply Int.ceil_le.mpr
      push_cast
      linarith
  have hrow (r : Int) (hr : (B : Set Int) r) :
      Finset.sum (Finset.filter (fun rho : Complex => Int.ceil rho.im = r) A)
        (fun rho => (Zeta23.zeroMult rho : Real)) <= C*Real.log (T+5) := by
    have hs := zero_mult_sum_le_Ncount
      (Finset.filter (fun rho : Complex => Int.ceil rho.im = r) A)
      (a := (r : Real)-1) (b := (r : Real)) (by
        intro rho hrho
        have hmem := Finset.mem_filter.mp hrho
        have hlo := Int.ceil_lt_add_one rho.im
        have hhi := Int.le_ceil rho.im
        rw [hmem.2] at hlo hhi
        exact And.intro (hA rho hmem.1) (And.intro (by linarith) hhi))
    have hl := hlocal ((r : Real)-1)
    rw [show (r : Real)-1+1 = (r : Real) by ring] at hl
    have hrR : abs (r : Real) <= (R : Real) := by
      have hrB := hr
      simp only [B, Finset.coe_Icc] at hrB
      have hb := And.intro hrB.1 hrB.2
      apply abs_le.mpr
      constructor
      next =>
        exact_mod_cast hb.1
      next =>
        exact_mod_cast hb.2
    have hdist : abs ((r : Real)-1) <= (R : Real)+1 := by
      have hb := abs_le.mp hrR
      apply abs_le.mpr
      constructor <;> linarith [hb.1, hb.2]
    have hlog := Real.log_le_log
      (by linarith [abs_nonneg ((r : Real)-1)] : 0 < abs ((r : Real)-1)+3)
      (by linarith : abs ((r : Real)-1)+3 <= T+5)
    exact (hs.trans hl).trans (mul_le_mul_of_nonneg_left hlog hC)
  have hcardI := Int.card_Icc_of_le (a := -(R : Int)) (b := (R : Int)) (by omega)
  have hcardI2 : (B.card : Int) = 2*(R : Int)+1 := by
    dsimp [B]
    linarith
  have hcard : (B.card : Real) = 2*(R : Real)+1 := by exact_mod_cast hcardI2
  have hlog0 : 0 <= Real.log (T+5) := Real.log_nonneg (by linarith)
  calc
    _ = Finset.sum B (fun r =>
        Finset.sum (Finset.filter (fun rho : Complex => Int.ceil rho.im = r) A)
          (fun rho => (Zeta23.zeroMult rho : Real))) :=
      (Finset.sum_fiberwise_of_maps_to hmap (fun rho => (Zeta23.zeroMult rho : Real))).symm
    _ <= Finset.sum B (fun _ => C*Real.log (T+5)) :=
      Finset.sum_le_sum (fun r hr => hrow r hr)
    _ = (2*(R : Real)+1)*(C*Real.log (T+5)) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ <= (2*T+3)*(C*Real.log (T+5)) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hC hlog0)
    _ = _ := by ring

theorem zeta_zero_mass_log_bound :
    Exists fun C : Real => 1 <= C /\ forall T : Real, 1 <= T ->
      forall A : Finset Complex,
      (forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) ->
      (forall rho, (A : Set Complex) rho -> abs rho.im <= T) ->
      Finset.sum A (fun rho => (Zeta23.zeroMult rho : Real)) <=
        C*(2*T+3)*Real.log (T+5) := by
  obtain h := Zeta23.RvM.zeta_local_zero_count
  refine Exists.intro h.choose (And.intro h.choose_spec.1 ?_)
  intro T hT A hA hh
  exact zero_mass_of_local_count
    (by linarith [h.choose_spec.1] : 0 <= h.choose) h.choose_spec.2 hT A hA hh

theorem zeta_zero_mass_positive_band_log_bound :
    Exists fun C : Real => 1 <= C /\
      forall L U : Real, 0 <= L -> 1 <= U ->
      forall A : Finset Complex,
      (forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) ->
      (forall rho, (A : Set Complex) rho -> L < rho.im /\ rho.im < U) ->
      Finset.sum A (fun rho => (Zeta23.zeroMult rho : Real)) <=
        C*(2*U+3)*Real.log (U+5) := by
  obtain h := zeta_zero_mass_log_bound
  refine Exists.intro h.choose (And.intro h.choose_spec.1 ?_)
  intro L U hL hU A hA hband
  apply h.choose_spec.2 U hU A hA
  intro rho hrho
  have hb := hband rho hrho
  rw [abs_of_pos (lt_of_le_of_lt hL hb.1)]
  linarith [hb.2]


private theorem zero_row_of_local_count {C T c : Real} (hC : 0 <= C)
    (hlocal : forall t : Real, (Zeta23.Ncount t (t+1) : Real) <=
      C*Real.log (abs t+3))
    (_hT : 1 <= T) (hc : abs c <= 3*T) (A : Finset Complex)
    (hA : forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) :
    Finset.sum (Finset.filter (fun rho : Complex => abs (c-rho.im) <= 1) A)
      (fun rho => (Zeta23.zeroMult rho : Real)) <= 3*C*Real.log (3*T+5) := by
  classical
  have hs := zero_mult_sum_le_Ncount
    (Finset.filter (fun rho : Complex => abs (c-rho.im) <= 1) A)
    (a := c-2) (b := c+1) (by
      intro rho hrho
      have hm := Finset.mem_filter.mp hrho
      have hd := abs_le.mp hm.2
      exact And.intro (hA rho hm.1) (And.intro (by linarith) (by linarith)))
  have hl (t : Real) (ht : abs t <= 3*T+2) :
      (Zeta23.Ncount t (t+1) : Real) <= C*Real.log (3*T+5) :=
    (hlocal t).trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)) hC)
  have hcb := abs_le.mp hc
  have h0 := hl (c-2) (by apply abs_le.mpr; constructor <;> linarith)
  have h1 := hl (c-1) (by apply abs_le.mpr; constructor <;> linarith)
  have h2 := hl c (by linarith)
  rw [show c-2+1 = c-1 by ring] at h0
  rw [show c-1+1 = c by ring] at h1
  have hsplit : Zeta23.Ncount (c-2) (c+1) =
      Zeta23.Ncount (c-2) (c-1)+Zeta23.Ncount (c-1) c+Zeta23.Ncount c (c+1) := by
    rw [Zeta23.Ncount_add (a := c-2) (b := c-1) (c := c+1)
      (by linarith) (by linarith),
      Zeta23.Ncount_add (a := c-1) (b := c) (c := c+1)
        (by linarith) (by linarith)]
    omega
  rw [hsplit, Nat.cast_add, Nat.cast_add] at hs
  linarith

private theorem zero_unit_energy_of_local_count {C T : Real} (hC : 0 <= C)
    (hlocal : forall t : Real, (Zeta23.Ncount t (t+1) : Real) <=
      C*Real.log (abs t+3))
    (hT : 1 <= T) (A : Finset Complex)
    (hA : forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho)
    (hheight : forall rho, (A : Set Complex) rho -> abs rho.im <= T) :
    Finset.sum A (fun i => Finset.sum A (fun j => Finset.sum A (fun k =>
      Finset.sum A (fun l =>
        if abs (i.im+j.im-k.im-l.im) <= 1
        then ((Zeta23.zeroMult i : Real)*(Zeta23.zeroMult j : Real))*
          ((Zeta23.zeroMult k : Real)*(Zeta23.zeroMult l : Real)) else 0)))) <=
      (3*C*Real.log (3*T+5))*
        (Finset.sum A (fun rho => (Zeta23.zeroMult rho : Real)))^3 := by
  classical
  let m : Complex -> Real := fun rho => (Zeta23.zeroMult rho : Real)
  let K : Real := 3*C*Real.log (3*T+5)
  have hrow (i : Complex) (hi : (A : Set Complex) i)
      (j : Complex) (hj : (A : Set Complex) j)
      (k : Complex) (hk : (A : Set Complex) k) :
      Finset.sum A (fun l =>
        if abs (i.im+j.im-k.im-l.im) <= 1 then (m i*m j)*(m k*m l) else 0) <=
      (m i*m j*m k)*K := by
    have hiT := abs_le.mp (hheight i hi)
    have hjT := abs_le.mp (hheight j hj)
    have hkT := abs_le.mp (hheight k hk)
    have hc : abs (i.im+j.im-k.im) <= 3*T := by
      apply abs_le.mpr
      constructor <;> linarith [hiT.1, hiT.2, hjT.1, hjT.2, hkT.1, hkT.2]
    have hr := zero_row_of_local_count hC hlocal hT hc A hA
    have heq :
        Finset.sum A (fun l =>
          if abs (i.im+j.im-k.im-l.im) <= 1 then (m i*m j)*(m k*m l) else 0) =
        (m i*m j*m k)*
          Finset.sum (Finset.filter (fun l : Complex => abs (i.im+j.im-k.im-l.im) <= 1) A)
            m := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hd : abs (i.im+j.im-k.im-l.im) <= 1
      next =>
        rw [if_pos hd, if_pos hd]
        ring
      next =>
        simp only [if_neg hd, mul_zero]
    rw [heq]
    exact mul_le_mul_of_nonneg_left hr
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  have hcube :
      Finset.sum A (fun i => Finset.sum A (fun j => Finset.sum A (fun k =>
        m i*m j*m k))) = (Finset.sum A m)^3 := by
    rw [show (Finset.sum A m)^3 = (Finset.sum A m)*((Finset.sum A m)*(Finset.sum A m)) by ring]
    simp_rw [Finset.sum_mul_sum, Finset.mul_sum, mul_assoc]
  calc
    _ <= Finset.sum A (fun i => Finset.sum A (fun j => Finset.sum A (fun k =>
        (m i*m j*m k)*K))) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj =>
        Finset.sum_le_sum (fun k hk => hrow i hi j hj k hk)))
    _ = (Finset.sum A (fun i => Finset.sum A (fun j => Finset.sum A (fun k =>
        m i*m j*m k))))*K := by simp only [<- Finset.sum_mul]
    _ = _ := by rw [hcube]; ring

theorem zeta_unit_energy_log_bound :
    Exists fun C : Real => 1 <= C /\ forall T : Real, 1 <= T ->
      forall A : Finset Complex,
      (forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) ->
      (forall rho, (A : Set Complex) rho -> abs rho.im <= T) ->
      Finset.sum A (fun i => Finset.sum A (fun j => Finset.sum A (fun k =>
        Finset.sum A (fun l =>
          if abs (i.im+j.im-k.im-l.im) <= 1
          then ((Zeta23.zeroMult i : Real)*(Zeta23.zeroMult j : Real))*
            ((Zeta23.zeroMult k : Real)*(Zeta23.zeroMult l : Real)) else 0)))) <=
        375*C^4*T^3*(Real.log (8*T))^4 := by
  obtain h := Zeta23.RvM.zeta_local_zero_count
  let C : Real := h.choose
  have hC1 : 1 <= C := h.choose_spec.1
  have hC : 0 <= C := by linarith
  have hlocal : forall t : Real, (Zeta23.Ncount t (t+1) : Real) <=
      C*Real.log (abs t+3) := h.choose_spec.2
  refine Exists.intro C (And.intro hC1 ?_)
  intro T hT A hA hh
  let M : Real := Finset.sum A (fun rho => (Zeta23.zeroMult rho : Real))
  let L : Real := Real.log (8*T)
  have hT0 : 0 <= T := by linarith
  have hL0 : 0 <= L := Real.log_nonneg (by linarith)
  have hM0 : 0 <= M := Finset.sum_nonneg (fun rho _ => Nat.cast_nonneg _)
  have hm := zero_mass_of_local_count hC hlocal hT A hA hh
  have hlog1 : Real.log (T+5) <= L :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log (3*T+5) <= L :=
    Real.log_le_log (by linarith) (by linarith)
  have hM : M <= 5*C*T*L := by
    calc
      M <= C*(2*T+3)*Real.log (T+5) := hm
      _ <= C*(2*T+3)*L :=
        mul_le_mul_of_nonneg_left hlog1 (mul_nonneg hC (by linarith))
      _ <= C*(5*T)*L :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC) hL0
      _ = _ := by ring
  have hB0 : 0 <= 5*C*T*L :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) hT0) hL0
  have hM2 : M^2 <= (5*C*T*L)^2 := by
    simpa only [pow_two] using mul_le_mul hM hM hM0 hB0
  have hM3 : M^3 <= (5*C*T*L)^3 := by
    calc
      M^3 = M^2*M := by ring
      _ <= (5*C*T*L)^2*(5*C*T*L) :=
        mul_le_mul hM2 hM hM0 (sq_nonneg (5*C*T*L))
      _ = _ := by ring
  have hE := zero_unit_energy_of_local_count hC hlocal hT A hA hh
  calc
    _ <= (3*C*Real.log (3*T+5))*M^3 := hE
    _ <= (3*C*L)*M^3 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog2 (mul_nonneg (by norm_num) hC))
        (pow_nonneg hM0 3)
    _ <= (3*C*L)*(5*C*T*L)^3 :=
      mul_le_mul_of_nonneg_left hM3 (mul_nonneg (mul_nonneg (by norm_num) hC) hL0)
    _ = _ := by ring

end RobinBV.Sieve
