/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import RobinBV.Mathlib.Analysis.Complex.FiniteCircleEnergy

/-!
# Real near-energy and finite color comparison

Flooring transfers real pair and quadruple proximity to the indexed integer
energy from the finite-circle module. The resulting color inequality retains
all mixed quadruples and is consumed by the reflection zero-band energy chain.
-/

set_option autoImplicit false

namespace Real

noncomputable def finiteNearPairCount {I : Type*} (A : Finset I)
    (H : I -> Real) (r : Real) : Real := by
  classical
  exact A.sum (fun i => A.sum (fun j => if abs (H i-H j) <= r then 1 else 0))

noncomputable def finiteNearEnergy {I : Type*} (A : Finset I)
    (H : I -> Real) (r : Real) : Real :=
  finiteNearPairCount (SProd.sprod A A : Finset (Prod I I))
    (fun p => H p.1+H p.2) r

private theorem five_offset_indicator (m : Int) (hm : Membership.mem (Finset.Icc (-2 : Int) 2) m) :
    (Finset.Icc (-2 : Int) 2).sum (fun k => if m = k then (1 : Real) else 0) = 1 := by
  classical
  simp [hm]

private theorem five_offset_card : ((Finset.Icc (-2 : Int) 2).card : Real) = 5 := by
  rw [Int.card_Icc]
  change ((5 : Nat) : Real) = 5
  norm_num

private theorem floor_near_two_offsets (x y : Real) (h : abs (x-y) <= 2) :
    -2 <= Int.floor x-Int.floor y /\ Int.floor x-Int.floor y <= 2 := by
  have hl : (-3 : Real) < ((Int.floor x-Int.floor y : Int) : Real) := by
    push_cast
    linarith [Int.floor_le y, Int.lt_floor_add_one x, (abs_le.mp h).1]
  have hu : (((Int.floor x-Int.floor y : Int) : Real)) < 3 := by
    push_cast
    linarith [Int.floor_le x, Int.lt_floor_add_one y, (abs_le.mp h).2]
  have hlZ : -3 < Int.floor x-Int.floor y := by exact_mod_cast hl
  have huZ : Int.floor x-Int.floor y < 3 := by exact_mod_cast hu
  omega

private theorem floor_pair_near_one_offsets (a b c d : Real) (h : abs ((a+b)-(c+d)) <= 1) :
    -2 <= (Int.floor a+Int.floor b)-(Int.floor c+Int.floor d) /\
    (Int.floor a+Int.floor b)-(Int.floor c+Int.floor d) <= 2 := by
  have hl : (-3 : Real) <
      (((Int.floor a+Int.floor b)-(Int.floor c+Int.floor d) : Int) : Real) := by
    push_cast
    linarith [Int.floor_le c, Int.floor_le d,
      Int.lt_floor_add_one a, Int.lt_floor_add_one b, (abs_le.mp h).1]
  have hu : ((((Int.floor a+Int.floor b)-(Int.floor c+Int.floor d) : Int) : Real)) < 3 := by
    push_cast
    linarith [Int.floor_le a, Int.floor_le b,
      Int.lt_floor_add_one c, Int.lt_floor_add_one d, (abs_le.mp h).2]
  have hlZ : -3 < (Int.floor a+Int.floor b)-(Int.floor c+Int.floor d) := by
    exact_mod_cast hl
  have huZ : (Int.floor a+Int.floor b)-(Int.floor c+Int.floor d) < 3 := by
    exact_mod_cast hu
  omega

private theorem floor_pair_equal_near_two (a b c d : Real)
    (h : (Int.floor a+Int.floor b)-(Int.floor c+Int.floor d) = 0) :
    abs ((a+b)-(c+d)) < 2 := by
  have he : ((Int.floor a : Real)+(Int.floor b : Real))-
      ((Int.floor c : Real)+(Int.floor d : Real)) = 0 := by exact_mod_cast h
  apply abs_lt.mpr
  constructor <;> linarith [Int.floor_le a, Int.floor_le b, Int.floor_le c,
    Int.floor_le d, Int.lt_floor_add_one a, Int.lt_floor_add_one b,
    Int.lt_floor_add_one c, Int.lt_floor_add_one d]

private theorem finite_sum_three_swap {I J K : Type*} (A : Finset I) (B : Finset J) (C : Finset K)
    (f : I -> J -> K -> Real) :
    A.sum (fun i => B.sum (fun j => C.sum (fun k => f i j k))) =
      C.sum (fun k => A.sum (fun i => B.sum (fun j => f i j k))) := by
  calc
    _ = A.sum (fun i => C.sum (fun k => B.sum (fun j => f i j k))) :=
      Finset.sum_congr rfl (fun i hi => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem finiteNearPairCount_le_five_zero {I : Type*}
    (A : Finset I) (H : I -> Real) (q : I -> Int) (r : Real)
    (hq : forall i, Membership.mem A i -> forall j, Membership.mem A j ->
      abs (H i-H j) <= r ->
      Membership.mem (Finset.Icc (-2 : Int) 2) (q i-q j)) :
    finiteNearPairCount A H r <= 5*AddCircle.integerPairCount A q 0 := by
  classical
  let F := Finset.Icc (-2 : Int) 2
  have hpoint (i : I) (hi : Membership.mem A i)
      (j : I) (hj : Membership.mem A j) :
      (if abs (H i-H j) <= r then (1 : Real) else 0) <=
        F.sum (fun k => if q i-q j = k then (1 : Real) else 0) := by
    by_cases h : abs (H i-H j) <= r
    next =>
      rw [if_pos h]
      exact le_of_eq (five_offset_indicator (q i-q j) (hq i hi j hj h)).symm
    next =>
      rw [if_neg h]
      exact Finset.sum_nonneg (fun k hk => by split_ifs <;> norm_num)
  calc
    _ <= A.sum (fun i => A.sum (fun j =>
        F.sum (fun k => if q i-q j = k then (1 : Real) else 0))) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpoint i hi j hj))
    _ = F.sum (fun k => AddCircle.integerPairCount A q k) := by
      unfold AddCircle.integerPairCount
      exact finite_sum_three_swap A A F _
    _ <= F.sum (fun _ => AddCircle.integerPairCount A q 0) :=
      Finset.sum_le_sum (fun k hk => AddCircle.integerPairCount_le_zero A q k)
    _ = 5*AddCircle.integerPairCount A q 0 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      change ((Finset.Icc (-2 : Int) 2).card : Real) * _ = _
      rw [five_offset_card]

theorem finiteNearPairCount_two_le_five_one {I : Type*} (A : Finset I)
    (H : I -> Real) :
    finiteNearPairCount A H 2 <= 5*finiteNearPairCount A H 1 := by
  classical
  have hz : AddCircle.integerPairCount A (fun i => Int.floor (H i)) 0 <=
      finiteNearPairCount A H 1 := by
    unfold AddCircle.integerPairCount finiteNearPairCount
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    by_cases h : Int.floor (H i)-Int.floor (H j) = 0
    next =>
      have hb : abs (H i-H j) <= 1 :=
        (Int.abs_sub_lt_one_of_floor_eq_floor (sub_eq_zero.mp h)).le
      simp only [if_pos h, if_pos hb, le_refl]
    next =>
      rw [if_neg h]
      split_ifs <;> norm_num
  have hn := finiteNearPairCount_le_five_zero A H (fun i => Int.floor (H i)) 2
    (fun i hi j hj h => Finset.mem_Icc.mpr (floor_near_two_offsets (H i) (H j) h))
  exact hn.trans (mul_le_mul_of_nonneg_left hz (by norm_num))

theorem finiteNearEnergy_two_le_five_one {I : Type*} (A : Finset I)
    (H : I -> Real) :
    finiteNearEnergy A H 2 <= 5*finiteNearEnergy A H 1 :=
  finiteNearPairCount_two_le_five_one
    (SProd.sprod A A : Finset (Prod I I)) (fun p => H p.1+H p.2)

theorem finiteNearEnergy_one_le_five_integer {I : Type*} (A : Finset I)
    (H : I -> Real) :
    finiteNearEnergy A H 1 <=
      5*AddCircle.integerEnergy A (fun i => Int.floor (H i)) := by
  apply finiteNearPairCount_le_five_zero
    (SProd.sprod A A : Finset (Prod I I)) (fun p => H p.1+H p.2)
    (fun p => Int.floor (H p.1)+Int.floor (H p.2)) 1
  intro p hp q hq h
  exact Finset.mem_Icc.mpr
    (floor_pair_near_one_offsets (H p.1) (H p.2) (H q.1) (H q.2) h)

theorem integerEnergy_floor_le_near_two {I : Type*} (A : Finset I)
    (H : I -> Real) :
    AddCircle.integerEnergy A (fun i => Int.floor (H i)) <=
      finiteNearEnergy A H 2 := by
  classical
  unfold AddCircle.integerEnergy AddCircle.integerPairCount
    finiteNearEnergy finiteNearPairCount
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  by_cases h : (Int.floor (H p.1)+Int.floor (H p.2))-
      (Int.floor (H q.1)+Int.floor (H q.2)) = 0
  next =>
    have hb : abs ((H p.1+H p.2)-(H q.1+H q.2)) <= 2 :=
      (floor_pair_equal_near_two (H p.1) (H p.2) (H q.1) (H q.2) h).le
    simp only [if_pos h, if_pos hb, le_refl]
  next =>
    rw [if_neg h]
    split_ifs <;> norm_num

theorem finiteNearEnergy_color_le {I J : Type*} [DecidableEq J]
    (A : Finset I) (C : Finset J) (H : I -> Real) (color : I -> J)
    (hc : forall i, Membership.mem A i -> Membership.mem C (color i)) :
    finiteNearEnergy A H 1 <= 25*(C.card : Real)^3 *
      C.sum (fun c => finiteNearEnergy (A.filter (fun i => color i = c)) H 1) := by
  classical
  have hcolor := AddCircle.integerEnergy_color_le A C
    (fun i => Int.floor (H i)) color hc
  have hband (c : J) :
      AddCircle.integerEnergy (A.filter (fun i => color i = c))
        (fun i => Int.floor (H i)) <=
      5*finiteNearEnergy (A.filter (fun i => color i = c)) H 1 :=
    (integerEnergy_floor_le_near_two _ H).trans (finiteNearEnergy_two_le_five_one _ H)
  calc
    _ <= 5*AddCircle.integerEnergy A (fun i => Int.floor (H i)) :=
      finiteNearEnergy_one_le_five_integer A H
    _ <= 5*((C.card : Real)^3*C.sum (fun c =>
        AddCircle.integerEnergy (A.filter (fun i => color i = c))
          (fun i => Int.floor (H i)))) :=
      mul_le_mul_of_nonneg_left hcolor (by norm_num)
    _ <= 5*((C.card : Real)^3*C.sum (fun c =>
        5*finiteNearEnergy (A.filter (fun i => color i = c)) H 1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c hcc => hband c))
          (by positivity)) (by norm_num)
    _ = _ := by
      rw [<- Finset.mul_sum]
      ring

end Real
