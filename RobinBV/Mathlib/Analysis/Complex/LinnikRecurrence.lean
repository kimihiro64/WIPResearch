/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LinnikFourier

/-!
# Exact branch decomposition in Linnik's mean-value recurrence

This module partitions every power-sum fiber according to whether its first
`k` coordinates collide. It then substitutes that partition into the actual
Vinogradov mean-value count and proves the two branch inequalities used by
Linnik's induction. Thus the collision estimate in `LinnikFourier` has a
complete consumer, while the remaining branch is isolated as the distinct
prefix square sum to be bounded by the local congruence argument.
-/

set_option autoImplicit false

namespace Finset

/-- The part of a power-sum fiber whose first `k` coordinates are distinct. -/
noncomputable def linnikDistinctFiber (k r X : Nat) (hr : 0 < r)
    (h : Fin k -> Nat) : Finset (Fin (k * r) -> Fin X) :=
  (linnikMomentFiber k r X h).filter
    (fun v => Function.Injective (linnikMomentPrefix k r X hr v))

/-- Collision and distinct-prefix fibers are disjoint. -/
theorem disjoint_linnikCollisionFiber_linnikDistinctFiber
    (k r X : Nat) (hr : 0 < r) (h : Fin k -> Nat) :
    Disjoint (linnikCollisionFiber k r X hr h)
      (linnikDistinctFiber k r X hr h) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvCollision hvDistinct
  have hc := (Finset.mem_filter.mp hvCollision).2
  have hd := (Finset.mem_filter.mp hvDistinct).2
  exact hc hd

/-- The cardinality of a power-sum fiber is the sum of its two exact
branches. -/
theorem card_linnikMomentFiber_eq_collision_add_distinct
    (k r X : Nat) (hr : 0 < r) (h : Fin k -> Nat) :
    (linnikMomentFiber k r X h).card =
      (linnikCollisionFiber k r X hr h).card +
        (linnikDistinctFiber k r X hr h).card := by
  classical
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := linnikMomentFiber k r X h)
    (p := fun v => Function.Injective (linnikMomentPrefix k r X hr v))
  simpa only [linnikCollisionFiber, linnikDistinctFiber, Nat.add_comm]
    using hpartition.symm

/-- The complete square sum of the collision branch. -/
noncomputable def linnikCollisionSquareSum
    (k r X : Nat) (hr : 0 < r) : Nat :=
  Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
    (linnikCollisionFiber k r X hr h).card ^ 2)

/-- The complete square sum of the distinct-prefix branch. -/
noncomputable def linnikDistinctSquareSum
    (k r X : Nat) (hr : 0 < r) : Nat :=
  Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
    (linnikDistinctFiber k r X hr h).card ^ 2)

/-- Equality of all first `k` power sums is equality of the corresponding
power-sum data vectors. -/
theorem linnikMomentPowerSumData_eq_iff
    (k m X : Nat) (v w : Fin m -> Fin X) :
    (forall j : Fin k,
      Finset.univ.sum (fun i : Fin m => (v i).val ^ (j.val + 1)) =
        Finset.univ.sum (fun i : Fin m => (w i).val ^ (j.val + 1))) <->
      linnikMomentPowerSumData k m X v =
        linnikMomentPowerSumData k m X w := by
  constructor
  next =>
    intro h
    funext j
    exact h j
  next =>
    intro h j
    exact congrFun h j

/-- The Vinogradov mean value is exactly the sum of the squares of its
attained power-sum fibers. -/
theorem vinogradovMeanValue_eq_sum_sq_linnikMomentFiber
    (k r X : Nat) :
    vinogradovMeanValue k (k * r) X =
      Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
        (linnikMomentFiber k r X h).card ^ 2) := by
  classical
  let A : Finset (Fin (k * r) -> Fin X) := Finset.univ
  let g := linnikMomentPowerSumValue k r X
  have hJ : vinogradovMeanValue k (k * r) X =
      A.sum (fun v =>
        (A.filter (fun w =>
          linnikMomentPowerSumData k (k * r) X w =
            linnikMomentPowerSumData k (k * r) X v)).card) := by
    dsimp [vinogradovMeanValue, A]
    rw [Finset.card_filter, <- Finset.univ_product_univ, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro w hw
    apply if_congr
    constructor
    next =>
      intro h
      exact ((linnikMomentPowerSumData_eq_iff k (k * r) X v w).mp h).symm
    next =>
      intro h
      exact (linnikMomentPowerSumData_eq_iff k (k * r) X v w).mpr h.symm
    next => rfl
    next => rfl
  rw [hJ]
  calc
    A.sum (fun v =>
        (A.filter (fun w =>
          linnikMomentPowerSumData k (k * r) X w =
            linnikMomentPowerSumData k (k * r) X v)).card) =
        A.sum (fun v => (A.filter (fun w => g w = g v)).card) := by
      apply Finset.sum_congr rfl
      intro v hv
      congr 1
      ext w
      simp only [Finset.mem_filter]
      constructor
      next =>
        intro hw
        exact And.intro hw.1 (Subtype.ext hw.2)
      next =>
        intro hw
        exact And.intro hw.1 (congrArg Subtype.val hw.2)
    _ = Finset.univ.sum (fun h : linnikMomentPowerSumRange k r X =>
        (A.filter (fun v => g v = h)).card ^ 2) :=
      (sum_sq_fiber_card_eq_sum_fiber_card A g).symm
    _ = Finset.univ.sum (fun h : linnikMomentPowerSumRange k r X =>
        (linnikMomentFiber k r X h.val).card ^ 2) := by
      apply Finset.sum_congr rfl
      intro h hh
      apply congrArg (fun s : Finset (Fin (k * r) -> Fin X) => s.card ^ 2)
      ext v
      simp only [A, g, Finset.mem_filter, Finset.mem_univ, true_and,
        linnikMomentFiber]
      exact Subtype.ext_iff
    _ = Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
        (linnikMomentFiber k r X h).card ^ 2) :=
      Finset.sum_coe_sort (linnikMomentPowerSumRange k r X)
        (fun h : Fin k -> Nat => (linnikMomentFiber k r X h).card ^ 2)

/-- The square of a two-part cardinality is at most twice the sum of the
two branch squares. -/
theorem add_sq_le_two_mul_add_sq (a b : Nat) :
    (a + b) ^ 2 <= 2 * (a ^ 2 + b ^ 2) := by
  calc
    (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by ring
    _ <= a ^ 2 + b ^ 2 + (a ^ 2 + b ^ 2) := by
      gcongr
      exact two_mul_le_add_sq a b
    _ = 2 * (a ^ 2 + b ^ 2) := by ring

/-- The complete mean value is bounded by the two exact branch square sums. -/
theorem vinogradovMeanValue_le_two_mul_branch_sums
    (k r X : Nat) (hr : 0 < r) :
    vinogradovMeanValue k (k * r) X <=
      2 * (linnikDistinctSquareSum k r X hr +
        linnikCollisionSquareSum k r X hr) := by
  rw [vinogradovMeanValue_eq_sum_sq_linnikMomentFiber]
  unfold linnikDistinctSquareSum linnikCollisionSquareSum
  calc
    _ <= Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
        2 * ((linnikCollisionFiber k r X hr h).card ^ 2 +
          (linnikDistinctFiber k r X hr h).card ^ 2)) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [card_linnikMomentFiber_eq_collision_add_distinct k r X hr h]
      exact add_sq_le_two_mul_add_sq _ _
    _ = 2 * Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
        (linnikCollisionFiber k r X hr h).card ^ 2 +
          (linnikDistinctFiber k r X hr h).card ^ 2) := by
      rw [Finset.mul_sum]
    _ = 2 * (Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
          (linnikCollisionFiber k r X hr h).card ^ 2) +
        Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
          (linnikDistinctFiber k r X hr h).card ^ 2)) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * (Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
          (linnikDistinctFiber k r X hr h).card ^ 2) +
        Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
          (linnikCollisionFiber k r X hr h).card ^ 2)) := by
      rw [Nat.add_comm]

/-- In the distinct-dominant case, the full mean value costs at most four
times the distinct-prefix square sum. -/
theorem vinogradovMeanValue_le_four_mul_distinct_of_collision_lt
    (k r X : Nat) (hr : 0 < r)
    (hdom : linnikCollisionSquareSum k r X hr <
      linnikDistinctSquareSum k r X hr) :
    vinogradovMeanValue k (k * r) X <=
      4 * linnikDistinctSquareSum k r X hr := by
  calc
    _ <= 2 * (linnikDistinctSquareSum k r X hr +
        linnikCollisionSquareSum k r X hr) :=
      vinogradovMeanValue_le_two_mul_branch_sums k r X hr
    _ <= 2 * (linnikDistinctSquareSum k r X hr +
        linnikDistinctSquareSum k r X hr) := by omega
    _ = 4 * linnikDistinctSquareSum k r X hr := by omega

/-- In the collision-dominant case, the full mean value costs at most four
times the collision square sum. -/
theorem vinogradovMeanValue_le_four_mul_collision_of_distinct_le
    (k r X : Nat) (hr : 0 < r)
    (hdom : linnikDistinctSquareSum k r X hr <=
      linnikCollisionSquareSum k r X hr) :
    vinogradovMeanValue k (k * r) X <=
      4 * linnikCollisionSquareSum k r X hr := by
  calc
    _ <= 2 * (linnikDistinctSquareSum k r X hr +
        linnikCollisionSquareSum k r X hr) :=
      vinogradovMeanValue_le_two_mul_branch_sums k r X hr
    _ <= 2 * (linnikCollisionSquareSum k r X hr +
        linnikCollisionSquareSum k r X hr) := by omega
    _ = 4 * linnikCollisionSquareSum k r X hr := by omega

/-- The collision-dominant branch closes completely: combining the branch
dichotomy with the Fourier collision estimate eliminates both the collision
sum and the mean value on the right. -/
theorem vinogradovMeanValue_le_collision_branch_explicit
    (k r X : Nat) (hr : 0 < r) (hm : 2 <= k * r)
    (hdom : linnikDistinctSquareSum k r X hr <=
      linnikCollisionSquareSum k r X hr) :
    vinogradovMeanValue k (k * r) X <=
      4 ^ (k * r) * k ^ (4 * (k * r)) := by
  let m := k * r
  let J := vinogradovMeanValue k (k * r) X
  let S2 := linnikCollisionSquareSum k r X hr
  have hbranch : J <= 4 * S2 := by
    exact vinogradovMeanValue_le_four_mul_collision_of_distinct_le
      k r X hr hdom
  have hcollision : S2 ^ m <=
      k ^ (4 * m) * J ^ (m - 1) := by
    exact pow_sum_sq_linnikCollisionFiber_le_explicit k r X hr hm
  have hpow : J ^ m <=
      (4 ^ m * k ^ (4 * m)) * J ^ (m - 1) := by
    calc
      J ^ m <= (4 * S2) ^ m := Nat.pow_le_pow_left hbranch m
      _ = 4 ^ m * S2 ^ m := by rw [mul_pow]
      _ <= 4 ^ m * (k ^ (4 * m) * J ^ (m - 1)) := by
        exact Nat.mul_le_mul_left _ hcollision
      _ = (4 ^ m * k ^ (4 * m)) * J ^ (m - 1) := by ring
  by_cases hzero : J = 0
  case pos => simp [J, hzero]
  case neg =>
    have hmpos : 0 < m := lt_of_lt_of_le (by omega) hm
    have hfactor : 0 < J ^ (m - 1) :=
      pow_pos (Nat.pos_of_ne_zero hzero) _
    have hsplit : J ^ m = J * J ^ (m - 1) := by
      calc
        J ^ m = J ^ ((m - 1) + 1) := by congr 1 <;> omega
        _ = J ^ (m - 1) * J := by rw [pow_succ]
        _ = J * J ^ (m - 1) := Nat.mul_comm _ _
    have hcancel : J * J ^ (m - 1) <=
        (4 ^ m * k ^ (4 * m)) * J ^ (m - 1) := by
      simpa only [hsplit] using hpow
    exact Nat.le_of_mul_le_mul_right hcancel hfactor

/-- A bound for the distinct-prefix square sum now has a complete consumer:
the full mean value is bounded by the larger of the distinct contribution and
the already closed collision contribution. -/
theorem vinogradovMeanValue_le_max_of_distinctSquareSum_le
    (k r X D : Nat) (hr : 0 < r) (hm : 2 <= k * r)
    (hdistinct : linnikDistinctSquareSum k r X hr <= D) :
    vinogradovMeanValue k (k * r) X <=
      max (4 * D) (4 ^ (k * r) * k ^ (4 * (k * r))) := by
  by_cases hdom : linnikDistinctSquareSum k r X hr <=
      linnikCollisionSquareSum k r X hr
  case pos =>
    exact le_trans
      (vinogradovMeanValue_le_collision_branch_explicit k r X hr hm hdom)
      (Nat.le_max_right _ _)
  case neg =>
    have hlt : linnikCollisionSquareSum k r X hr <
        linnikDistinctSquareSum k r X hr := Nat.lt_of_not_ge hdom
    calc
      vinogradovMeanValue k (k * r) X <=
          4 * linnikDistinctSquareSum k r X hr :=
        vinogradovMeanValue_le_four_mul_distinct_of_collision_lt
          k r X hr hlt
      _ <= 4 * D := Nat.mul_le_mul_left 4 hdistinct
      _ <= max (4 * D) (4 ^ (k * r) * k ^ (4 * (k * r))) :=
        Nat.le_max_left _ _

end Finset
