/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
/-
# Square-interval density estimates

This module proves explicit density identities and bounds for the odd
candidates between consecutive squares.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalIncidenceFloors

/-!
# Positive coefficient of the complete joint square-interval packet

The reciprocal-modulus coefficient retains every small-prime subset and all
three medium-prime incidences. It factors exactly and has a positive lower
bound by half the finite Euler product. No sign bound for the centered moving
interval remainder, or positivity of the actual prime count, is asserted.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- Adding one clock splits the complete pair sum into old pairs and new cross terms. -/
theorem pair_product_sum_insert {a : Nat} {s : Finset Nat}
    (ha : Not (Membership.mem s a)) (f : Nat -> Real) :
    ((insert a s).powersetCard 2).sum (fun t => t.prod f) =
      (s.powersetCard 2).sum (fun t => t.prod f) + f a * s.sum f := by
  have hd : Disjoint (s.powersetCard 2) ((s.powersetCard 1).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro t ht hit
    obtain hsub := (Finset.mem_powersetCard.mp ht).1
    choose u hu using Finset.mem_image.mp hit
    have hat : Membership.mem t a := by rw [<- hu.2]; exact Finset.mem_insert_self _ _
    exact ha (hsub hat)
  have hinj : Set.InjOn (insert a) (s.powersetCard 1 : Set (Finset Nat)) := by
    intro u hu v hv huv
    have hau : Not (Membership.mem u a) := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
    have hav : Not (Membership.mem v a) := fun h => ha ((Finset.mem_powersetCard.mp hv).1 h)
    have he := congrArg (fun t : Finset Nat => t.erase a) huv
    simpa [Finset.erase_insert hau, Finset.erase_insert hav] using he
  rw [Finset.powersetCard_succ_insert ha 1, Finset.sum_union hd, Finset.sum_image hinj]
  congr 1
  rw [Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hap : Not (a = p) := by
    intro h
    subst p
    exact ha hp
  simp [Finset.prod_insert, hap]

/-- The exact second elementary-symmetric sum, including the diagonal subtraction. -/
theorem twice_pair_product_sum (s : Finset Nat) (f : Nat -> Real) :
    2 * (s.powersetCard 2).sum (fun t => t.prod f) =
      (s.sum f)^2 - s.sum (fun p => (f p)^2) := by
  induction s using Finset.induction_on with
  | empty =>
    have he : ({} : Finset Nat).powersetCard 2 = {} :=
      Finset.powersetCard_eq_empty.mpr (by simp)
    simp [he]
  | @insert a s ha ih =>
    rw [pair_product_sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    nlinarith

/-- Complete signed reciprocal subset cancellation into the finite Euler product. -/
theorem signed_reciprocal_product (a : Finset Nat) :
    a.powerset.sum (fun u => (-1 : Real)^u.card * u.prod (fun p => 1 / (p : Real))) =
      a.prod (fun p => 1 - 1 / (p : Real)) := by
  rw [Finset.prod_sub]
  simp

/-- The full reciprocal-modulus coefficient of one incidence, without truncation. -/
noncomputable def squareReciprocalIncidence (a b : Finset Nat) (k : Nat) : Real :=
  a.powerset.sum (fun u => (-1 : Real)^u.card *
    (b.powersetCard k).sum (fun v =>
      1 / (((Union.union u v).prod (fun p => p) : Nat) : Real)))

/-- Disjoint clock sets factor the complete reciprocal-modulus coefficient. -/
theorem squareReciprocalIncidence_factor {a b : Finset Nat}
    (hab : Disjoint a b) (k : Nat) :
    squareReciprocalIncidence a b k =
      a.prod (fun p => 1 - 1 / (p : Real)) *
        (b.powersetCard k).sum (fun v => v.prod (fun p => 1 / (p : Real))) := by
  rw [<- signed_reciprocal_product, Finset.sum_mul]
  unfold squareReciprocalIncidence
  apply Finset.sum_congr rfl
  intro u hu
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have huv : Disjoint u v := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.disjoint_left.mp hab)
      ((Finset.mem_powerset.mp hu) hp) ((Finset.mem_powersetCard.mp hv).1 hq)
  rw [Finset.prod_union huv]
  simp [Nat.cast_prod, one_div, Finset.prod_inv_distrib, mul_comm]

/-- Exact coefficient of the combined weights 3, -3 and 2, not separate estimates. -/
theorem squareJointReciprocal_identity {a b : Finset Nat} (hab : Disjoint a b) :
    3 * squareReciprocalIncidence a b 0 - 3 * squareReciprocalIncidence a b 1 +
      2 * squareReciprocalIncidence a b 2 =
      a.prod (fun p => 1 - 1 / (p : Real)) *
        (3 - 3 * b.sum (fun p => 1 / (p : Real)) +
          (b.sum (fun p => 1 / (p : Real)))^2 -
          b.sum (fun p => (1 / (p : Real))^2)) := by
  rw [squareReciprocalIncidence_factor hab, squareReciprocalIncidence_factor hab,
    squareReciprocalIncidence_factor hab]
  simp only [Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty,
    Finset.powersetCard_one, Finset.sum_map, Finset.prod_singleton, mul_one,
    Function.Embedding.coeFn_mk]
  have hp := twice_pair_product_sum b (fun p => 1 / (p : Real))
  have hm := congrArg (fun x : Real => a.prod (fun p => 1 - 1 / (p : Real)) * x) hp
  nlinarith only [hm]

/-- Elementary telescoping majorant for every finite odd reciprocal-square tail. -/
theorem odd_reciprocal_square_range_bound (N : Nat) :
    (Finset.range N).sum (fun k => 1 / (2 * (k : Real) + 3)^2) <=
      1 / 4 - 1 / (4 * ((N : Real) + 1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hN : (0 : Real) <= N := Nat.cast_nonneg N
    have h1 : (0 : Real) < (N : Real) + 1 := by linarith
    have h2 : (0 : Real) < (N : Real) + 2 := by linarith
    have h3 : (0 : Real) < 2 * (N : Real) + 3 := by linarith
    have hlocal : 1 / (2 * (N : Real) + 3)^2 <=
        1 / (4 * ((N : Real) + 1) * ((N : Real) + 2)) := by
      apply one_div_le_one_div_of_le
      next => positivity
      next => nlinarith
    have htel : (1 : Real) / 4 - 1 / (4 * ((N : Real) + 1)) +
        1 / (4 * ((N : Real) + 1) * ((N : Real) + 2)) =
        1 / 4 - 1 / (4 * ((N : Real) + 2)) := by
      field_simp
      ring
    push_cast
    rw [show (N : Real) + 1 + 1 = (N : Real) + 2 by ring]
    exact (_root_.add_le_add ih hlocal).trans_eq htel

/-- Every finite set of odd integers at least three has reciprocal-square sum below one quarter. -/
theorem odd_reciprocal_square_sum_lt_quarter {b : Finset Nat}
    (hb : forall p, Membership.mem b p -> 3 <= p /\ p % 2 = 1) :
    b.sum (fun p => (1 / (p : Real))^2) < 1 / 4 := by
  let index : Nat -> Nat := fun p => (p - 3) / 2
  let N := b.sup id + 1
  have hrepr : forall p, Membership.mem b p -> p = 2 * index p + 3 := by
    intro p hp
    have h := hb p hp
    dsimp [index]
    omega
  have hi : Set.InjOn index (b : Set Nat) := by
    intro p hp q hq he
    rw [hrepr p hp, hrepr q hq, he]
  have hsub : b.image index <= Finset.range N := by
    intro k hk
    choose p hp using Finset.mem_image.mp hk
    have hbound : p <= b.sup id := Finset.le_sup (f := id) hp.1
    have he := hrepr p hp.1
    apply Finset.mem_range.mpr
    dsimp [N]
    omega
  have heq : b.sum (fun p => (1 / (p : Real))^2) =
      (b.image index).sum (fun k => 1 / (2 * (k : Real) + 3)^2) := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro p hp
    have hcast : (p : Real) = 2 * (index p : Real) + 3 := by exact_mod_cast hrepr p hp
    rw [hcast]
    simp only [div_pow, one_pow]
  rw [heq]
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => (by positivity : (0 : Real) <= 1 / (2 * (k : Real) + 3)^2))
  have hpos : (0 : Real) < 1 / (4 * ((N : Real) + 1)) := by positivity
  have hbound := odd_reciprocal_square_range_bound N
  linarith

/-- The complete joint coefficient exceeds half the small-clock Euler product. -/
theorem squareJointReciprocal_lower {a b : Finset Nat}
    (hab : Disjoint a b)
    (ha : forall p, Membership.mem a p -> 2 <= p)
    (hb : forall p, Membership.mem b p -> 3 <= p /\ p % 2 = 1) :
    a.prod (fun p => 1 - 1 / (p : Real)) / 2 <
      3 * squareReciprocalIncidence a b 0 - 3 * squareReciprocalIncidence a b 1 +
        2 * squareReciprocalIncidence a b 2 := by
  rw [squareJointReciprocal_identity hab]
  have hprod : (0 : Real) < a.prod (fun p => 1 - 1 / (p : Real)) := by
    apply Finset.prod_pos
    intro p hp
    have hpR : (1 : Real) < p := by exact_mod_cast (show 1 < p by have h := ha p hp; omega)
    have hrec : 1 / (p : Real) < 1 := (div_lt_one (by linarith)).mpr hpR
    linarith
  have hq := odd_reciprocal_square_sum_lt_quarter hb
  have hsq := sq_nonneg (b.sum (fun p => 1 / (p : Real)) - 3/2)
  have hpoly : (1 : Real) / 2 <
      3 - 3 * b.sum (fun p => 1 / (p : Real)) +
        (b.sum (fun p => 1 / (p : Real)))^2 - b.sum (fun p => (1 / (p : Real))^2) := by
    nlinarith
  have hm := _root_.mul_lt_mul_of_pos_left hpoly hprod
  simpa only [mul_one_div] using hm

/-- The joint reciprocal coefficient at the actual moving prime cutoffs. -/
noncomputable def squareJointDensity (n : Nat) : Real :=
  3 * squareReciprocalIncidence (squareSmallOddPrimes n) (squareMediumOddPrimes n) 0 -
    3 * squareReciprocalIncidence (squareSmallOddPrimes n) (squareMediumOddPrimes n) 1 +
    2 * squareReciprocalIncidence (squareSmallOddPrimes n) (squareMediumOddPrimes n) 2

/-- The actual cutoff coefficient obeys the strict lower bound for every index. -/
theorem squareJointDensity_lower (n : Nat) :
    (squareSmallOddPrimes n).prod (fun p => 1 - 1 / (p : Real)) / 2 <
      squareJointDensity n := by
  apply squareJointReciprocal_lower
  next =>
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have h1 := (Finset.mem_filter.mp hp).2.2.2
    have h2 := (Finset.mem_filter.mp hq).2.2.2
    omega
  next =>
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1.two_le
  next =>
    intro p hp
    have h := (Finset.mem_filter.mp hp).2
    exact And.intro (by have h2 := h.1.two_le; omega) h.2.1

/-- Exact telescoping product over all consecutive integer clocks. -/
theorem reciprocal_successor_product (N : Nat) :
    (Finset.range N).prod (fun k => 1 - 1 / ((k : Real) + 2)) =
      1 / ((N : Real) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ, ih]
    have h1 : Not ((N : Real) + 1 = 0) := by positivity
    have h2 : Not ((N : Real) + 2 = 0) := by positivity
    push_cast
    rw [show (N : Real) + 1 + 1 = (N : Real) + 2 by ring]
    field_simp
    ring

/-- An elementary Euler-product lower bound requiring no prime-distribution input. -/
theorem finite_reciprocal_product_lower {a : Finset Nat} {N : Nat}
    (ha : forall p, Membership.mem a p -> 2 <= p /\ p <= N + 1) :
    1 / ((N : Real) + 1) <= a.prod (fun p => 1 - 1 / (p : Real)) := by
  let index : Nat -> Nat := fun p => p - 2
  have hrepr : forall p, Membership.mem a p -> p = index p + 2 := by
    intro p hp
    dsimp [index]
    have h := ha p hp
    omega
  have hi : Set.InjOn index (a : Set Nat) := by
    intro p hp q hq he
    rw [hrepr p hp, hrepr q hq, he]
  have hsub : a.image index <= Finset.range N := by
    intro k hk
    choose p hp using Finset.mem_image.mp hk
    have h := ha p hp.1
    have he := hrepr p hp.1
    apply Finset.mem_range.mpr
    omega
  have heq : a.prod (fun p => 1 - 1 / (p : Real)) =
      (a.image index).prod (fun k => 1 - 1 / ((k : Real) + 2)) := by
    rw [Finset.prod_image hi]
    apply Finset.prod_congr rfl
    intro p hp
    have hcast : (p : Real) = (index p : Real) + 2 := by exact_mod_cast hrepr p hp
    rw [hcast]
  rw [heq, <- reciprocal_successor_product N]
  apply Finset.prod_le_prod_of_subset_of_le_one hsub
  next =>
    intro k hk
    have hkR : (0 : Real) <= k := Nat.cast_nonneg k
    have hrec : 1 / ((k : Real) + 2) <= 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  next =>
    intro k hk hnot
    have hrec : (0 : Real) <= 1 / ((k : Real) + 2) := by positivity
    linarith

end Nat.PrimeSieve
