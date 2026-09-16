/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalModulusLedger

/-!
# Signed geometric loss in two adjacent square intervals

Keep all admissible odd quadratic factorizations outside the first strip.
An old-window cell loses at most three, whereas a new-window cell loses at
most six. The resulting exact geometric budget uniformly improves the shared
gap-capacity bound, while retaining every other part of the joint packet.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- Every odd large modulus outside the first strip that can meet either square window. -/
noncomputable def squareGeometricLargeModuli (n : Nat) : Finset Nat :=
  (Finset.Icc (n+2) ((n+2)*(n+2)-1)).filter (fun d =>
    d % 2 = 1 /\ 2*n < (d-(n+1))*(d-(n+1)))

/-- All admissible near-gap odd factor pairs, without a prime-factor restriction. -/
noncomputable def squareGeometricNearCells (n K : Nat) : Finset (Prod Nat Nat) :=
  nearGapCofactorCells n K (squareGeometricLargeModuli n)

/-- The old-window part of the complete geometric near-gap set. -/
noncomputable def squareGeometricOldNearCells (n K : Nat) : Finset (Prod Nat Nat) :=
  (squareGeometricNearCells n K).filter (fun x => x.2*x.1 <= n*n+2*n)

/-- The sharp coefficient-only loss: three in the old window and six in the new. -/
def squareNearCellLoss (n : Nat) (x : Prod Nat Nat) : Int :=
  if x.2*x.1 <= n*n+2*n then 3 else 6

/-- The geometric loss is nonnegative on every pair. -/
theorem squareNearCellLoss_nonneg (n : Nat) (x : Prod Nat Nat) :
    0 <= squareNearCellLoss n x := by
  unfold squareNearCellLoss
  split_ifs <;> norm_num

/-- Every geometric modulus has the exact large, odd and outside-strip data. -/
theorem squareGeometricLargeModuli_data {n d : Nat}
    (hd : Membership.mem (squareGeometricLargeModuli n) d) :
    n+1 < d /\ d % 2 = 1 /\ 2*n < (d-(n+1))*(d-(n+1)) := by
  have h := Finset.mem_filter.mp hd
  have hi := Finset.mem_Icc.mp h.1
  exact And.intro (by omega) h.2

/-- Every live supported cell embeds into the full prime-independent geometric set. -/
theorem nearGapCofactorCells_subset_geometry (n K : Nat) {s : Finset Nat}
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hout : forall d, Membership.mem s d -> 2*n < (d-(n+1))*(d-(n+1))) :
    nearGapCofactorCells n K s <= squareGeometricNearCells n K := by
  intro x hx
  have h := nearGapCofactorCells_data hs hx
  have hr : 1 <= x.1 := by omega
  have hmul : x.2 <= x.2*x.1 := by
    simpa using Nat.mul_le_mul_left x.2 hr
  have hd : Membership.mem (squareGeometricLargeModuli n) x.2 := by
    apply Finset.mem_filter.mpr
    exact And.intro (Finset.mem_Icc.mpr (And.intro (by have := hs x.2 h.1; omega) (by omega)))
      (And.intro (hs x.2 h.1).2 (hout x.2 h.1))
  have hx' := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  exact And.intro (Finset.mem_product.mpr
    (And.intro (Finset.mem_product.mp hx'.1).1 hd)) hx'.2

/-- The old and new interval signs give different worst-case coefficient losses. -/
theorem squarePairedCofactorKernel_ge_neg_loss (n d r : Nat) {c : Int}
    (hc : (-3 : Int) <= c /\ c <= 3) :
    -squareNearCellLoss n (r,d) <= c*squarePairedCofactorKernel n d r := by
  unfold squareNearCellLoss squarePairedCofactorKernel
  dsimp
  by_cases hold : r%2 = 1 /\ n*n < d*r /\ d*r <= n*n+2*n
  next =>
    have hnew : Not (r%2 = 1 /\ (n+1)*(n+1) < d*r /\
        d*r <= (n+1)*(n+1)+2*(n+1)) := by
      intro h
      nlinarith [hold.2.2, h.2.1]
    simp only [if_pos hold, if_neg hnew, if_pos hold.2.2]
    omega
  next =>
    by_cases hnew : r%2 = 1 /\ (n+1)*(n+1) < d*r /\
        d*r <= (n+1)*(n+1)+2*(n+1)
    next =>
      have hhigh : Not (d*r <= n*n+2*n) := by nlinarith [hnew.2.1]
      simp only [if_neg hold, if_pos hnew, if_neg hhigh]
      omega
    next =>
      simp only [if_neg hold, if_neg hnew]
      split_ifs <;> omega

/-- The full geometric loss is six per cell, with three returned for every old cell. -/
theorem sum_squareGeometricNearCellLoss (n K : Nat) :
    (squareGeometricNearCells n K).sum (squareNearCellLoss n) =
      6*((squareGeometricNearCells n K).card : Int) -
        3*((squareGeometricOldNearCells n K).card : Int) := by
  unfold squareGeometricOldNearCells
  calc
    _ = (squareGeometricNearCells n K).sum (fun x =>
        (6 : Int)-3*(if x.2*x.1 <= n*n+2*n then (1 : Int) else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [squareNearCellLoss]
      split_ifs <;> norm_num
    _ = _ := by
      rw [Finset.sum_sub_distrib, <- Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_boole]
      ring

/-- The whole supported near packet is bounded by its complete geometric loss. -/
theorem nearGapJointPacket_signed_geometry_lower (n K : Nat) {s : Finset Nat}
    (c : Nat -> Int)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hout : forall d, Membership.mem s d -> 2*n < (d-(n+1))*(d-(n+1)))
    (hc : forall d, Membership.mem s d -> (-3 : Int) <= c d /\ c d <= 3) :
    -(6 : Int)*((squareGeometricNearCells n K).card : Int) +
      3*((squareGeometricOldNearCells n K).card : Int) <= nearGapJointPacket n K s c := by
  have hp : -(Finset.sum (nearGapCofactorCells n K s) (squareNearCellLoss n)) <=
      nearGapJointPacket n K s c := by
    rw [<- Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro x hx
    exact squarePairedCofactorKernel_ge_neg_loss n x.2 x.1 (hc x.2 (nearGapCofactorCells_data hs hx).1)
  have hsum : Finset.sum (nearGapCofactorCells n K s) (squareNearCellLoss n) <=
      Finset.sum (squareGeometricNearCells n K) (squareNearCellLoss n) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (nearGapCofactorCells_subset_geometry n K hs hout)
    intro x hx hnot
    exact squareNearCellLoss_nonneg n x
  rw [sum_squareGeometricNearCellLoss] at hsum
  linarith only [hp, hsum]

/-- The exact geometric set obeys the previously proved shared unused-gap capacity. -/
theorem card_squareGeometricNearCells_le (n K J : Nat)
    (hJ : (J+1)*(J+1) <= 2*n) :
    (squareGeometricNearCells n K).card <= K-J := by
  apply card_nearGap_after_firstStrip_le n K J
  next =>
    intro d hd
    have h := squareGeometricLargeModuli_data hd
    exact And.intro h.1 h.2.1
  next => exact fun d hd => (squareGeometricLargeModuli_data hd).2.2
  next => exact hJ

/-- The signed geometry bound applies to the actual arithmetic modulus coefficients. -/
theorem actual_nearGap_signed_geometry_lower (n K : Nat) (a b : Finset Nat)
    (ha : forall p, Membership.mem a p -> p % 2 = 1)
    (hb : forall p, Membership.mem b p -> p % 2 = 1) :
    -(6 : Int)*((squareGeometricNearCells n K).card : Int) +
      3*((squareGeometricOldNearCells n K).card : Int) <=
      nearGapJointPacket n K (squareRemainingLargeModuli n a b) (squareModulusCoefficient a b) := by
  apply nearGapJointPacket_signed_geometry_lower
  next =>
    intro d hd
    have h := Finset.mem_filter.mp hd
    exact And.intro h.2.1 (squareModulusSupport_odd ha hb h.1)
  next => exact fun d hd => (Finset.mem_filter.mp hd).2.2
  next => exact fun d hd => squareModulusCoefficient_bounds a b d

/-- The full joint packet retains the low and far sums with the improved geometric loss. -/
theorem squareJointPacket_signed_gap_lower {n : Nat} (hn : 2 <= n) (K : Nat)
    {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1)
    (hab : Disjoint a b) :
    squareFirstStripPacket n a b + squareLowModulusPacket n a b +
      farGapJointPacket n K (squareRemainingLargeModuli n a b) (squareModulusCoefficient a b) -
      6*((squareGeometricNearCells n K).card : Int) +
      3*((squareGeometricOldNearCells n K).card : Int) <=
      2*squareJointPacket (n+1) a b - squareJointPacket n a b := by
  rw [squareJointPacket_gap_ledger hn K ha hb hab]
  have h := actual_nearGap_signed_geometry_lower n K a b
    (fun p hp => (ha p hp).2) (fun p hp => (hb p hp).2)
  linarith only [h]

/-- The new signed geometry lower bound is uniformly at least the earlier capacity bound. -/
theorem signed_geometry_bound_dominates_gap_capacity (n K J : Nat)
    (hJ : (J+1)*(J+1) <= 2*n) :
    -(6 : Int)*((K-J : Nat) : Int) <=
      -(6 : Int)*((squareGeometricNearCells n K).card : Int) +
        3*((squareGeometricOldNearCells n K).card : Int) := by
  have h : ((squareGeometricNearCells n K).card : Int) <= ((K-J : Nat) : Int) := by
    exact_mod_cast card_squareGeometricNearCells_le n K J hJ
  have h0 : (0 : Int) <= ((squareGeometricOldNearCells n K).card : Int) := by positivity
  linarith only [h, h0]

/-- At a square-root-sized gap cutoff, every actual center lies in five explicit families. -/
theorem squareGeometricNearCells_five_centers {n K : Nat}
    (hK : K*K <= 8*n) {x : Prod Nat Nat}
    (hx : Membership.mem (squareGeometricNearCells n K) x) :
    n+1 <= x.1+(x.2-x.1)/2 /\ x.1+(x.2-x.1)/2 <= n+5 := by
  have hs : forall d, Membership.mem (squareGeometricLargeModuli n) d ->
      n+1 < d /\ d % 2 = 1 := by
    intro d hd
    have h := squareGeometricLargeModuli_data hd
    exact And.intro h.1 h.2.1
  have h := nearGapCofactorCells_data hs hx
  let k := (x.2-x.1)/2
  have hk : k <= K := h.2.2.2.2.1
  have hd : x.2 = x.1+2*k := h.2.2.1
  have he : x.2*x.1+k*k = (x.1+k)*(x.1+k) := by rw [hd]; ring
  have hk2 := Nat.mul_le_mul hk hk
  change n+1 <= x.1+k /\ x.1+k <= n+5
  constructor
  next =>
    by_contra hnot
    have ha : x.1+k <= n := by omega
    have ha2 := Nat.mul_le_mul ha ha
    nlinarith only [ha2, he, h.2.2.2.2.2.1]
  next =>
    by_contra hnot
    have ha : n+6 <= x.1+k := by omega
    have ha2 := Nat.mul_le_mul ha ha
    nlinarith only [ha2, he, hk2, hK, h.2.2.2.2.2.2]

end Nat.PrimeSieve
