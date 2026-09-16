/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.OwnerModuli
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalJointRemainder

/-!
# Bounded coefficients of the complete square-interval packet

Unique prime factorization prevents coefficient accumulation when all signed
small-prime subsets and three medium-prime incidences are grouped by modulus.
The exact packet has coefficients between minus three and three, with neither
large moduli nor zero-count centered terms silently removed.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- The complete signed small-prime exclusion with all three retained incidences. -/
def squareSubsetWeight (u v : Finset Nat) : Int :=
  (-1 : Int)^u.card *
    (if v.card = 0 then 3 else if v.card = 1 then -3 else if v.card = 2 then 2 else 0)

/-- The unique coefficient attached to a product modulus; no branch multiplicity is assumed. -/
noncomputable def squareModulusCoefficient (a b : Finset Nat) (d : Nat) : Int :=
  squareSubsetWeight (Inter.inter d.primeFactors a) (Inter.inter d.primeFactors b)

/-- Every individual full-incidence coefficient lies between minus three and three. -/
theorem squareSubsetWeight_bounds (u v : Finset Nat) :
    (-3 : Int) <= squareSubsetWeight u v /\ squareSubsetWeight u v <= 3 := by
  have hsign : (-1 : Int)^u.card = 1 \/ (-1 : Int)^u.card = -1 :=
    neg_one_pow_eq_or Int _
  unfold squareSubsetWeight
  rcases hsign with h | h <;> rw [h] <;> split_ifs <;> norm_num

/-- The exact arithmetic coefficient satisfies the local budget required by gap estimates. -/
theorem squareModulusCoefficient_bounds (a b : Finset Nat) (d : Nat) :
    (-3 : Int) <= squareModulusCoefficient a b d /\
      squareModulusCoefficient a b d <= 3 := squareSubsetWeight_bounds _ _

/-- Intersecting a union with disjoint ambient sets recovers both selected subsets. -/
theorem disjoint_subsets_union_inter {a b u v : Finset Nat}
    (hab : Disjoint a b) (hu : forall p, Membership.mem u p -> Membership.mem a p)
    (hv : forall p, Membership.mem v p -> Membership.mem b p) :
    Inter.inter (Union.union u v) a = u /\ Inter.inter (Union.union u v) b = v := by
  constructor
  next =>
    ext p
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    next =>
      intro h
      rcases h.1 with hpu | hpv
      next => exact hpu
      next => exact False.elim ((Finset.disjoint_left.mp hab) h.2 (hv p hpv))
    next => exact fun h => And.intro (Or.inl h) (hu p h)
  next =>
    ext p
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    next =>
      intro h
      rcases h.1 with hpu | hpv
      next => exact False.elim ((Finset.disjoint_left.mp hab) (hu p hpu) h.2)
      next => exact hpv
    next => exact fun h => And.intro (Or.inr h) (hv p h)

/-- Prime factorization recovers the exact signed coefficient of each subset branch. -/
theorem squareModulusCoefficient_prod {a b u v : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p)
    (hab : Disjoint a b) (hu : forall p, Membership.mem u p -> Membership.mem a p)
    (hv : forall p, Membership.mem v p -> Membership.mem b p) :
    squareModulusCoefficient a b ((Union.union u v).prod (fun p => p)) =
      squareSubsetWeight u v := by
  have hp : forall p, Membership.mem (Union.union u v) p -> Nat.Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    next => exact ha p (hu p h)
    next => exact hb p (hv p h)
  unfold squareModulusCoefficient
  rw [Nat.primeFactors_prod hp, (disjoint_subsets_union_inter hab hu hv).1,
    (disjoint_subsets_union_inter hab hu hv).2]

/-- Distinct disjoint prime-subset pairs cannot accumulate at the same product modulus. -/
theorem disjoint_prime_subset_product_injOn {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p) (hab : Disjoint a b) :
    Set.InjOn (fun x : Prod (Finset Nat) (Finset Nat) =>
      (Union.union x.1 x.2).prod (fun p => p)) (a.powerset.product b.powerset) := by
  intro x hx y hy he
  have hxu : forall p, Membership.mem x.1 p -> Membership.mem a p :=
    fun p hp => (Finset.mem_powerset.mp (Finset.mem_product.mp hx).1) hp
  have hxv : forall p, Membership.mem x.2 p -> Membership.mem b p :=
    fun p hp => (Finset.mem_powerset.mp (Finset.mem_product.mp hx).2) hp
  have hyu : forall p, Membership.mem y.1 p -> Membership.mem a p :=
    fun p hp => (Finset.mem_powerset.mp (Finset.mem_product.mp hy).1) hp
  have hyv : forall p, Membership.mem y.2 p -> Membership.mem b p :=
    fun p hp => (Finset.mem_powerset.mp (Finset.mem_product.mp hy).2) hp
  have hp {u v : Finset Nat} (hu : forall p, Membership.mem u p -> Membership.mem a p)
      (hv : forall p, Membership.mem v p -> Membership.mem b p) :
      forall p, Membership.mem (Union.union u v) p -> Nat.Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    next => exact ha p (hu p h)
    next => exact hb p (hv p h)
  have hsets := congrArg Nat.primeFactors he
  rw [Nat.primeFactors_prod (hp hxu hxv), Nat.primeFactors_prod (hp hyu hyv)] at hsets
  apply Prod.ext
  next =>
    have hi := congrArg (fun t : Finset Nat => Inter.inter t a) hsets
    simpa only [(disjoint_subsets_union_inter hab hxu hxv).1,
      (disjoint_subsets_union_inter hab hyu hyv).1] using hi
  next =>
    have hi := congrArg (fun t : Finset Nat => Inter.inter t b) hsets
    simpa only [(disjoint_subsets_union_inter hab hxu hxv).2,
      (disjoint_subsets_union_inter hab hyu hyv).2] using hi

/-- All product moduli in the complete finite expansion, including zero-weight terms. -/
noncomputable def squareModulusSupport (a b : Finset Nat) : Finset Nat :=
  (a.powerset.product b.powerset).image (fun x => (Union.union x.1 x.2).prod (fun p => p))

/-- Exact coefficient aggregation, preserving the entire finite subset expansion. -/
theorem squareModulus_sum_eq_subsets {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p) (hab : Disjoint a b)
    (f : Nat -> Int) :
    (squareModulusSupport a b).sum (fun d => squareModulusCoefficient a b d * f d) =
      a.powerset.sum (fun u => b.powerset.sum (fun v =>
        squareSubsetWeight u v * f ((Union.union u v).prod (fun p => p)))) := by
  unfold squareModulusSupport
  rw [Finset.sum_image (disjoint_prime_subset_product_injOn ha hb hab)]
  rw [Finset.sum_finset_product (a.powerset.product b.powerset)
    a.powerset (fun _ => b.powerset) (fun _ => Finset.mem_product)]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [squareModulusCoefficient_prod ha hb hab (fun p hp => (Finset.mem_powerset.mp hu) hp)
    (fun p hp => (Finset.mem_powerset.mp hv) hp)]

/-- The bounded branch coefficient is exactly the original three-incidence combination. -/
theorem squareSubsetWeight_floor_sum (x : Nat) (a b : Finset Nat) :
    a.powerset.sum (fun u => b.powerset.sum (fun v =>
      squareSubsetWeight u v * oddSquareFloor x ((Union.union u v).prod (fun p => p)))) =
    3 * squareFrozenFloorIncidence x a b 0 - 3 * squareFrozenFloorIncidence x a b 1 +
      2 * squareFrozenFloorIncidence x a b 2 := by
  unfold squareFrozenFloorIncidence
  simp_rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
  simp only [Finset.mul_sum, <- Finset.sum_sub_distrib, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  unfold squareSubsetWeight
  split_ifs <;> first | omega | ring

/-- The actual sieved joint packet equals the complete bounded-coefficient modulus sum. -/
theorem squareJointPacket_eq_modulus_sum (x : Nat) {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1)
    (hab : Disjoint a b) :
    squareJointPacket x a b = (squareModulusSupport a b).sum
      (fun d => squareModulusCoefficient a b d * oddSquareFloor x d) := by
  rw [squareModulus_sum_eq_subsets (fun p hp => (ha p hp).1)
    (fun p hp => (hb p hp).1) hab, squareSubsetWeight_floor_sum,
    squareJointPacket_eq_frozenFloors x ha hb]

/-- Supported moduli in the first quadratic strip, with the exact square cutoff. -/
noncomputable def squareFirstStrip (n : Nat) (s : Finset Nat) : Finset Nat :=
  s.filter (fun d => n+1 < d /\ (d-(n+1))*(d-(n+1)) <= 2*n)

/-- The full signed first-strip packet cancels to coefficients and one boundary correction. -/
theorem sum_first_quadratic_strip {n : Nat} (hn : 2 <= n) (s : Finset Nat)
    (c : Nat -> Int) (hs : forall d, Membership.mem s d -> d % 2 = 1) :
    (squareFirstStrip n s).sum (fun d =>
      c d * (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)) =
    (squareFirstStrip n s).sum c -
      2 * (if Membership.mem (squareFirstStrip n s) (n+2) then c (n+2) else 0) := by
  have he (d : Nat) (hd : Membership.mem (squareFirstStrip n s) d) :
      2 * oddSquareFloor (n+1) d - oddSquareFloor n d =
        1 - 2 * (if d = n+2 then (1 : Int) else 0) := by
    have hm := Finset.mem_filter.mp hd
    have hdk : n+1+(d-(n+1)) = d := by omega
    have h := paired_first_quadratic_layer hn (by omega : 1 <= d-(n+1)) hm.2.2
      (by rw [hdk]; exact hs d hm.1)
    rw [hdk] at h
    rw [h]
    split_ifs <;> omega
  calc
    _ = (squareFirstStrip n s).sum (fun d => c d - 2 * (if d = n+2 then c d else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [he d hd]
      split_ifs <;> ring
    _ = _ := by simp [Finset.sum_sub_distrib]

/-- The two-interval packet has the same bounded coefficients in both quadratic windows. -/
theorem squareJointPacket_paired_modulus_sum (n : Nat) {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1)
    (hab : Disjoint a b) :
    2 * squareJointPacket (n+1) a b - squareJointPacket n a b =
      (squareModulusSupport a b).sum (fun d => squareModulusCoefficient a b d *
        (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)) := by
  rw [squareJointPacket_eq_modulus_sum (n+1) ha hb hab,
    squareJointPacket_eq_modulus_sum n ha hb hab]
  simp only [Finset.mul_sum, <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Every modulus in the complete odd-clock expansion is odd. -/
theorem squareModulusSupport_odd {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> p % 2 = 1)
    (hb : forall p, Membership.mem b p -> p % 2 = 1)
    {d : Nat} (hd : Membership.mem (squareModulusSupport a b) d) : d % 2 = 1 := by
  choose x hx using Finset.mem_image.mp hd
  rw [<- hx.2]
  apply prod_odd_mod_two
  intro p hp
  rcases Finset.mem_union.mp hp with h | h
  next => exact ha p ((Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).1) h)
  next => exact hb p ((Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).2) h)

/-- Exact first-strip cancellation inside the whole joint packet, retaining every other modulus. -/
theorem squareJointPacket_firstStrip_ledger {n : Nat} (hn : 2 <= n)
    {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1)
    (hab : Disjoint a b) :
    2 * squareJointPacket (n+1) a b - squareJointPacket n a b =
      (squareFirstStrip n (squareModulusSupport a b)).sum (squareModulusCoefficient a b) -
      2 * (if Membership.mem (squareFirstStrip n (squareModulusSupport a b)) (n+2)
        then squareModulusCoefficient a b (n+2) else 0) +
      ((squareModulusSupport a b).filter (fun d =>
        Not (n+1 < d /\ (d-(n+1))*(d-(n+1)) <= 2*n))).sum
          (fun d => squareModulusCoefficient a b d *
            (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)) := by
  rw [squareJointPacket_paired_modulus_sum n ha hb hab]
  have hsplit := Finset.sum_filter_add_sum_filter_not (squareModulusSupport a b)
    (fun d => n+1 < d /\ (d-(n+1))*(d-(n+1)) <= 2*n)
    (fun d => squareModulusCoefficient a b d *
      (2 * oddSquareFloor (n+1) d - oddSquareFloor n d))
  rw [<- hsplit, show (squareModulusSupport a b).filter
    (fun d => n+1 < d /\ (d-(n+1))*(d-(n+1)) <= 2*n) =
      squareFirstStrip n (squareModulusSupport a b) from rfl,
    sum_first_quadratic_strip hn _ _ (fun d hd => squareModulusSupport_odd
      (fun p hp => (ha p hp).2) (fun p hp => (hb p hp).2) hd)]

/-- The common quadratic upper window forces every sufficiently small gap into the first strip. -/
theorem small_halfGap_forces_firstStrip {n d r k : Nat}
    (hd : n+1 < d) (he : d = r+2*k)
    (hupper : d*r < (n+2)*(n+2)) (hk : (k+1)*(k+1) <= 2*n) :
    (d-(n+1))*(d-(n+1)) <= 2*n := by
  have hcenter : r+k <= n+2 := by
    by_contra h
    have hge : n+3 <= r+k := by omega
    have hsq := Nat.mul_le_mul hge hge
    nlinarith
  have hdiff : d-(n+1) <= k+1 := by omega
  exact le_trans (Nat.mul_le_mul hdiff hdiff) hk

/-- Removing the first strip also removes all half-gaps up to J; they cannot be charged again. -/
theorem card_nearGap_after_firstStrip_le (n K J : Nat) {s : Finset Nat}
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hout : forall d, Membership.mem s d -> 2*n < (d-(n+1))*(d-(n+1)))
    (hJ : (J+1)*(J+1) <= 2*n) :
    (nearGapCofactorCells n K s).card <= K-J := by
  have hcard : (nearGapCofactorCells n K s).card <= (Finset.Icc (J+1) K).card := by
    apply Finset.card_le_card_of_injOn (fun x : Prod Nat Nat => (x.2-x.1)/2)
    next =>
      intro x hx
      have h := nearGapCofactorCells_data hs hx
      have hlow : J < (x.2-x.1)/2 := by
        by_contra hbad
        have hle : (x.2-x.1)/2+1 <= J+1 := by omega
        have hsq := le_trans (Nat.mul_le_mul hle hle) hJ
        have hstrip := small_halfGap_forces_firstStrip (hs x.2 h.1).1
          h.2.2.1 h.2.2.2.2.2.2 hsq
        have hout' := hout x.2 h.1
        omega
      exact Finset.mem_Icc.mpr (And.intro
        (show J+1 <= (x.2-x.1)/2 by omega) h.2.2.2.2.1)
    next => exact nearGapCofactorCells_halfGap_injOn n K hs
  simpa using hcard

/-- The remaining shared near-gap packet has loss at most six times its unspent gap capacity. -/
theorem nearGapJointPacket_after_firstStrip_lower (n K J : Nat) {s : Finset Nat}
    (c : Nat -> Int)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hc : forall d, Membership.mem s d -> (-3 : Int) <= c d /\ c d <= 3)
    (hout : forall d, Membership.mem s d -> 2*n < (d-(n+1))*(d-(n+1)))
    (hJ : (J+1)*(J+1) <= 2*n) :
    -(6 : Int)*((K-J : Nat) : Int) <= nearGapJointPacket n K s c := by
  have hsum : -(6 : Int)*((nearGapCofactorCells n K s).card : Int) <=
      nearGapJointPacket n K s c := by
    calc
      _ = (nearGapCofactorCells n K s).sum (fun _ => (-6 : Int)) := by
        simp [Finset.sum_const, mul_comm]
      _ <= _ := by
        apply Finset.sum_le_sum
        intro x hx
        have hc' := hc x.2 (nearGapCofactorCells_data hs hx).1
        have hk := squarePairedCofactorKernel_bounds n x.2 x.1
        by_cases hpos : 0 <= c x.2
        next =>
          have hprod := _root_.mul_le_mul_of_nonneg_left hk.1 hpos
          nlinarith
        next =>
          have hneg : c x.2 <= 0 := by omega
          have hprod := _root_.mul_le_mul_of_nonpos_left hk.2 hneg
          nlinarith
  have hcard : ((nearGapCofactorCells n K s).card : Int) <= (K-J : Nat) := by
    exact_mod_cast card_nearGap_after_firstStrip_le n K J hs hout hJ
  nlinarith

/-- All large supported moduli outside the exactly cancelled first strip. -/
noncomputable def squareRemainingLargeModuli (n : Nat) (a b : Finset Nat) : Finset Nat :=
  (squareModulusSupport a b).filter (fun d =>
    n+1 < d /\ 2*n < (d-(n+1))*(d-(n+1)))

/-- The improved residual-gap loss bound applies to the actual arithmetic coefficients. -/
theorem actual_nearGap_after_firstStrip_lower (n K J : Nat) (a b : Finset Nat)
    (ha : forall p, Membership.mem a p -> p % 2 = 1)
    (hb : forall p, Membership.mem b p -> p % 2 = 1)
    (hJ : (J+1)*(J+1) <= 2*n) :
    -(6 : Int)*((K-J : Nat) : Int) <=
      nearGapJointPacket n K (squareRemainingLargeModuli n a b) (squareModulusCoefficient a b) := by
  apply nearGapJointPacket_after_firstStrip_lower n K J
  next =>
    intro d hd
    have h := Finset.mem_filter.mp hd
    exact And.intro h.2.1 (squareModulusSupport_odd ha hb h.1)
  next => exact fun d _ => squareModulusCoefficient_bounds a b d
  next => exact fun d hd => (Finset.mem_filter.mp hd).2.2
  next => exact hJ

/-- The full signed complementary-factor contribution beyond the selected half-gap cutoff. -/
noncomputable def farGapJointPacket (n K : Nat) (s : Finset Nat) (c : Nat -> Int) : Int :=
  ((Finset.range (n+2)).product s).sum (fun x =>
    if K < (x.2-x.1)/2 then c x.2 * squarePairedCofactorKernel n x.2 x.1 else 0)

/-- The exact complementary-factor switch splits into near and far gaps without any missing cell. -/
theorem large_modulus_packet_eq_near_add_far (n K : Nat) (s : Finset Nat) (c : Nat -> Int)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1) :
    s.sum (fun d => c d * (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)) =
      nearGapJointPacket n K s c + farGapJointPacket n K s c := by
  rw [sum_large_modulus_joint_switch n s c hs]
  have hprod := Finset.sum_finset_product ((Finset.range (n+2)).product s)
    (Finset.range (n+2)) (fun _ => s) (fun _ => Finset.mem_product)
    (f := fun x : Prod Nat Nat => c x.2 * squarePairedCofactorKernel n x.2 x.1)
  rw [<- hprod]
  unfold nearGapJointPacket nearGapCofactorCells farGapJointPacket
  rw [Finset.sum_filter, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hgap : (x.2-x.1)/2 <= K
  next =>
    have hnot : Not (K < (x.2-x.1)/2) := by omega
    by_cases hz : squarePairedCofactorKernel n x.2 x.1 = 0
    next => simp [hgap, hnot, hz]
    next => simp [hgap, hnot, hz]
  next =>
    have hlt : K < (x.2-x.1)/2 := by omega
    simp [hgap, hlt]

/-- All moduli outside the first strip partition into low moduli and remaining large moduli. -/
theorem outside_firstStrip_sum_split (n : Nat) (s : Finset Nat) (f : Nat -> Int) :
    (s.filter (fun d => Not (n+1 < d /\ (d-(n+1))*(d-(n+1)) <= 2*n))).sum f =
      (s.filter (fun d => d <= n+1)).sum f +
      (s.filter (fun d => n+1 < d /\ 2*n < (d-(n+1))*(d-(n+1)))).sum f := by
  simp only [Finset.sum_filter, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hlow : d <= n+1
  next => simp [hlow, show Not (n+1 < d) by omega]
  next =>
    have hlarge : n+1 < d := by omega
    by_cases hsq : (d-(n+1))*(d-(n+1)) <= 2*n
    next => simp [hlow, hlarge, hsq, show Not (2*n < (d-(n+1))*(d-(n+1))) by omega]
    next => simp [hlow, hlarge, hsq, show 2*n < (d-(n+1))*(d-(n+1)) by omega]

/-- The exactly cancelled first-strip contribution, including its signed boundary coefficient. -/
noncomputable def squareFirstStripPacket (n : Nat) (a b : Finset Nat) : Int :=
  (squareFirstStrip n (squareModulusSupport a b)).sum (squareModulusCoefficient a b) -
    2 * (if Membership.mem (squareFirstStrip n (squareModulusSupport a b)) (n+2)
      then squareModulusCoefficient a b (n+2) else 0)

/-- Every low-modulus contribution, with the old and new floors kept coupled. -/
noncomputable def squareLowModulusPacket (n : Nat) (a b : Finset Nat) : Int :=
  ((squareModulusSupport a b).filter (fun d => d <= n+1)).sum
    (fun d => squareModulusCoefficient a b d *
      (2 * oddSquareFloor (n+1) d - oddSquareFloor n d))

/-- Complete exact four-part ledger: first strip, low moduli, remaining near gaps and far gaps. -/
theorem squareJointPacket_gap_ledger {n : Nat} (hn : 2 <= n) (K : Nat)
    {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1)
    (hab : Disjoint a b) :
    2 * squareJointPacket (n+1) a b - squareJointPacket n a b =
      squareFirstStripPacket n a b + squareLowModulusPacket n a b +
      nearGapJointPacket n K (squareRemainingLargeModuli n a b) (squareModulusCoefficient a b) +
      farGapJointPacket n K (squareRemainingLargeModuli n a b) (squareModulusCoefficient a b) := by
  rw [squareJointPacket_firstStrip_ledger hn ha hb hab, outside_firstStrip_sum_split]
  change squareFirstStripPacket n a b + (squareLowModulusPacket n a b +
    (squareRemainingLargeModuli n a b).sum (fun d => squareModulusCoefficient a b d *
      (2 * oddSquareFloor (n+1) d - oddSquareFloor n d))) = _
  have hs : forall d, Membership.mem (squareRemainingLargeModuli n a b) d ->
      n+1 < d /\ d % 2 = 1 := by
    intro d hd
    have h := Finset.mem_filter.mp hd
    exact And.intro h.2.1 (squareModulusSupport_odd
      (fun p hp => (ha p hp).2) (fun p hp => (hb p hp).2) h.1)
  rw [large_modulus_packet_eq_near_add_far n K _ _ hs]
  ring

/-- The shared unspent-gap capacity bounds a retained part of the complete joint packet. -/
theorem squareJointPacket_gap_lower {n : Nat} (hn : 2 <= n) (K J : Nat)
    {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1)
    (hab : Disjoint a b) (hJ : (J+1)*(J+1) <= 2*n) :
    squareFirstStripPacket n a b + squareLowModulusPacket n a b +
      farGapJointPacket n K (squareRemainingLargeModuli n a b) (squareModulusCoefficient a b) -
      6*((K-J : Nat) : Int) <=
        2 * squareJointPacket (n+1) a b - squareJointPacket n a b := by
  rw [squareJointPacket_gap_ledger hn K ha hb hab]
  have h := actual_nearGap_after_firstStrip_lower n K J a b
    (fun p hp => (ha p hp).2) (fun p hp => (hb p hp).2) hJ
  omega

end Nat.PrimeSieve
