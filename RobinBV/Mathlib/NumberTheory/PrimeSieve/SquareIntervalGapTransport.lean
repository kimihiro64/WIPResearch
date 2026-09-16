/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalSignedGapBudget

/-!
# Transport of quadratic factorization cells between square intervals

The predecessor (r,d) -> (r,d-2) pairs new cells with old cells except for
at most one cell at each of four possible centers. This reduces the leading
near-gap loss from six to nine halves, retaining the entire signed remainder.
No prime-distribution estimate is used or inferred.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- The strict new-window part of the complete geometric near-gap set. -/
noncomputable def squareGeometricNewNearCells (n K : Nat) : Finset (Prod Nat Nat) :=
  (squareGeometricNearCells n K).filter (fun x => n*n+2*n < x.2*x.1)

/-- Decrease the large odd factor by two, preserving the small factor. -/
def squareGapPredecessor (x : Prod Nat Nat) : Prod Nat Nat := (x.1, x.2-2)

/-- The arithmetic center of an admissible odd factor pair. -/
def squareGapCenter (x : Prod Nat Nat) : Nat := x.1+(x.2-x.1)/2

/-- New cells whose predecessor is absent from the actual old geometric set. -/
noncomputable def squareGeometricUnmatchedNew (n K : Nat) : Finset (Prod Nat Nat) :=
  (squareGeometricNewNearCells n K).filter (fun x =>
    Not (Membership.mem (squareGeometricOldNearCells n K) (squareGapPredecessor x)))

/-- A higher-center new pair has small factor at most n minus one. -/
theorem new_square_pair_small_factor {n r d : Nat} (hn : 2 <= n)
    (hr : r <= n+1) (hcenter : 2*(n+3) <= r+d)
    (hupper : d*r < (n+2)*(n+2)) : r+1 <= n := by
  by_contra hnot
  have hc : r = n \/ r = n+1 := by omega
  rcases hc with he | he
  next =>
    subst r
    have hd : n+6 <= d := by omega
    have hm := Nat.mul_le_mul_right n hd
    nlinarith only [hm, hupper, hn]
  next =>
    subst r
    have hd : n+5 <= d := by omega
    have hm := Nat.mul_le_mul_right (n+1) hd
    nlinarith only [hm, hupper]

/-- Reducing the large factor by two preserves the strict old lower endpoint. -/
theorem new_square_pair_predecessor_lower {n r d : Nat} (hn : 2 <= n)
    (hr : r <= n+1) (hcenter : 2*(n+3) <= r+d)
    (hlower : (n+1)*(n+1) < d*r) (hupper : d*r < (n+2)*(n+2)) :
    n*n < (d-2)*r := by
  have hrsmall := new_square_pair_small_factor hn hr hcenter hupper
  have hd : d-2+2 = d := by omega
  have he : (d-2)*r+2*r = d*r := by
    calc
      _ = (d-2+2)*r := by ring
      _ = _ := by rw [hd]
  nlinarith only [hrsmall, he, hlower]

/-- An old pair above the first center lies outside the first modulus strip. -/
theorem old_square_pair_outside_first_strip {n r d : Nat}
    (hd : n+1 < d) (hcenter : 2*(n+2) <= r+d)
    (hupper : d*r <= n*n+2*n) : 2*n < (d-(n+1))*(d-(n+1)) := by
  let g := d-(n+1)
  have he : d = n+1+g := by dsimp [g]; omega
  change 2*n < g*g
  rw [he] at hcenter hupper
  have hm := Nat.mul_le_mul_left (n+1+g) hcenter
  by_contra hnot
  have hg : g*g <= 2*n := by omega
  nlinarith only [hm, hupper, hg]

/-- A new geometric cell belongs to the strict new square interval. -/
theorem squareGeometricNewNearCells_window {n K : Nat} {x : Prod Nat Nat}
    (hx : Membership.mem (squareGeometricNewNearCells n K) x) :
    (n+1)*(n+1) < x.2*x.1 /\ x.2*x.1 < (n+2)*(n+2) := by
  have hb := Finset.mem_filter.mp hx
  have hc := Finset.mem_filter.mp hb.1
  have hgeometry := squarePairedCofactorKernel_geometry hc.2.2
  have hold : Not (x.1%2 = 1 /\ n*n < x.2*x.1 /\ x.2*x.1 <= n*n+2*n) := by
    intro h
    omega
  have hnew : x.1%2 = 1 /\ (n+1)*(n+1) < x.2*x.1 /\
      x.2*x.1 <= (n+1)*(n+1)+2*(n+1) := by
    by_contra hnot
    apply hc.2.2
    simp [squarePairedCofactorKernel, hnot, hold]
  exact And.intro hnew.2.1 hgeometry.2.2

/-- Every higher-center predecessor passing the old upper endpoint is an actual old cell. -/
theorem squareGapPredecessor_mem_old {n K : Nat} (hn : 2 <= n)
    {x : Prod Nat Nat} (hx : Membership.mem (squareGeometricNewNearCells n K) x)
    (hcenter : n+3 <= x.1+(x.2-x.1)/2)
    (hupper : (x.2-2)*x.1 <= n*n+2*n) :
    Membership.mem (squareGeometricOldNearCells n K) (squareGapPredecessor x) := by
  have hs : forall d, Membership.mem (squareGeometricLargeModuli n) d ->
      n+1 < d /\ d % 2 = 1 := by
    intro d hd
    have h := squareGeometricLargeModuli_data hd
    exact And.intro h.1 h.2.1
  have hb := Finset.mem_filter.mp hx
  have h := nearGapCofactorCells_data hs hb.1
  have hmem := Finset.mem_filter.mp hb.1
  have hrange := (Finset.mem_product.mp hmem.1).1
  have hr : x.1 <= n+1 := by have := Finset.mem_range.mp hrange; omega
  have hsum : 2*(n+3) <= x.1+x.2 := by omega
  have hw := squareGeometricNewNearCells_window hx
  have hrsmall := new_square_pair_small_factor hn hr hsum hw.2
  have hlower := new_square_pair_predecessor_lower hn hr hsum hw.1 hw.2
  have hdlarge : n+1 < x.2-2 := by omega
  have hsumold : 2*(n+2) <= x.1+(x.2-2) := by omega
  have hout := old_square_pair_outside_first_strip hdlarge hsumold hupper
  have hrpos : 1 <= x.1 := by omega
  have hdle : x.2-2 <= (x.2-2)*x.1 := by
    simpa using Nat.mul_le_mul_left (x.2-2) hrpos
  have hdodd := (hs x.2 h.1).2
  have hpredodd : (x.2-2)%2 = 1 := by omega
  have hexpand : (n+2)*(n+2) = n*n+4*n+4 := by ring
  have hdtop : x.2-2 <= (n+2)*(n+2)-1 := by omega
  have hmod : Membership.mem (squareGeometricLargeModuli n) (x.2-2) := by
    apply Finset.mem_filter.mpr
    exact And.intro (Finset.mem_Icc.mpr (And.intro (by omega) hdtop))
      (And.intro hpredodd hout)
  have hgap : ((x.2-2)-x.1)/2 <= K := by omega
  have hold : x.1%2 = 1 /\ n*n < (x.2-2)*x.1 /\ (x.2-2)*x.1 <= n*n+2*n :=
    And.intro h.2.1 (And.intro hlower hupper)
  have hnew : Not (x.1%2 = 1 /\ (n+1)*(n+1) < (x.2-2)*x.1 /\
      (x.2-2)*x.1 <= (n+1)*(n+1)+2*(n+1)) := by
    intro hh
    nlinarith only [hh.2.1, hupper]
  have hk : Not (squarePairedCofactorKernel n (x.2-2) x.1 = 0) := by
    simp only [squarePairedCofactorKernel, if_neg hnew, if_pos hold]
    norm_num
  apply Finset.mem_filter.mpr
  refine And.intro ?_ hupper
  apply Finset.mem_filter.mpr
  exact And.intro (Finset.mem_product.mpr (And.intro hrange hmod)) (And.intro hgap hk)

/-- The predecessor map is injective on the complete new geometric set. -/
theorem squareGapPredecessor_injOn_new (n K : Nat) :
    Set.InjOn squareGapPredecessor (squareGeometricNewNearCells n K) := by
  intro x hx y hy he
  have hxd := (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1).2
  have hyd := (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1).2
  have hxl := (squareGeometricLargeModuli_data hxd).1
  have hyl := (squareGeometricLargeModuli_data hyd).1
  have hr := congrArg (fun z : Prod Nat Nat => z.1) he
  have hd := congrArg (fun z : Prod Nat Nat => z.2) he
  simp only [squareGapPredecessor] at hr hd
  apply Prod.ext hr
  omega

/-- At most one integer gap straddles a fixed translated square threshold. -/
theorem translated_square_crossing_unique {a b k l : Nat}
    (hklo : a < k*k+b) (hkhi : (k-1)*(k-1)+b < a)
    (hllo : a < l*l+b) (hlhi : (l-1)*(l-1)+b < a) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  next =>
    have hle : k <= l-1 := by omega
    have hsq := Nat.mul_le_mul hle hle
    nlinarith only [hsq, hklo, hlhi]
  next => exact h
  next =>
    have hle : l <= k-1 := by omega
    have hsq := Nat.mul_le_mul hle hle
    nlinarith only [hsq, hllo, hkhi]
/-- The square-strip endpoint conditions permit at most one gap of a given parity. -/
theorem square_strip_parity_unique {n k l : Nat}
    (hpar : k%2 = l%2)
    (hklo : 2*n < (k+1)*(k+1)) (hkhi : k*k <= 2*n+2)
    (hllo : 2*n < (l+1)*(l+1)) (hlhi : l*l <= 2*n+2) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  next =>
    have hle : k+2 <= l := by omega
    have hsq := Nat.mul_le_mul hle hle
    nlinarith only [hsq, hklo, hlhi]
  next => exact h
  next =>
    have hle : l+2 <= k := by omega
    have hsq := Nat.mul_le_mul hle hle
    nlinarith only [hsq, hllo, hkhi]

/-- The original and predecessor products have exact center-minus-gap square identities. -/
theorem squareGeometricNearCells_center_identities {n K : Nat} {x : Prod Nat Nat}
    (hx : Membership.mem (squareGeometricNearCells n K) x) :
    x.2*x.1+((x.2-x.1)/2)^2 = (squareGapCenter x)^2 /\
      (x.2-2)*x.1+((x.2-x.1)/2-1)^2 = (squareGapCenter x-1)^2 := by
  have hs : forall d, Membership.mem (squareGeometricLargeModuli n) d ->
      n+1 < d /\ d%2 = 1 := by
    intro d hd
    have h := squareGeometricLargeModuli_data hd
    exact And.intro h.1 h.2.1
  have h := nearGapCofactorCells_data hs hx
  let k := (x.2-x.1)/2
  have hk : 1 <= k := h.2.2.2.1
  have hd : x.2 = x.1+2*k := h.2.2.1
  change x.2*x.1+k^2 = (x.1+k)^2 /\ (x.2-2)*x.1+(k-1)^2 = (x.1+k-1)^2
  constructor
  next => rw [hd]; ring
  next =>
    have hdp : x.2-2 = x.1+2*(k-1) := by omega
    have hap : x.1+k-1 = x.1+(k-1) := by omega
    rw [hdp, hap]
    ring

/-- Every new geometric cell has center at least n plus two. -/
theorem squareGeometricNewNearCells_center_lower {n K : Nat} {x : Prod Nat Nat}
    (hx : Membership.mem (squareGeometricNewNearCells n K) x) :
    n+2 <= squareGapCenter x := by
  have he := (squareGeometricNearCells_center_identities (Finset.mem_filter.mp hx).1).1
  have hw := squareGeometricNewNearCells_window hx
  by_contra hnot
  have hle : squareGapCenter x <= n+1 := by omega
  have hsq := Nat.mul_le_mul hle hle
  nlinarith only [he, hw.1, hsq]

/-- At most one actual new cell occupies the lowest admissible center. -/
theorem squareGeometricNewNearCells_first_center_unique {n K : Nat} {x y : Prod Nat Nat}
    (hx : Membership.mem (squareGeometricNewNearCells n K) x)
    (hy : Membership.mem (squareGeometricNewNearCells n K) y)
    (hxC : squareGapCenter x = n+2) (hyC : squareGapCenter y = n+2) : x = y := by
  have hs : forall d, Membership.mem (squareGeometricLargeModuli n) d ->
      n+1 < d /\ d%2 = 1 := by
    intro d hd
    have h := squareGeometricLargeModuli_data hd
    exact And.intro h.1 h.2.1
  have hxb := (Finset.mem_filter.mp hx).1
  have hyb := (Finset.mem_filter.mp hy).1
  have hxd := nearGapCofactorCells_data hs hxb
  have hyd := nearGapCofactorCells_data hs hyb
  let k := (x.2-x.1)/2
  let l := (y.2-y.1)/2
  have hxc : x.1+k = n+2 := hxC
  have hyc : y.1+l = n+2 := hyC
  have hpar : k%2 = l%2 := by omega
  have hxx : x.2-(n+1) = k+1 := by omega
  have hyy : y.2-(n+1) = l+1 := by omega
  have hxs := (squareGeometricLargeModuli_data hxd.1).2.2
  have hys := (squareGeometricLargeModuli_data hyd.1).2.2
  rw [hxx] at hxs
  rw [hyy] at hys
  have hxw := squareGeometricNewNearCells_window hx
  have hyw := squareGeometricNewNearCells_window hy
  have hxe : x.2*x.1+k*k = (n+2)*(n+2) := by
    simpa only [pow_two, hxC] using (squareGeometricNearCells_center_identities hxb).1
  have hye : y.2*y.1+l*l = (n+2)*(n+2) := by
    simpa only [pow_two, hyC] using (squareGeometricNearCells_center_identities hyb).1
  have hxhi : k*k <= 2*n+2 := by nlinarith only [hxe, hxw.1]
  have hyhi : l*l <= 2*n+2 := by nlinarith only [hye, hyw.1]
  have he := square_strip_parity_unique hpar hxs hxhi hys hyhi
  exact nearGapCofactorCells_halfGap_injOn n K hs hxb hyb he

/-- A failed higher-center predecessor straddles two consecutive gap squares. -/
theorem squareGeometricUnmatchedNew_crossing {n K : Nat} (hn : 2 <= n)
    {x : Prod Nat Nat} (hx : Membership.mem (squareGeometricUnmatchedNew n K) x)
    (hcenter : n+3 <= squareGapCenter x) :
    (squareGapCenter x-1)^2 < ((x.2-x.1)/2)^2+(n*n+2*n) /\
      ((x.2-x.1)/2-1)^2+(n*n+2*n) < (squareGapCenter x-1)^2 := by
  have hb := Finset.mem_filter.mp hx
  have hbad : n*n+2*n < (x.2-2)*x.1 := by
    by_contra hnot
    exact hb.2 (squareGapPredecessor_mem_old hn hb.1 hcenter (by omega))
  have he := squareGeometricNearCells_center_identities (Finset.mem_filter.mp hb.1).1
  have hw := squareGeometricNewNearCells_window hb.1
  let a := squareGapCenter x
  let k := (x.2-x.1)/2
  have ha : n+3 <= a := hcenter
  have ha1 : n+2 <= a-1 := by omega
  have hae : a-1+1 = a := by omega
  have hasq : (a-1)*(a-1)+2*(a-1)+1 = a*a := by
    calc
      _ = (a-1+1)*(a-1+1) := by ring
      _ = _ := by rw [hae]
  have hep : x.2*x.1+k*k = a*a := by simpa only [pow_two] using he.1
  have heq : (x.2-2)*x.1+(k-1)*(k-1) = (a-1)*(a-1) := by
    simpa only [pow_two] using he.2
  simp only [pow_two]
  change (a-1)*(a-1) < k*k+(n*n+2*n) /\
    (k-1)*(k-1)+(n*n+2*n) < (a-1)*(a-1)
  constructor
  next => nlinarith only [hep, hw.2, hasq, ha1]
  next => nlinarith only [heq, hbad]

/-- Unmatched new cells have distinct centers. -/
theorem squareGapCenter_injOn_unmatched {n K : Nat} (hn : 2 <= n) :
    Set.InjOn squareGapCenter (squareGeometricUnmatchedNew n K) := by
  intro x hx y hy he
  have hxN := (Finset.mem_filter.mp hx).1
  have hyN := (Finset.mem_filter.mp hy).1
  have hxlo := squareGeometricNewNearCells_center_lower hxN
  by_cases hxC : squareGapCenter x = n+2
  next =>
    exact squareGeometricNewNearCells_first_center_unique hxN hyN hxC (by omega)
  next =>
    have hxc := squareGeometricUnmatchedNew_crossing hn hx (by omega)
    have hyc := squareGeometricUnmatchedNew_crossing hn hy (by omega)
    rw [<- he] at hyc
    simp only [pow_two] at hxc hyc
    have hk := translated_square_crossing_unique hxc.1 hxc.2 hyc.1 hyc.2
    have hs : forall d, Membership.mem (squareGeometricLargeModuli n) d ->
        n+1 < d /\ d%2 = 1 := by
      intro d hd
      have h := squareGeometricLargeModuli_data hd
      exact And.intro h.1 h.2.1
    exact nearGapCofactorCells_halfGap_injOn n K hs
      (Finset.mem_filter.mp hxN).1 (Finset.mem_filter.mp hyN).1 hk

/-- At a square-root gap cutoff there are at most four unmatched new cells. -/
theorem card_squareGeometricUnmatchedNew_le_four {n K : Nat} (hn : 2 <= n)
    (hK : K*K <= 8*n) : (squareGeometricUnmatchedNew n K).card <= 4 := by
  have hcard : (squareGeometricUnmatchedNew n K).card <= (Finset.Icc (n+2) (n+5)).card := by
    apply Finset.card_le_card_of_injOn squareGapCenter
    next =>
      intro x hx
      have hxN := (Finset.mem_filter.mp hx).1
      have hlo := squareGeometricNewNearCells_center_lower hxN
      have hhi := (squareGeometricNearCells_five_centers hK (Finset.mem_filter.mp hxN).1).2
      exact Finset.mem_Icc.mpr (And.intro hlo hhi)
    next => exact squareGapCenter_injOn_unmatched hn
  simp only [Nat.card_Icc] at hcard
  omega

/-- All but four new geometric cells inject into the old geometric cells. -/
theorem card_squareGeometricNewNearCells_le_old_add_four {n K : Nat} (hn : 2 <= n)
    (hK : K*K <= 8*n) :
    (squareGeometricNewNearCells n K).card <= (squareGeometricOldNearCells n K).card+4 := by
  let good := (squareGeometricNewNearCells n K).filter (fun x =>
    Membership.mem (squareGeometricOldNearCells n K) (squareGapPredecessor x))
  have hg : good.card <= (squareGeometricOldNearCells n K).card := by
    apply Finset.card_le_card_of_injOn squareGapPredecessor
    next => exact fun x hx => (Finset.mem_filter.mp hx).2
    next =>
      intro x hx y hy he
      exact squareGapPredecessor_injOn_new n K (Finset.mem_filter.mp hx).1
        (Finset.mem_filter.mp hy).1 he
  have hb := card_squareGeometricUnmatchedNew_le_four hn hK
  have hp := Finset.sum_filter_add_sum_filter_not (squareGeometricNewNearCells n K)
    (fun x => Membership.mem (squareGeometricOldNearCells n K) (squareGapPredecessor x))
    (fun _ => (1 : Nat))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hp
  change good.card+(squareGeometricUnmatchedNew n K).card =
    (squareGeometricNewNearCells n K).card at hp
  omega

/-- The old and new windows partition the complete geometric near set. -/
theorem card_squareGeometricNearCells_split (n K : Nat) :
    (squareGeometricOldNearCells n K).card + (squareGeometricNewNearCells n K).card =
      (squareGeometricNearCells n K).card := by
  have h := Finset.sum_filter_add_sum_filter_not (squareGeometricNearCells n K)
    (fun x => x.2*x.1 <= n*n+2*n) (fun _ => (1 : Nat))
  simpa [Finset.sum_const, nsmul_eq_mul, mul_one, not_le,
    squareGeometricOldNearCells, squareGeometricNewNearCells] using h

/-- Transport replaces the leading loss coefficient six by nine halves. -/
theorem squareGeometricNearCellLoss_transport_bound {n K J : Nat} (hn : 2 <= n)
    (hK : K*K <= 8*n) (hJ : (J+1)*(J+1) <= 2*n) :
    2*(6*((squareGeometricNearCells n K).card : Int) -
      3*((squareGeometricOldNearCells n K).card : Int)) <=
        9*((K-J : Nat) : Int)+12 := by
  have ht : ((squareGeometricNewNearCells n K).card : Int) <=
      ((squareGeometricOldNearCells n K).card : Int)+4 := by
    exact_mod_cast card_squareGeometricNewNearCells_le_old_add_four hn hK
  have hp : ((squareGeometricOldNearCells n K).card : Int)+
      ((squareGeometricNewNearCells n K).card : Int) =
        ((squareGeometricNearCells n K).card : Int) := by
    exact_mod_cast card_squareGeometricNearCells_split n K
  have hc : ((squareGeometricNearCells n K).card : Int) <= ((K-J : Nat) : Int) := by
    exact_mod_cast card_squareGeometricNearCells_le n K J hJ
  linarith only [ht, hp, hc]

/-- The complete arithmetic packet retains both low and far sums after transport. -/
theorem squareJointPacket_gap_transport_lower {n K J : Nat} (hn : 2 <= n)
    (hK : K*K <= 8*n) (hJ : (J+1)*(J+1) <= 2*n)
    {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p%2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p%2 = 1)
    (hab : Disjoint a b) :
    2*(squareFirstStripPacket n a b + squareLowModulusPacket n a b +
      farGapJointPacket n K (squareRemainingLargeModuli n a b) (squareModulusCoefficient a b)) -
      9*((K-J : Nat) : Int)-12 <=
        2*(2*squareJointPacket (n+1) a b-squareJointPacket n a b) := by
  have hp := squareJointPacket_signed_gap_lower hn K ha hb hab
  have hc := squareGeometricNearCellLoss_transport_bound hn hK hJ
  linarith only [hp, hc]

end Nat.PrimeSieve
