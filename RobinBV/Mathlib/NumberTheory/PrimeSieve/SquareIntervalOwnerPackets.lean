/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalDensity
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalGeometricSupply

/-!
# Exact small-owner removal in the full composite allowance

Screened small owners form a disjoint block. Removing that block from the
candidate supply leaves the complete finite Euler product and its signed
inclusion-exclusion error. The resulting prime-count estimate keeps all
middle owners, the independently bounded balanced band, and the collision
credit from the same geometry. No estimate of the middle packet is assumed.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

theorem owner_first_le_of_screened_prime_dvd
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n cut ell : Nat} {S R : Finset Nat}
    {x : Prod Nat Nat} (hell : Nat.Prime ell) (hmem : Membership.mem R ell)
    (hx : Membership.mem (ownerLineFamilyHighFactorCells Gamma n cut S R) x)
    (hd : Dvd.dvd ell (x.1*x.2)) : x.1 <= ell := by
  have hp := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have ho := Finset.mem_filter.mp hp.1
  rcases hell.dvd_mul.mp hd with hfirst | hsecond
  next => exact le_of_eq ((ho.2 ell hmem).1 hfirst).symm
  next =>
    by_contra h
    exact (ho.2 ell hmem).2 (by omega) hsecond

/-- Small screened owners are genuinely disjoint; no multiplicity relaxation
is used in their removal from the positive supply. -/
theorem screened_small_owner_product_injective
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n cut T : Nat} {S R : Finset Nat}
    (hcover : forall p, Nat.Prime p -> p%2 = 1 -> p <= T -> Membership.mem R p) :
    Set.InjOn (fun x : Prod Nat Nat => x.1*x.2)
      ((ownerLineFamilyHighFactorCells Gamma n cut S R).filter (fun x => x.1 <= T)) := by
  intro x hx y hy he
  change x.1*x.2 = y.1*y.2 at he
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  have hpx := Finset.mem_filter.mp (Finset.mem_filter.mp hx'.1).1
  have hpy := Finset.mem_filter.mp (Finset.mem_filter.mp hy'.1).1
  have hcx := Finset.mem_filter.mp (Finset.mem_filter.mp hpx.1).1
  have hcy := Finset.mem_filter.mp (Finset.mem_filter.mp hpy.1).1
  have hxm := hcover x.1 hpx.2 hcx.2.2.2.2.1 hx'.2
  have hym := hcover y.1 hpy.2 hcy.2.2.2.2.1 hy'.2
  have hdx : Dvd.dvd x.1 (y.1*y.2) := by rw [<- he]; exact dvd_mul_right x.1 x.2
  have hdy : Dvd.dvd y.1 (x.1*x.2) := by rw [he]; exact dvd_mul_right y.1 y.2
  have hxy := owner_first_le_of_screened_prime_dvd hpx.2 hxm hy'.1 hdx
  have hyx := owner_first_le_of_screened_prime_dvd hpy.2 hym hx'.1 hdy
  have hefirst : x.1 = y.1 := by omega
  change x.1*x.2 = y.1*y.2 at he
  rw [<- hefirst] at he
  exact Prod.ext hefirst (Nat.eq_of_mul_eq_mul_left hpx.2.pos he)

theorem screened_small_owner_image
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 2 <= n) (hT : T <= n)
    (hS : forall p, Membership.mem S p -> Nat.Prime p)
    (hR : forall p, Membership.mem R p -> 2 <= p)
    (hcover : forall p, Nat.Prime p -> p%2 = 1 -> p <= T -> Membership.mem R p) :
    (((ownerLineFamilyHighFactorCells Gamma n 0 S R).filter (fun x => x.1 <= T)).image
      (fun x => x.1*x.2)) =
        SDiff.sdiff (oddSievedOwnerInSquare n 1 S)
          (oddSievedOwnerInSquare n 1 (Union.union S (oddEarlierPrimes (T+1)))) := by
  classical
  ext m
  constructor
  next =>
    intro hm
    choose x hx using Finset.mem_image.mp hm
    have hx' := Finset.mem_filter.mp hx.1
    have hp := Finset.mem_filter.mp (Finset.mem_filter.mp hx'.1).1
    have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1
    have hf : Membership.mem (oddSievedOwnerInSquare n 1 S) m := by
      rw [<- hx.2]
      exact line_family_product_mem_prefix hS hx'.1
    have hb : Membership.mem (oddEarlierPrimes (T+1)) x.1 :=
      Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
        (And.intro hp.2 hc.2.2.2.2.1))
    apply Finset.mem_sdiff.mpr
    refine And.intro hf ?_
    intro he
    have hav := (Finset.mem_filter.mp he).2.2 x.1 (Finset.mem_union_right S hb)
    apply hav
    rw [<- hx.2]
    exact dvd_mul_right x.1 x.2
  next =>
    intro hm
    have hd := Finset.mem_sdiff.mp hm
    have hex : exists p, Membership.mem (oddEarlierPrimes (T+1)) p /\ Dvd.dvd p m := by
      by_contra hnone
      apply hd.2
      have hf := Finset.mem_filter.mp hd.1
      apply Finset.mem_filter.mpr
      refine And.intro hf.1 (And.intro hf.2.1 ?_)
      intro p hp
      rcases Finset.mem_union.mp hp with hs | hb
      next => exact hf.2.2 p hs
      next =>
        intro hdiv
        exact hnone (Exists.intro p (And.intro hb hdiv))
    choose p hp using hex
    have hb := Finset.mem_filter.mp hp.1
    have hple : p <= T := by have h := Finset.mem_range.mp hb.1; omega
    have hpmem := hcover p hb.2.1 hb.2.2 hple
    have hlo : n*n < m := (Finset.mem_filter.mp (Finset.mem_filter.mp hd.1).1).2
    have hnp : Not (Nat.Prime m) := by
      intro hprime
      have he := (hprime.eq_one_or_self_of_dvd p hp.2).resolve_left hb.2.1.ne_one
      nlinarith
    rcases prefix_composite_mem_owner_or_line_family (T := 0) Gamma S R hR hn hd.1 hnp with hlow | hhigh
    next =>
      choose q hq using Finset.mem_biUnion.mp hlow
      have hqf := Finset.mem_filter.mp hq.1
      have hq0 := Finset.mem_range.mp hqf.1
      have hq2 := hqf.2.1.two_le
      omega
    next =>
      choose x hx using Finset.mem_image.mp hhigh
      have hdiv : Dvd.dvd p (x.1*x.2) := by rw [hx.2]; exact hp.2
      have hxp := owner_first_le_of_screened_prime_dvd hb.2.1 hpmem hx.1 hdiv
      exact Finset.mem_image.mpr (Exists.intro x (And.intro
        (Finset.mem_filter.mpr (And.intro hx.1 (hxp.trans hple))) hx.2))

/-- Exact joint removal of all small owners. This preserves the survivor
supply and retains every middle and large owner for subsequent estimates. -/
theorem screened_small_owner_removal
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 2 <= n) (hT : T <= n)
    (hS : forall p, Membership.mem S p -> Nat.Prime p)
    (hR : forall p, Membership.mem R p -> 2 <= p)
    (hcover : forall p, Nat.Prime p -> p%2 = 1 -> p <= T -> Membership.mem R p) :
    ((ownerLineFamilyHighFactorCells Gamma n 0 S R).filter (fun x => x.1 <= T)).card+
      (oddSievedOwnerInSquare n 1 (Union.union S (oddEarlierPrimes (T+1)))).card =
        (oddSievedOwnerInSquare n 1 S).card := by
  classical
  have hsub : oddSievedOwnerInSquare n 1 (Union.union S (oddEarlierPrimes (T+1))) <=
      oddSievedOwnerInSquare n 1 S := by
    intro m hm
    have hd := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr (And.intro hd.1 (And.intro hd.2.1
      (fun p hp => hd.2.2 p (Finset.mem_union_left _ hp))))
  have hi := screened_small_owner_image (Gamma := Gamma) hn hT hS hR hcover
  have h := Finset.card_sdiff_add_card_eq_card hsub
  rw [<- hi] at h
  have hc := Finset.card_image_iff.mpr (screened_small_owner_product_injective
    (Gamma := Gamma) (n := n) (cut := 0) (S := S) hcover)
  rw [hc] at h
  exact h

/-- Keep the complete finite density exactly. Only the nonempty divisor
packet errors are bounded, after the signed main terms have been combined. -/
theorem sieved_square_complete_packet_error (n : Nat) (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p /\ p%2 = 1) :
    abs (((oddSievedOwnerInSquare n 1 S).card : Real)-
      (n : Real)*S.prod (fun p => 1-1/(p : Real))) <= (2 : Real)^S.card-1 := by
  classical
  let P := S.powerset
  let D := P.erase (Finset.empty : Finset Nat)
  let w := fun u : Finset Nat => (-1 : Real)^u.card *
    (((oddMultiplesInSquare n (u.prod (fun p => p))).card : Real)-
      (n : Real)/((u.prod (fun p => p) : Nat) : Real))
  have hc : ((oddSievedOwnerInSquare n 1 S).card : Real) =
      P.sum (fun u => (-1 : Real)^u.card *
        ((oddMultiplesInSquare n (u.prod (fun p => p))).card : Real)) := by
    have h := prefix_card_eq_signed_packet S n (fun p hp => (hS p hp).1)
    unfold signedOddSquarePacket at h
    exact_mod_cast h
  have hm : P.sum (fun u => (-1 : Real)^u.card *
      ((n : Real)/((u.prod (fun p => p) : Nat) : Real))) =
        (n : Real)*S.prod (fun p => 1-1/(p : Real)) := by
    calc
      _ = (n : Real)*P.sum (fun u => (-1 : Real)^u.card *
          u.prod (fun p => 1/(p : Real))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        simp only [Nat.cast_prod, div_eq_mul_inv, one_mul, Finset.prod_inv_distrib]
        ring
      _ = _ := by rw [signed_reciprocal_product]
  have hid : ((oddSievedOwnerInSquare n 1 S).card : Real)-
      (n : Real)*S.prod (fun p => 1-1/(p : Real)) = P.sum w := by
    dsimp only [w]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, <- hc, hm]
  have h1 : (oddMultiplesInSquare n 1).card = n := by
    have h := card_oddMultiplesInSquare n (d := 1) (by decide)
    simp only [Nat.div_one] at h
    omega
  have hw0 : w (Finset.empty : Finset Nat) = 0 := by simp [w, Finset.empty, h1]
  have he : Membership.mem P (Finset.empty : Finset Nat) := by simp [P, Finset.empty]
  have hDsum : D.sum w = P.sum w := by
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro u hu hnot
    have hu0 : u = (Finset.empty : Finset Nat) := by
      by_contra hh
      exact hnot (Finset.mem_erase.mpr (And.intro hh hu))
    simpa only [hu0] using hw0
  have hw : forall u, Membership.mem D u -> abs (w u) <= 1 := by
    intro u hu
    have huS : u <= S := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hu)
    have hodd : (u.prod (fun p => p))%2 = 1 :=
      prod_odd_mod_two (fun p hp => (hS p (huS hp)).2)
    have h := odd_interval_abs_unit_error n hodd
    simpa only [w, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using h.le
  have hcard : D.card+1 = 2^S.card := by
    have hd := Finset.card_erase_of_mem he
    have hp : 0 < P.card := Finset.card_pos.mpr (Exists.intro _ he)
    have hpow : P.card = 2^S.card := by simp [P]
    change D.card = P.card-1 at hd
    omega
  have hcardR : (D.card : Real)+1 = (2 : Real)^S.card := by exact_mod_cast hcard
  calc
    abs (((oddSievedOwnerInSquare n 1 S).card : Real)-
        (n : Real)*S.prod (fun p => 1-1/(p : Real))) = abs (D.sum w) := by rw [hid, hDsum]
    _ <= D.sum (fun u => abs (w u)) := Finset.abs_sum_le_sum_abs _ _
    _ <= D.sum (fun _ => (1 : Real)) := Finset.sum_le_sum hw
    _ = (D.card : Real) := by simp
    _ = (2 : Real)^S.card-1 := by linarith only [hcardR]

/-- A bound on the negative small-owner packet with a surviving, exact
finite-density supply. No middle or large owner is removed from the ledger. -/
theorem screened_small_owner_packet_upper
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 2 <= n) (hT : T <= n)
    (hS : forall p, Membership.mem S p -> Nat.Prime p /\ p%2 = 1)
    (hR : forall p, Membership.mem R p -> 2 <= p)
    (hcover : forall p, Nat.Prime p -> p%2 = 1 -> p <= T -> Membership.mem R p) :
    let B := Union.union S (oddEarlierPrimes (T+1))
    (((ownerLineFamilyHighFactorCells Gamma n 0 S R).filter
      (fun x => x.1 <= T)).card : Real) <=
        ((oddSievedOwnerInSquare n 1 S).card : Real)-
          (n : Real)*B.prod (fun p => 1-1/(p : Real))+(2 : Real)^B.card-1 := by
  let B := Union.union S (oddEarlierPrimes (T+1))
  have hB : forall p, Membership.mem B p -> Nat.Prime p /\ p%2 = 1 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hs | hb
    next => exact hS p hs
    next => exact (Finset.mem_filter.mp hb).2
  have he := sieved_square_complete_packet_error n B hB
  have hl := (abs_le.mp he).1
  have hi := screened_small_owner_removal (Gamma := Gamma) hn hT
    (fun p hp => (hS p hp).1) hR hcover
  have hr : (((ownerLineFamilyHighFactorCells Gamma n 0 S R).filter
      (fun x => x.1 <= T)).card : Real)+
        ((oddSievedOwnerInSquare n 1 B).card : Real) =
          ((oddSievedOwnerInSquare n 1 S).card : Real) := by exact_mod_cast hi
  change _ <= ((oddSievedOwnerInSquare n 1 S).card : Real)-
    (n : Real)*B.prod (fun p => 1-1/(p : Real))+(2 : Real)^B.card-1
  linarith only [hl, hr]

/-- Full prime-count bound after exact small-owner removal. The finite
density is kept intact for joint comparison with the middle owners. -/
theorem prime_count_ge_middle_owner_allowance
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) {n T : Nat}
    (hn : 9 <= n) (hT : 2*T <= n) (hTs : T*T <= 2*n+1) :
    let B := Union.union fivePrimePrefix (oddEarlierPrimes (T+1))
    let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix (balancedOwnerScreen n)
    (n : Real)*B.prod (fun p => 1-1/(p : Real))-((2 : Real)^B.card-1)-
      ((G.filter (fun x => T < x.1 /\ 2*x.1 <= n)).card : Real)-
        (((Finset.Icc (n+1) (2*n+1)).filter Nat.Prime).card : Real)+
          lineCollisionCredit G <= ((squareIntervalPrimes n).card : Real) := by
  classical
  let R := balancedOwnerScreen n
  let B := Union.union fivePrimePrefix (oddEarlierPrimes (T+1))
  let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R
  let small := G.filter (fun x => x.1 <= T)
  let middle := G.filter (fun x => T < x.1 /\ 2*x.1 <= n)
  let low := G.filter (fun x => 2*x.1 <= n)
  let high := G.filter (fun x => n < 2*x.1)
  have hS : forall p, Membership.mem fivePrimePrefix p -> Nat.Prime p /\ p%2 = 1 := by
    intro p hp
    refine And.intro (fivePrimePrefix_prime hp) ?_
    simp only [fivePrimePrefix, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
  have hR : forall p, Membership.mem R p -> 2 <= p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1.two_le
  have hcomplete : forall p, Nat.Prime p -> p%2 = 1 -> p*p <= 2*n+1 -> Membership.mem R p := by
    intro p hp ho hs
    exact balancedOwnerScreen_complete hp ho hs
  have hcut : forall p, Nat.Prime p -> p%2 = 1 -> p*p <= n -> Membership.mem R p := by
    intro p hp ho hs
    exact hcomplete p hp ho (by omega)
  have hcover : forall p, Nat.Prime p -> p%2 = 1 -> p <= T -> Membership.mem R p := by
    intro p hp ho hpt
    exact hcomplete p hp ho ((Nat.mul_le_mul hpt hpt).trans hTs)
  have hcomp := actual_composites_le_exactPrefixAllowance (Gamma := Gamma)
    (by omega : 2 <= n) hR hcut
  dsimp only at hcomp
  change 2*(n : Real)-((squareIntervalPrimes n).card : Real) <=
    2*(n : Real)-((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+
      (G.card : Real)-lineCollisionCredit G at hcomp
  have hs := screened_small_owner_packet_upper (Gamma := Gamma)
    (by omega : 2 <= n) (by omega : T <= n) hS hR hcover
  dsimp only at hs
  change (small.card : Real) <= ((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)-
    (n : Real)*B.prod (fun p => 1-1/(p : Real))+(2 : Real)^B.card-1 at hs
  have hsmall : low.filter (fun x => x.1 <= T) = small := by
    ext x
    constructor
    next =>
      intro hx
      have hh := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_filter.mp hh.1).1 hh.2)
    next =>
      intro hx
      have hh := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr (And.intro
        (Finset.mem_filter.mpr (And.intro hh.1 ((Nat.mul_le_mul_left 2 hh.2).trans hT))) hh.2)
  have hmiddle : low.filter (fun x => Not (x.1 <= T)) = middle := by
    ext x
    constructor
    next =>
      intro hx
      have hh := Finset.mem_filter.mp hx
      have hl := Finset.mem_filter.mp hh.1
      exact Finset.mem_filter.mpr (And.intro hl.1 (And.intro (by omega) hl.2))
    next =>
      intro hx
      have hh := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr (And.intro
        (Finset.mem_filter.mpr (And.intro hh.1 hh.2.2)) (by have h := hh.2.1; omega))
  have hhigh : G.filter (fun x => Not (2*x.1 <= n)) = high := by
    change G.filter (fun x => Not (2*x.1 <= n)) = G.filter (fun x => n < 2*x.1)
    simp only [not_le]
  have hlow := Finset.card_filter_add_card_filter_not (s := low) (fun x => x.1 <= T)
  rw [hsmall, hmiddle] at hlow
  have hall := Finset.card_filter_add_card_filter_not (s := G) (fun x => 2*x.1 <= n)
  rw [hhigh] at hall
  change low.card+high.card = G.card at hall
  have hsplit : small.card+middle.card+high.card = G.card := by omega
  have hsplitR : (small.card : Real)+(middle.card : Real)+(high.card : Real) = (G.card : Real) := by
    exact_mod_cast hsplit
  have hb : (high.card : Real) <=
      (((Finset.Icc (n+1) (2*n+1)).filter Nat.Prime).card : Real) := by
    exact_mod_cast screened_balanced_owner_card_le_prime_cofactors (Gamma := Gamma)
      (T := 0) (S := fivePrimePrefix) hn hcomplete
  change (n : Real)*B.prod (fun p => 1-1/(p : Real))-((2 : Real)^B.card-1)-
    (middle.card : Real)-(((Finset.Icc (n+1) (2*n+1)).filter Nat.Prime).card : Real)+
      lineCollisionCredit G <= _
  linarith only [hcomp, hs, hsplitR, hb]

/-- An explicit high-band fallback, kept separate from the sharper prime
cofactor capacity. The middle owner-minus-collision estimate is still open. -/
theorem prime_count_ge_middle_owner_explicit_high
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) {n T : Nat}
    (hn : 9 <= n) (hT : 2*T <= n) (hTs : T*T <= 2*n+1) :
    let B := Union.union fivePrimePrefix (oddEarlierPrimes (T+1))
    let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix (balancedOwnerScreen n)
    (n : Real)*B.prod (fun p => 1-1/(p : Real))-((2 : Real)^B.card-1)-
      ((G.filter (fun x => T < x.1 /\ 2*x.1 <= n)).card : Real)-
        balancedPrimeLogAllowance n+lineCollisionCredit G <=
          ((squareIntervalPrimes n).card : Real) := by
  have h := prime_count_ge_middle_owner_allowance Gamma hn hT hTs
  have hb := balanced_prime_cofactors_le_explicit_log (by omega : 4 <= n)
  dsimp only at h
  dsimp only
  linarith only [h, hb]

end Nat.PrimeSieve
