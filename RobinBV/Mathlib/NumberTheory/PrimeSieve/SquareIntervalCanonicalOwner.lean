/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalBalancedCollisions
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalTensorLog

/-!
# Canonical least-owner transfer of the collision-corrected allowance

The complete three-fiber correction transports the representation count
exactly to canonical least-prime-owner pairs. A canonical owner above the
cube-root cutoff has a prime cofactor. The final prime-count consumer keeps
the canonical middle count explicit and applies the independent tensor
estimate only to the upper half band; no uniform middle estimate is assumed.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

theorem line_family_first_le_index
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    {x : Prod Nat Nat} (hx : Membership.mem (ownerLineFamilyHighFactorCells Gamma n T S R) x) :
    x.1 <= n := by
  have hp := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1
  have h := Finset.mem_range.mp (Finset.mem_product.mp hc.1).1
  omega

theorem line_family_product_not_prime
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    {x : Prod Nat Nat} (hn : 2 <= n)
    (hx : Membership.mem (ownerLineFamilyHighFactorCells Gamma n T S R) x) :
    Not (Nat.Prime (x.1*x.2)) := by
  have hp := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1
  have hlo := hc.2.2.1
  have hpn := line_family_first_le_index hx
  intro hprime
  have he := (hprime.eq_one_or_self_of_dvd x.1 (dvd_mul_right x.1 x.2)).resolve_left hp.2.ne_one
  nlinarith

theorem line_family_image_eq_prefix_composites
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) {n : Nat} {S R : Finset Nat}
    (hn : 2 <= n) (hS : forall p, Membership.mem S p -> Nat.Prime p)
    (hR : forall p, Membership.mem R p -> 2 <= p) :
    (ownerLineFamilyHighFactorCells Gamma n 0 S R).image (fun x => x.1*x.2) =
      (oddSievedOwnerInSquare n 1 S).filter (fun m => Not (Nat.Prime m)) := by
  ext m
  constructor
  next =>
    intro hm
    choose x hx using Finset.mem_image.mp hm
    have hf := line_family_product_mem_prefix hS hx.1
    have hc := line_family_product_not_prime hn hx.1
    rw [hx.2] at hf hc
    exact Finset.mem_filter.mpr (And.intro hf hc)
  next =>
    intro hm
    have hd := Finset.mem_filter.mp hm
    rcases prefix_composite_mem_owner_or_line_family (T := 0) Gamma S R hR hn hd.1 hd.2 with
      hlow | hhigh
    next =>
      choose p hp using Finset.mem_biUnion.mp hlow
      have hs := Finset.mem_filter.mp hp.1
      have hi := Finset.mem_range.mp hs.1
      have hp2 := hs.2.1.two_le
      omega
    next => exact hhigh

noncomputable def canonicalOwnerScreen (n : Nat) : Finset Nat :=
  (Finset.range (n+1)).filter Nat.Prime

theorem mem_canonicalOwnerScreen {n p : Nat} :
    Membership.mem (canonicalOwnerScreen n) p <-> Nat.Prime p /\ p <= n := by
  simp only [canonicalOwnerScreen, Finset.mem_filter, Finset.mem_range]
  constructor
  next => exact fun h => And.intro h.2 (by omega)
  next => exact fun h => And.intro (by omega) h.1

noncomputable def canonicalOwnerFamily
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) (n : Nat) (S : Finset Nat) :
    Finset (Prod Nat Nat) :=
  ownerLineFamilyHighFactorCells Gamma n 0 S (canonicalOwnerScreen n)

theorem canonicalOwnerFamily_product_injective
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) (n : Nat) (S : Finset Nat) :
    Set.InjOn (fun x : Prod Nat Nat => x.1*x.2) (canonicalOwnerFamily Gamma n S) := by
  have hcover : forall p, Nat.Prime p -> p%2 = 1 -> p <= n ->
      Membership.mem (canonicalOwnerScreen n) p :=
    fun p hp _ hpn => mem_canonicalOwnerScreen.mpr (And.intro hp hpn)
  have h := screened_small_owner_product_injective (Gamma := Gamma) (n := n)
    (cut := 0) (T := n) (S := S) hcover
  intro x hx y hy he
  exact h (Finset.mem_filter.mpr (And.intro hx (line_family_first_le_index hx)))
    (Finset.mem_filter.mpr (And.intro hy (line_family_first_le_index hy))) he

theorem line_family_joint_eq_canonical
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) {n : Nat} {S R : Finset Nat}
    (hn : 2 <= n) (hS : forall p, Membership.mem S p -> Nat.Prime p)
    (hR : forall p, Membership.mem R p -> 2 <= p)
    (hcut : forall p, Nat.Prime p -> p%2 = 1 -> p*p <= n -> Membership.mem R p) :
    ((ownerLineFamilyHighFactorCells Gamma n 0 S R).card : Real)-
      lineCollisionCredit (ownerLineFamilyHighFactorCells Gamma n 0 S R) =
        ((canonicalOwnerFamily Gamma n S).card : Real) := by
  let G := ownerLineFamilyHighFactorCells Gamma n 0 S R
  let C := canonicalOwnerFamily Gamma n S
  have hcan : forall p, Membership.mem (canonicalOwnerScreen n) p -> 2 <= p :=
    fun p hp => (mem_canonicalOwnerScreen.mp hp).1.two_le
  have himage : G.image (fun x => x.1*x.2) = C.image (fun x => x.1*x.2) :=
    (line_family_image_eq_prefix_composites Gamma hn hS hR).trans
      (line_family_image_eq_prefix_composites Gamma hn hS hcan).symm
  have hcard : (G.image (fun x => x.1*x.2)).card = C.card := by
    rw [himage]
    exact Finset.card_image_iff.mpr (canonicalOwnerFamily_product_injective Gamma n S)
  have hcardR : ((G.image (fun x => x.1*x.2)).card : Real) = (C.card : Real) := by
    exact_mod_cast hcard
  have hnats := Finset.three_fiber_card_identity G (fun x => x.1*x.2)
    (fun m _ => line_family_product_fiber_card_le_three hn hcut m)
  have hr : 3*(G.card : Real) =
      3*((G.image (fun x => x.1*x.2)).card : Real)+
        2*(Finset.imageFiberPairs G (fun x => x.1*x.2) : Real)+
          (Finset.imageDoubleFibers G (fun x => x.1*x.2) : Real) := by
    exact_mod_cast hnats
  change (G.card : Real)-lineCollisionCredit G = (C.card : Real)
  unfold lineCollisionCredit
  linarith only [hr, hcardR]

theorem canonical_owner_first_eq_minFac
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n : Nat} {S : Finset Nat}
    {x : Prod Nat Nat} (hn : 2 <= n)
    (hx : Membership.mem (canonicalOwnerFamily Gamma n S) x) :
    x.1 = (x.1*x.2).minFac := by
  have hp := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1
  have hlo := hc.2.2.1
  have hm2 : 2 <= x.1*x.2 := by nlinarith
  have hprime : Nat.Prime (x.1*x.2).minFac := Nat.minFac_prime (by omega)
  have hle : (x.1*x.2).minFac <= x.1 :=
    Nat.minFac_le_of_dvd hp.2.two_le (dvd_mul_right x.1 x.2)
  have hmem : Membership.mem (canonicalOwnerScreen n) (x.1*x.2).minFac :=
    mem_canonicalOwnerScreen.mpr (And.intro hprime (hle.trans (line_family_first_le_index hx)))
  have hfirst := owner_first_le_of_screened_prime_dvd hprime hmem hx (Nat.minFac_dvd (x.1*x.2))
  exact Nat.le_antisymm hfirst hle

theorem canonical_owner_cofactor_prime_of_cube
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n : Nat} {S : Finset Nat}
    {x : Prod Nat Nat} (hn : 2 <= n)
    (hx : Membership.mem (canonicalOwnerFamily Gamma n S) x)
    (hlarge : n*n+2*n < x.1^3) : Nat.Prime x.2 := by
  have hp := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1
  have hpn := line_family_first_le_index hx
  have hlo : n*n < x.1*x.2 := hc.2.2.1
  have hhi : x.1*x.2 <= n*n+2*n := by
    have h := hc.2.2.2.1
    nlinarith
  have hqn : n < x.2 := by
    by_contra h
    have hm := Nat.mul_le_mul hpn (show x.2 <= n by omega)
    omega
  have hcanon := canonical_owner_first_eq_minFac hn hx
  have hqdiv : Dvd.dvd x.2 (x.1*x.2) := dvd_mul_left x.2 x.1
  by_contra hnot
  choose r hr using exists_minFac_mul (show 2 <= x.2 by omega) hnot
  have hqprime : Nat.Prime x.2.minFac := Nat.minFac_prime (by omega)
  have ha : x.1 <= x.2.minFac := by
    calc
      _ = (x.1*x.2).minFac := hcanon
      _ <= _ := Nat.minFac_le_of_dvd hqprime.two_le
        (dvd_trans (Nat.minFac_dvd x.2) hqdiv)
  have hrd : Dvd.dvd r x.2 := by
    rw [hr.2]
    exact dvd_mul_left r x.2.minFac
  have hb : x.1 <= r := by
    calc
      _ = (x.1*x.2).minFac := hcanon
      _ <= _ := Nat.minFac_le_of_dvd hr.1 (dvd_trans hrd hqdiv)
  have hsq : x.1*x.1 <= x.2 := by
    rw [hr.2]
    exact Nat.mul_le_mul ha hb
  have hcube : x.1^3 <= x.1*x.2 := by
    have h := Nat.mul_le_mul_left x.1 hsq
    nlinarith only [h]
  omega

theorem prime_count_ge_canonical_owner_allowance
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) {n : Nat} (hn : 2 <= n) :
    (384/1001 : Real)*n-31-((canonicalOwnerFamily Gamma n fivePrimePrefix).card : Real) <=
      ((squareIntervalPrimes n).card : Real) := by
  let R := balancedOwnerScreen n
  let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R
  have hR : forall p, Membership.mem R p -> 2 <= p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1.two_le
  have hcut : forall p, Nat.Prime p -> p%2 = 1 -> p*p <= n -> Membership.mem R p :=
    fun p hp ho hs => balancedOwnerScreen_complete hp ho (by omega)
  have hcomp := actual_composites_le_exactPrefixAllowance (Gamma := Gamma) hn hR hcut
  dsimp only at hcomp
  change 2*(n : Real)-((squareIntervalPrimes n).card : Real) <=
    2*(n : Real)-((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+
      (G.card : Real)-lineCollisionCredit G at hcomp
  have hJ := line_family_joint_eq_canonical Gamma hn
    (fun p hp => fivePrimePrefix_prime hp) hR hcut
  have hF := five_prime_prefix_card_lower n
  change (G.card : Real)-lineCollisionCredit G =
    ((canonicalOwnerFamily Gamma n fivePrimePrefix).card : Real) at hJ
  linarith only [hcomp, hJ, hF]

theorem prime_count_ge_canonical_middle_tensor
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) {n : Nat} (hn : 64^78 <= n) :
    let C := canonicalOwnerFamily Gamma n fivePrimePrefix
    (384/1001 : Real)*n-31-((C.filter (fun x => 2*x.1 <= n)).card : Real)-
      balancedTensorLogAllowance n <= ((squareIntervalPrimes n).card : Real) := by
  let C := canonicalOwnerFamily Gamma n fivePrimePrefix
  have h64 : (64 : Nat) <= 64^78 := Nat.le_self_pow (by decide) 64
  have hn2 : 2 <= n := by omega
  have hR : forall p, Nat.Prime p -> p%2 = 1 -> p*p <= 2*n+1 ->
      Membership.mem (canonicalOwnerScreen n) p := by
    intro p hp _ hs
    have hpp := Nat.mul_le_mul_left p hp.two_le
    apply mem_canonicalOwnerScreen.mpr
    exact And.intro hp (by nlinarith)
  have hhigh := screened_balanced_owner_card_le_tensor_log
    (Gamma := Gamma) (T := 0) (S := fivePrimePrefix) hn hR
  change ((C.filter (fun x => n < 2*x.1)).card : Real) <= balancedTensorLogAllowance n at hhigh
  have hsum := Finset.card_filter_add_card_filter_not (s := C) (fun x => n < 2*x.1)
  simp only [not_lt] at hsum
  have hsumR : ((C.filter (fun x => n < 2*x.1)).card : Real)+
      ((C.filter (fun x => 2*x.1 <= n)).card : Real) = (C.card : Real) := by
    exact_mod_cast hsum
  have hP := prime_count_ge_canonical_owner_allowance Gamma hn2
  change (384/1001 : Real)*n-31-(C.card : Real) <= ((squareIntervalPrimes n).card : Real) at hP
  dsimp only
  linarith only [hP, hsumR, hhigh]

end Nat.PrimeSieve
