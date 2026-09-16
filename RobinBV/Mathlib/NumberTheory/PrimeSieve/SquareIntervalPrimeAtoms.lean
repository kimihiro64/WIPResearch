/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Nat.PrimeFin
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalFifthIncidence

/-!
# Actual fixed-prime atoms in corrected square-interval moments

All products lie in the original interval and retain the full larger-owner
exclusion history. The large prime makes distinct fixed-factor packets disjoint.
No prime-density estimate or existence of a nonempty packet is assumed.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- A bounded fixed factor forces the complementary interval factor above the index. -/
theorem square_atom_large_prime {n D p : Nat} (hD : D<=n) (hlo : n*n<D*p) : n<p := by
  by_contra hc
  have h := Nat.mul_le_mul hD (show p<=n by omega)
  omega

/-- An actual prime atom satisfies every large-owner exclusion on the moment support. -/
theorem square_prime_atom_mem {n z D p : Nat} (hn : 2<=n) (hD : D<=n)
    (hodd : D%2=1) (hsmall : forall r, Membership.mem D.primeFactors r -> r<=z)
    (hp : Nat.Prime p) (hlo : n*n<D*p) (hhi : D*p<(n+1)*(n+1)) :
    Membership.mem (squareMomentSurvivors n z) (D*p) := by
  have hlarge := square_atom_large_prime hD hlo
  have hpodd := hp.eq_two_or_odd.resolve_left (show Not (p=2) by omega)
  have hD0 : Not (D=0) := by omega
  apply mem_squareMomentSurvivors.mpr
  refine And.intro hhi (And.intro hlo (And.intro ?_ ?_))
  next => rw [Nat.mul_mod, hodd, hpodd]
  next =>
    intro r hr hd
    have hdta := Finset.mem_filter.mp hr
    have hrn := Finset.mem_range.mp hdta.1
    rcases hdta.2.1.dvd_mul.mp hd with hrD | hrp
    next =>
      have hrz := hsmall r (Nat.mem_primeFactors.mpr
        (And.intro hdta.2.1 (And.intro hrD hD0)))
      omega
    next =>
      have heq := (Nat.prime_dvd_prime_iff_eq hdta.2.1 hp).mp hrp
      omega

/-- The small-prime multiplicity of an actual atom is exactly that of its fixed factor. -/
theorem square_prime_atom_multiplicity {n z D p : Nat} (hz : z<=n) (hD : D<=n)
    (hodd : D%2=1) (hsmall : forall r, Membership.mem D.primeFactors r -> r<=z)
    (hp : Nat.Prime p) (hlo : n*n<D*p) :
    squareMomentMultiplicity z (D*p)=D.primeFactors.card := by
  have hlarge := square_atom_large_prime hD hlo
  have hD0 : Not (D=0) := by omega
  unfold squareMomentMultiplicity
  apply congrArg Finset.card
  ext r
  constructor
  next =>
    intro hr
    have hmem := Finset.mem_filter.mp hr
    have hdta := Finset.mem_filter.mp hmem.1
    have hrz := Finset.mem_range.mp hdta.1
    apply Nat.mem_primeFactors.mpr
    refine And.intro hdta.2.1 (And.intro ?_ hD0)
    rcases hdta.2.1.dvd_mul.mp hmem.2 with hrD | hrp
    next => exact hrD
    next =>
      have heq := (Nat.prime_dvd_prime_iff_eq hdta.2.1 hp).mp hrp
      omega
  next =>
    intro hr
    have hdta := Nat.mem_primeFactors.mp hr
    have hrz := hsmall r hr
    have hro : r%2=1 := by
      apply hdta.1.eq_two_or_odd.resolve_left
      intro heq
      have hd := hdta.2.1
      rw [heq] at hd
      have hzero := Nat.mod_eq_zero_of_dvd hd
      omega
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
      (And.intro hdta.1 (And.intro hro (by have h2:=hdta.1.two_le; omega))))) ?_
    exact dvd_mul_of_dvd_left hdta.2.1 p

/-- A sufficiently large prime uniquely identifies its atom representation. -/
theorem square_prime_atoms_unique {n D E p q : Nat} (hE : 0<E)
    (hEn : E<=n) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpn : n<p) (heq : D*p=E*q) : D=E /\ p=q := by
  have hdiv : Dvd.dvd p (E*q) := by rw [<- heq]; exact dvd_mul_left p D
  have hpq : p=q := by
    rcases hp.dvd_mul.mp hdiv with hpE | hpq
    next => have hle := Nat.le_of_dvd hE hpE; omega
    next => exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  refine And.intro ?_ hpq
  rw [hpq] at heq
  exact Nat.eq_of_mul_eq_mul_right hq.pos heq

/-- Every admissible fixed-factor prime packet injects into its actual multiplicity class. -/
theorem card_square_prime_atoms_le_multiplicity {n z D : Nat} (hn : 2<=n) (hz : z<=n)
    (hD : D<=n) (hodd : D%2=1)
    (hsmall : forall r, Membership.mem D.primeFactors r -> r<=z)
    (t : Finset Nat) (ht : forall p, Membership.mem t p ->
      Nat.Prime p /\ n*n<D*p /\ D*p<(n+1)*(n+1)) :
    t.card <= ((squareMomentSurvivors n z).filter
      (fun m => squareMomentMultiplicity z m=D.primeFactors.card)).card := by
  apply Finset.card_le_card_of_injOn (fun p => D*p)
  next =>
    intro p hp
    have h := ht p hp
    exact Finset.mem_filter.mpr (And.intro
      (square_prime_atom_mem hn hD hodd hsmall h.1 h.2.1 h.2.2)
      (square_prime_atom_multiplicity hz hD hodd hsmall h.1 h.2.1))
  next =>
    intro p hp q hq heq
    exact Nat.eq_of_mul_eq_mul_left (show 0<D by omega) heq

/-- A complete finite family of distinct fixed-factor packets gives a joint cardinal lower bound. -/
theorem sum_card_square_prime_atoms_le_multiplicity {n z k : Nat}
    (hn : 2<=n) (hz : z<=n) (s : Finset Nat) (t : Nat -> Finset Nat)
    (hs : forall D, Membership.mem s D -> D<=n /\ D%2=1 /\ D.primeFactors.card=k /\
      forall r, Membership.mem D.primeFactors r -> r<=z)
    (ht : forall D, Membership.mem s D -> forall p, Membership.mem (t D) p ->
      Nat.Prime p /\ n*n<D*p /\ D*p<(n+1)*(n+1)) :
    s.sum (fun D => (t D).card) <=
      ((squareMomentSurvivors n z).filter (fun m => squareMomentMultiplicity z m=k)).card := by
  let images : Nat -> Finset Nat := fun D => (t D).image (fun p => D*p)
  have hdisj : (s : Set Nat).PairwiseDisjoint images := by
    intro D hD E hE hne
    apply Finset.disjoint_left.mpr
    intro m hmD hmE
    choose p hp using Finset.mem_image.mp hmD
    choose q hq using Finset.mem_image.mp hmE
    have hDp := ht D hD p hp.1
    have hEq := ht E hE q hq.1
    have hDdata := hs D hD
    have hEdata := hs E hE
    have huniq := square_prime_atoms_unique (show 0<E by omega) hEdata.1 hDp.1 hEq.1
      (square_atom_large_prime hDdata.1 hDp.2.1) (hp.2.trans hq.2.symm)
    exact hne huniq.1
  have hcards : s.sum (fun D => (t D).card)=s.sum (fun D => (images D).card) := by
    apply Finset.sum_congr rfl
    intro D hD
    have hDdata := hs D hD
    have hinj : Function.Injective (fun p : Nat => D*p) := by
      intro p q heq
      exact Nat.eq_of_mul_eq_mul_left (show 0<D by omega) heq
    exact (Finset.card_image_of_injective (t D) hinj).symm
  rw [hcards, <- Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro m hm
  choose D hD using Finset.mem_biUnion.mp hm
  choose p hp using Finset.mem_image.mp hD.2
  have hDdata := hs D hD.1
  have hpdata := ht D hD.1 p hp.1
  rw [<- hp.2]
  apply Finset.mem_filter.mpr
  refine And.intro
    (square_prime_atom_mem hn hDdata.1 hDdata.2.1 hDdata.2.2.2 hpdata.1 hpdata.2.1 hpdata.2.2) ?_
  rw [square_prime_atom_multiplicity hz hDdata.1 hDdata.2.1 hDdata.2.2.2 hpdata.1 hpdata.2.1]
  exact hDdata.2.2.1

end Nat.PrimeSieve
