/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalPrimitiveLine

/-!
# SquareIntervalRoughFibers

Explicit finite interval estimates used in signed prime-candidate accounting.
All constants and endpoint conditions are retained; no prime-existence result
is claimed by a negative lower envelope.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- A false owner surviving a complete square-root screen represents a rough integer.
The screening cutoff is a finite set of actual primes, not a density assumption. -/
theorem rough_of_screened_false_owner
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T p v : Nat} {S R : Finset Nat}
    (hn : 2 <= n)
    (hR : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell)
    (hc : Membership.mem (ownerLineFamilyHighFactorCells Gamma n T S R) (Prod.mk p v))
    (hne : Not ((p*v).minFac = p)) :
    Membership.mem (squareRoughSurvivors n) (p*v) := by
  classical
  have hprimeCell := Finset.mem_filter.mp (Finset.mem_filter.mp hc).1
  have howner := Finset.mem_filter.mp hprimeCell.1
  have hcell := Finset.mem_filter.mp howner.1
  have hp : Nat.Prime p := hprimeCell.2
  have hlo : n*n < p*v := hcell.2.2.1
  have hhi : p*v < (n+1)*(n+1) := hcell.2.2.2.1
  have hpo : p%2 = 1 := hcell.2.2.2.2.1
  have hvo : v%2 = 1 := hcell.2.2.2.2.2.1
  have hm2 : 2 <= p*v := by nlinarith
  have hmo : (p*v)%2 = 1 := by rw [Nat.mul_mod, hpo, hvo]
  let r := (p*v).minFac
  have hr : Nat.Prime r := Nat.minFac_prime (by omega)
  have hrd : Dvd.dvd r (p*v) := Nat.minFac_dvd (p*v)
  have hrp : r < p := by
    have hl : r <= p := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p v)
    change Not (r = p) at hne
    omega
  have hrv : Dvd.dvd r v := by
    rcases hr.dvd_mul.mp hrd with hleft | hright
    next =>
      have he : r = p := (hp.eq_one_or_self_of_dvd r hleft).resolve_left hr.ne_one
      omega
    next => exact hright
  have hro : r%2 = 1 := hr.eq_two_or_odd.resolve_left (by
    intro he
    rw [he] at hrd
    have hz := Nat.mod_eq_zero_of_dvd hrd
    omega)
  have hcut : n < r*r := by
    by_contra hh
    have hrr : r*r <= n := by omega
    exact (howner.2 r (hR r hr hro hrr)).2 hrp hrv
  have hrough : forall t, Nat.Prime t -> Dvd.dvd t (p*v) -> n < t*t := by
    intro t ht htd
    have hrt : r <= t := Nat.minFac_le_of_dvd ht.two_le htd
    have hm := Nat.mul_le_mul hrt hrt
    omega
  exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr hhi)
    (And.intro hm2 (And.intro hlo (And.intro hmo hrough))))

/-- A rough integer with a nonminimal medium prime divisor has exactly three
prime factors. The already proved semiprime divisor identity rules out pq. -/
theorem rough_false_medium_owner_three {n m p : Nat}
    (hm : Membership.mem (squareRoughSurvivors n) m)
    (hp : Nat.Prime p) (hpn : p <= n) (hpd : Dvd.dvd p m)
    (hne : Not (m.minFac = p)) : IsThreePrime m := by
  classical
  have hd := Finset.mem_filter.mp hm
  have hlo := hd.2.2.1
  have hhi := Finset.mem_range.mp hd.1
  have hpmem : Membership.mem (mediumPrimeDivisors n m) p :=
    Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega)) (And.intro hp hpd))
  have hminp : Nat.Prime m.minFac := Nat.minFac_prime (by have := hd.2.1; omega)
  have hminle : m.minFac <= p := Nat.minFac_le_of_dvd hp.two_le hpd
  have hminmem : Membership.mem (mediumPrimeDivisors n m) m.minFac :=
    Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
      (And.intro hminp (Nat.minFac_dvd m)))
  rcases rough_prime_or_two_or_three hd.2.1 hhi hd.2.2.2.2 with hprime | htwo | hthree
  next =>
    rw [mediumPrimeDivisors_prime hprime hlo] at hpmem
    exact False.elim (Finset.notMem_empty p hpmem)
  next =>
    choose a b ha hb hab he using htwo
    have hset : mediumPrimeDivisors n m = {a} := by
      rw [he]
      exact mediumPrimeDivisors_two ha hb hab (by rw [<- he]; exact hlo)
        (by rw [<- he]; exact hhi)
    rw [hset] at hpmem hminmem
    exact False.elim (hne ((Finset.mem_singleton.mp hminmem).trans
      (Finset.mem_singleton.mp hpmem).symm))
  next => exact hthree

/-- Every excess cell of the actual geometric family is a rough three-prime
configuration once the complete square-root owner cutoff has been applied. -/
theorem line_family_false_owner_is_rough_three
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T p v : Nat} {S R : Finset Nat}
    (hn : 2 <= n)
    (hR : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell)
    (hc : Membership.mem (ownerLineFamilyHighFactorCells Gamma n T S R) (Prod.mk p v))
    (hne : Not ((p*v).minFac = p)) :
    Membership.mem (squareRoughSurvivors n) (p*v) /\ IsThreePrime (p*v) := by
  have hm := rough_of_screened_false_owner hn hR hc hne
  have hprimeCell := Finset.mem_filter.mp (Finset.mem_filter.mp hc).1
  have hcell := Finset.mem_filter.mp (Finset.mem_filter.mp hprimeCell.1).1
  have hpn : p <= n := by
    have h := Finset.mem_range.mp (Finset.mem_product.mp hcell.1).1
    omega
  exact And.intro hm (rough_false_medium_owner_three hm hprimeCell.2 hpn
    (dvd_mul_right p v) hne)

/-- Every product fiber of the screened geometric family has at most three cells. -/
theorem line_family_product_fiber_card_le_three
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 2 <= n)
    (hR : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell)
    (m : Nat) :
    ((ownerLineFamilyHighFactorCells Gamma n T S R).filter
      (fun x => x.1*x.2 = m)).card <= 3 := by
  classical
  let F := (ownerLineFamilyHighFactorCells Gamma n T S R).filter (fun x => x.1*x.2 = m)
  have hinj : Set.InjOn (fun x : Prod Nat Nat => x.1) F := by
    intro x hx y hy hxy
    change x.1 = y.1 at hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hp : Nat.Prime x.1 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx'.1).1).2
    have he := hx'.2.trans hy'.2.symm
    rw [<- hxy] at he
    exact Prod.ext hxy (Nat.eq_of_mul_eq_mul_left hp.pos he)
  by_cases hm : Membership.mem (squareRoughSurvivors n) m
  next =>
    have hsub : F.image (fun x => x.1) <= mediumPrimeDivisors n m := by
      intro q hq
      choose x hx using Finset.mem_image.mp hq
      have hx' := Finset.mem_filter.mp hx.1
      have hp := Finset.mem_filter.mp (Finset.mem_filter.mp hx'.1).1
      have hcell := Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1
      have hpn := Finset.mem_range.mp (Finset.mem_product.mp hcell.1).1
      have hdiv : Dvd.dvd x.1 m := by rw [<- hx'.2]; exact dvd_mul_right x.1 x.2
      rw [<- hx.2]
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr hpn) (And.intro hp.2 hdiv))
    have he := Finset.card_image_iff.mpr hinj
    have hle := Finset.card_le_card hsub
    have hthree := mediumPrimeCount_le_three hm
    change (mediumPrimeDivisors n m).card <= 3 at hthree
    change F.card <= 3
    omega
  next =>
    have hcanonical : forall x, Membership.mem F x -> x.1 = m.minFac := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      by_contra hh
      have hne : Not ((x.1*x.2).minFac = x.1) := by
        rw [hx'.2]
        exact fun he => hh he.symm
      have hr := rough_of_screened_false_owner hn hR hx'.1 hne
      rw [hx'.2] at hr
      exact hm hr
    have hle : F.card <= 1 := Finset.card_le_one.mpr (by
      intro x hx y hy
      exact hinj hx hy ((hcanonical x hx).trans (hcanonical y hy).symm))
    change F.card <= 3
    omega

end Nat.PrimeSieve

namespace Finset

/-- Positive pair incidence of equal-image elements, with its finite support explicit. -/
noncomputable def imageFiberPairs {A B : Type*} [DecidableEq B]
    (s : Finset A) (f : A -> B) : Nat :=
  (s.image f).sum (fun b => ((s.filter (fun a => f a = b)).card).choose 2)

/-- The exact residual defect in the degree-three collision formula. -/
noncomputable def imageDoubleFibers {A B : Type*} [DecidableEq B]
    (s : Finset A) (f : A -> B) : Nat :=
  ((s.image f).filter (fun b => (s.filter (fun a => f a = b)).card = 2)).card

theorem sum_card_image_fibers {A B : Type*} [DecidableEq B]
    (s : Finset A) (f : A -> B) :
    (s.image f).sum (fun b => (s.filter (fun a => f a = b)).card) = s.card := by
  classical
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp [Finset.mem_image_of_mem f ha]

/-- Exact signed collision accounting for fibers of sizes one, two and three. -/
theorem three_fiber_card_identity {A B : Type*} [DecidableEq B]
    (s : Finset A) (f : A -> B)
    (hthree : forall b, Membership.mem (s.image f) b ->
      (s.filter (fun a => f a = b)).card <= 3) :
    3*s.card = 3*(s.image f).card+2*imageFiberPairs s f+imageDoubleFibers s f := by
  classical
  have hpoint : forall b, Membership.mem (s.image f) b ->
      3*(s.filter (fun a => f a = b)).card =
        3+2*((s.filter (fun a => f a = b)).card).choose 2+
          (if (s.filter (fun a => f a = b)).card = 2 then 1 else 0) := by
    intro b hb
    have hk := hthree b hb
    have hk0 : 0 < (s.filter (fun a => f a = b)).card := by
      choose a ha using Finset.mem_image.mp hb
      exact Finset.card_pos.mpr (Exists.intro a (Finset.mem_filter.mpr ha))
    have he : (s.filter (fun a => f a = b)).card = 1 \/
        (s.filter (fun a => f a = b)).card = 2 \/
        (s.filter (fun a => f a = b)).card = 3 := by omega
    rcases he with he | he | he
    all_goals rw [he]; decide
  have hconst : (s.image f).sum (fun _ => (3 : Nat)) = 3*(s.image f).card := by
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  have hpairs : (s.image f).sum (fun b => 2*((s.filter (fun a => f a = b)).card).choose 2) =
      2*imageFiberPairs s f := by unfold imageFiberPairs; rw [Finset.mul_sum]
  have hdouble : (s.image f).sum (fun b =>
      if (s.filter (fun a => f a = b)).card = 2 then 1 else 0) = imageDoubleFibers s f := by
    unfold imageDoubleFibers
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    3*s.card = (s.image f).sum (fun b => 3*(s.filter (fun a => f a = b)).card) := by
      rw [<- Finset.mul_sum, sum_card_image_fibers]
    _ = (s.image f).sum (fun b => 3+2*((s.filter (fun a => f a = b)).card).choose 2+
        (if (s.filter (fun a => f a = b)).card = 2 then 1 else 0)) :=
      Finset.sum_congr rfl hpoint
    _ = 3*(s.image f).card+2*imageFiberPairs s f+imageDoubleFibers s f := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hconst, hpairs, hdouble]

/-- The positive pair correction is retained before bounding the double-fiber defect. -/
theorem three_fiber_image_card_bound {A B : Type*} [DecidableEq B]
    (s : Finset A) (f : A -> B)
    (hthree : forall b, Membership.mem (s.image f) b ->
      (s.filter (fun a => f a = b)).card <= 3) :
    3*(s.image f).card+2*imageFiberPairs s f <= 3*s.card := by
  have h := three_fiber_card_identity s f hthree
  omega

end Finset

namespace Nat.PrimeSieve

/-- Keep the product image in the existing cover, before relaxing its multiplicity. -/
theorem prefix_survivors_le_prime_owner_line_image {n T W : Nat}
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    (oddSievedOwnerInSquare n 1 S).card <= (squareIntervalPrimes n).card +
      (lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) +
      ((ownerLineFamilyHighFactorCells Gamma n T S R).image (fun x => x.1*x.2)).card := by
  classical
  let F := oddSievedOwnerInSquare n 1 S
  let B := F.filter (fun m => Not (Nat.Prime m))
  let rows := (lowClockOwners S T).biUnion (fun p => oddSievedOwnerInSquare n p S)
  let cells := (ownerLineFamilyHighFactorCells Gamma n T S R).image (fun x => x.1*x.2)
  have hsub : B <= Union.union rows cells := by
    intro m hm
    have hd := Finset.mem_filter.mp hm
    exact Finset.mem_union.mpr
      (prefix_composite_mem_owner_or_line_family Gamma S R hR hn hd.1 hd.2)
  have hrows : rows.card <= (lowClockOwners S T).sum
      (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) := by
    have h1 : rows.card <= (lowClockOwners S T).sum
        (fun p => (oddSievedOwnerInSquare n p S).card) := Finset.card_biUnion_le
    apply h1.trans
    apply Finset.sum_le_sum
    intro p hp
    exact card_oddSievedOwner_le_windowCapacity S (Finset.mem_filter.mp hp).2.2.1 hW0 hW
  have hbad : B.card <= rows.card+cells.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le rows cells)
  have hprime : (F.filter Nat.Prime).card <= (squareIntervalPrimes n).card := by
    apply Finset.card_le_card
    intro m hm
    have hd := Finset.mem_filter.mp hm
    have hs := Finset.mem_filter.mp hd.1
    have hi := Finset.mem_filter.mp hs.1
    have hu := Finset.mem_filter.mp hi.1
    have htop := Finset.mem_range.mp hu.1
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by nlinarith))
      (And.intro hi.2 hd.2))
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) Nat.Prime
  change _+B.card = F.card at hsplit
  change F.card <= _
  dsimp only [cells] at hbad
  omega

/-- The complete signed correction feeds the same prime-candidate bound. -/
theorem prefix_survivors_line_collision_bound {n T W : Nat}
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    let G := ownerLineFamilyHighFactorCells Gamma n T S R
    3*(oddSievedOwnerInSquare n 1 S).card+
      2*Finset.imageFiberPairs G (fun x => x.1*x.2)+
      Finset.imageDoubleFibers G (fun x => x.1*x.2) <=
        3*(squareIntervalPrimes n).card+
          3*(lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p))+
          3*G.card := by
  classical
  let G := ownerLineFamilyHighFactorCells Gamma n T S R
  have hcover := prefix_survivors_le_prime_owner_line_image (T := T) Gamma S R hR hn hW0 hW
  have hid := Finset.three_fiber_card_identity G (fun x => x.1*x.2)
    (fun m _ => line_family_product_fiber_card_le_three hn hcut m)
  change 3*(oddSievedOwnerInSquare n 1 S).card+
      2*Finset.imageFiberPairs G (fun x => x.1*x.2)+
      Finset.imageDoubleFibers G (fun x => x.1*x.2) <= _
  dsimp only [G] at hid
  dsimp only [G]
  omega

/-- Finite-clock prime-count enclosure with every positive collision term retained. -/
theorem prime_count_line_collision_clock_bound {n T W : Nat}
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell /\ ell%2 = 1)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    let G := ownerLineFamilyHighFactorCells Gamma n T S R
    3*(oddOwnerProductDrift S*(n : Int)+prefixClockMinimum S)+
      (oddOwnerPeriod 1 S : Int)*
        (2*(Finset.imageFiberPairs G (fun x => x.1*x.2) : Int)+
          (Finset.imageDoubleFibers G (fun x => x.1*x.2) : Int)) <=
      (oddOwnerPeriod 1 S : Int)*
        (3*((squareIntervalPrimes n).card : Int)+
          3*((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
          3*(G.card : Int)) := by
  classical
  let G := ownerLineFamilyHighFactorCells Gamma n T S R
  have hpref := prefixClockMinimum_le_defect S n hS
  have hcover := prefix_survivors_line_collision_bound (T := T) Gamma S R hR hcut hn hW0 hW
  have hcast : 3*((oddSievedOwnerInSquare n 1 S).card : Int)+
      2*(Finset.imageFiberPairs G (fun x => x.1*x.2) : Int)+
      (Finset.imageDoubleFibers G (fun x => x.1*x.2) : Int) <=
        3*((squareIntervalPrimes n).card : Int)+
          3*((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
          3*(G.card : Int) := by exact_mod_cast hcover
  have hscale := _root_.mul_le_mul_of_nonneg_left hcast
    (show (0 : Int) <= oddOwnerPeriod 1 S by omega)
  dsimp only
  change 3*(oddOwnerProductDrift S*(n : Int)+prefixClockMinimum S)+
      (oddOwnerPeriod 1 S : Int)*
        (2*(Finset.imageFiberPairs G (fun x => x.1*x.2) : Int)+
          (Finset.imageDoubleFibers G (fun x => x.1*x.2) : Int)) <= _
  nlinarith

end Nat.PrimeSieve
