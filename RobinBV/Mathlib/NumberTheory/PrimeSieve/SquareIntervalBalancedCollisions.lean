/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalOwnerPackets
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalRepeatedHyperbola

/-!
# Balanced collision counts

Fix the unpruned owner family, five-prime prefix and balanced square-root
screen. Double fibers inject into the repeated-factor correction and obey a
cubic-root upper bound. Pair incidence equals three times the triple-product
count plus the double-fiber count. No positive uniform lower bound for that
triple-product count or for the interval prime count is asserted.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

noncomputable def balancedUnprunedFamily (n : Nat) : Finset (Prod Nat Nat) :=
  ownerLineFamilyHighFactorCells (fun _ _ => Finset.empty) n 0
    fivePrimePrefix (balancedOwnerScreen n)

theorem balanced_multiple_fiber_avoids_screen {n m : Nat} (hn : 2 <= n)
    (hk : 2 <= ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card) :
    forall ell, Membership.mem (balancedOwnerScreen n) ell -> Not (Dvd.dvd ell m) := by
  let H := (balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)
  change 2 <= H.card at hk
  have hpos : 0 < H.card := by omega
  choose x hx using Finset.card_pos.mp hpos
  have hx' := Finset.mem_filter.mp hx
  have hf := line_family_product_mem_prefix
    (fun ell he => fivePrimePrefix_prime he) hx'.1
  rw [hx'.2] at hf
  have hlo : n*n < m := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
  have hmo : m%2 = 1 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).1).2.1
  intro ell hell hd
  let r := m.minFac
  have hr : Nat.Prime r := Nat.minFac_prime (by nlinarith)
  have hrd : Dvd.dvd r m := Nat.minFac_dvd m
  have he := (Finset.mem_filter.mp hell).2
  have hrel : r <= ell := Nat.minFac_le_of_dvd he.1.two_le hd
  have hro : r%2 = 1 := hr.eq_two_or_odd.resolve_left (by
    intro hh
    rw [hh] at hrd
    have hz := Nat.mod_eq_zero_of_dvd hrd
    omega)
  have hrR : Membership.mem (balancedOwnerScreen n) r :=
    balancedOwnerScreen_complete hr hro
      ((Nat.mul_le_mul hrel hrel).trans he.2.2)
  have hfirst : forall y, Membership.mem H y -> y.1 = r := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp hy'.1).1).2
    have hdiv : Dvd.dvd r (y.1*y.2) := by rw [hy'.2]; exact hrd
    have hylo := owner_first_le_of_screened_prime_dvd hr hrR hy'.1 hdiv
    have hyp : Dvd.dvd y.1 m := by rw [<- hy'.2]; exact dvd_mul_right _ _
    have hrlo : r <= y.1 := Nat.minFac_le_of_dvd hp.two_le hyp
    omega
  have hcard : H.card <= 1 := Finset.card_le_one.mpr (by
    intro y hy z hz
    have hy' := Finset.mem_filter.mp hy
    have hz' := Finset.mem_filter.mp hz
    have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp hy'.1).1).2
    have hefirst : y.1 = z.1 := (hfirst y hy).trans (hfirst z hz).symm
    have heprod := hy'.2.trans hz'.2.symm
    rw [<- hefirst] at heprod
    exact Prod.ext hefirst (Nat.eq_of_mul_eq_mul_left hp.pos heprod))
  omega

theorem balanced_screen_free_medium_cell {n m p : Nat} (hn : 2 <= n)
    (hm : Membership.mem (oddSievedOwnerInSquare n 1 fivePrimePrefix) m)
    (hav : forall ell, Membership.mem (balancedOwnerScreen n) ell -> Not (Dvd.dvd ell m))
    (hp : Membership.mem (mediumPrimeDivisors n m) p) :
    exists q, Membership.mem (balancedUnprunedFamily n) (Prod.mk p q) /\ p*q = m := by
  have hp' := Finset.mem_filter.mp hp
  have hpn : p <= n := by have h := Finset.mem_range.mp hp'.1; omega
  have hprime := hp'.2.1
  choose q hq using hp'.2.2
  have he : p*q = m := hq.symm
  have hm' := Finset.mem_filter.mp hm
  have hsq := Finset.mem_filter.mp hm'.1
  have hup := Finset.mem_filter.mp hsq.1
  have hhi := Finset.mem_range.mp hup.1
  have hqgt : n < q := by
    by_contra hh
    have hmul := Nat.mul_le_mul hpn (show q <= n by omega)
    rw [he] at hmul
    omega
  have hodd : p%2 = 1 /\ q%2 = 1 := by
    have ho := hup.2.1
    rw [<- he, Nat.mul_mod] at ho
    have hpmod := Nat.mod_lt p (by decide : 0 < 2)
    have hqmod := Nat.mod_lt q (by decide : 0 < 2)
    have hpo : p%2 = 1 := by
      by_contra hh
      have hz : p%2 = 0 := by omega
      rw [hz] at ho
      norm_num at ho
    rw [hpo, one_mul] at ho
    simp only [Nat.mod_mod] at ho
    exact And.intro hpo ho
  have hqhi : q < (n+1)*(n+1) := by
    have hp2 := hprime.two_le
    nlinarith
  have havf : forall ell, Membership.mem fivePrimePrefix ell ->
      Not (Dvd.dvd ell p) /\ Not (Dvd.dvd ell q) := by
    intro ell hell
    constructor
    next => intro hd; exact hm'.2.2 ell hell (by rw [<- he]; exact dvd_mul_of_dvd_left hd q)
    next => intro hd; exact hm'.2.2 ell hell (by rw [<- he]; exact dvd_mul_of_dvd_right hd p)
  refine Exists.intro q (And.intro ?_ he)
  apply Finset.mem_filter.mpr
  refine And.intro ?_ ?_
  next =>
    apply Finset.mem_filter.mpr
    refine And.intro ?_ hprime
    apply Finset.mem_filter.mpr
    refine And.intro ?_ ?_
    next =>
      apply Finset.mem_filter.mpr
      exact And.intro
        (Finset.mem_product.mpr (And.intro (Finset.mem_range.mpr (by omega))
          (Finset.mem_range.mpr hqhi)))
        (And.intro hprime.pos (And.intro (by rw [he]; exact hsq.2)
          (And.intro (by rw [he]; nlinarith) (And.intro hodd.1 (And.intro hodd.2 havf)))))
    next =>
      intro ell hell
      constructor
      next => intro hd; exact False.elim (hav ell hell (by rw [<- he]; exact dvd_mul_of_dvd_left hd q))
      next => intro _ hd; exact hav ell hell (by rw [<- he]; exact dvd_mul_of_dvd_right hd p)
  next =>
    intro z hz
    exact False.elim (Finset.notMem_empty z hz)

theorem balanced_screen_free_fiber_card_eq_medium {n m : Nat} (hn : 2 <= n)
    (hm : Membership.mem (oddSievedOwnerInSquare n 1 fivePrimePrefix) m)
    (hav : forall ell, Membership.mem (balancedOwnerScreen n) ell -> Not (Dvd.dvd ell m)) :
    ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card =
      mediumPrimeCount n m := by
  let H := (balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)
  have hinj : Set.InjOn (fun x : Prod Nat Nat => x.1) H := by
    intro y hy z hz hefirst
    have hy' := Finset.mem_filter.mp hy
    have hz' := Finset.mem_filter.mp hz
    have hp := (Finset.mem_filter.mp (Finset.mem_filter.mp hy'.1).1).2
    have heprod := hy'.2.trans hz'.2.symm
    change y.1 = z.1 at hefirst
    rw [<- hefirst] at heprod
    exact Prod.ext hefirst (Nat.eq_of_mul_eq_mul_left hp.pos heprod)
  have himage : H.image (fun x => x.1) = mediumPrimeDivisors n m := by
    ext p
    constructor
    next =>
      intro hp
      choose y hy using Finset.mem_image.mp hp
      have hy' := Finset.mem_filter.mp hy.1
      have hprime := Finset.mem_filter.mp (Finset.mem_filter.mp hy'.1).1
      have hcell := Finset.mem_filter.mp (Finset.mem_filter.mp hprime.1).1
      have hpn := Finset.mem_range.mp (Finset.mem_product.mp hcell.1).1
      rw [<- hy.2]
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr hpn)
        (And.intro hprime.2 (by rw [<- hy'.2]; exact dvd_mul_right _ _)))
    next =>
      intro hp
      choose q hq using balanced_screen_free_medium_cell hn hm hav hp
      exact Finset.mem_image.mpr (Exists.intro (Prod.mk p q)
        (And.intro (Finset.mem_filter.mpr hq) rfl))
  change H.card = (mediumPrimeDivisors n m).card
  rw [<- himage, Finset.card_image_iff.mpr hinj]

theorem balanced_multiple_fiber_card_eq_medium {n m : Nat} (hn : 2 <= n)
    (hk : 2 <= ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card) :
    ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card =
      mediumPrimeCount n m := by
  have hpos : 0 < ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card := by omega
  choose x hx using Finset.card_pos.mp hpos
  have hx' := Finset.mem_filter.mp hx
  have hm := line_family_product_mem_prefix
    (fun ell he => fivePrimePrefix_prime he) hx'.1
  rw [hx'.2] at hm
  exact balanced_screen_free_fiber_card_eq_medium hn hm
    (balanced_multiple_fiber_avoids_screen hn hk)

theorem balanced_multiple_fiber_rough {n m : Nat} (hn : 2 <= n)
    (hk : 2 <= ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card) :
    Membership.mem (squareRoughSurvivors n) m := by
  by_contra hh
  have hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem (balancedOwnerScreen n) ell := by
    intro ell hp ho hs
    exact balancedOwnerScreen_complete hp ho (by omega)
  have hsmall := line_family_nonrough_fiber_card_le_one
    (Gamma := fun _ _ => Finset.empty) (T := 0) (S := fivePrimePrefix) hn hcut hh
  change ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card <= 1 at hsmall
  omega

/-- Actual double fibers of the fixed unpruned balanced family inject into
the previously studied repeated-factor correction. -/
theorem balanced_double_fibers_le_two_distinct {n : Nat} (hn : 2 <= n) :
    Finset.imageDoubleFibers (balancedUnprunedFamily n) (fun x => x.1*x.2) <=
      (twoDistinctSurvivors n).card := by
  unfold Finset.imageDoubleFibers
  apply Finset.card_le_card
  intro m hm
  have hk := (Finset.mem_filter.mp hm).2
  change ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card = 2 at hk
  have hk2 : 2 <= ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card := by
    omega
  apply Finset.mem_filter.mpr
  refine And.intro (balanced_multiple_fiber_rough hn hk2) ?_
  rw [<- balanced_multiple_fiber_card_eq_medium hn hk2]
  exact hk

/-- Complete parameter-free bound on N2 for this exact screen and geometry. -/
theorem balanced_double_fibers_le_cubic_root {n : Nat} (hn : 2 <= n) :
    Finset.imageDoubleFibers (balancedUnprunedFamily n) (fun x => x.1*x.2) <=
      Nat.nthRoot 3 (n*n+2*n)+1-Nat.sqrt n :=
  (balanced_double_fibers_le_two_distinct hn).trans
    (card_twoDistinctSurvivors_le_cubic_root n)

noncomputable def balancedTripleProducts (n : Nat) : Finset Nat :=
  (oddSievedOwnerInSquare n 1 fivePrimePrefix).filter (fun m =>
    (forall ell, Membership.mem (balancedOwnerScreen n) ell -> Not (Dvd.dvd ell m)) /\
      mediumPrimeCount n m = 3)

theorem balanced_triple_fibers_eq_products {n : Nat} (hn : 2 <= n) :
    (((balancedUnprunedFamily n).image (fun x => x.1*x.2)).filter
      (fun m => ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card = 3)) =
        balancedTripleProducts n := by
  ext m
  constructor
  next =>
    intro hm
    have hm' := Finset.mem_filter.mp hm
    have heq := hm'.2
    change ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card = 3 at heq
    choose x hx using Finset.mem_image.mp hm'.1
    have hf := line_family_product_mem_prefix (fun ell he => fivePrimePrefix_prime he) hx.1
    rw [hx.2] at hf
    have hk : 2 <= ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card := by omega
    apply Finset.mem_filter.mpr
    refine And.intro hf (And.intro (balanced_multiple_fiber_avoids_screen hn hk) ?_)
    rw [<- balanced_multiple_fiber_card_eq_medium hn hk]
    exact heq
  next =>
    intro hm
    have hm' := Finset.mem_filter.mp hm
    have he := balanced_screen_free_fiber_card_eq_medium hn hm'.1 hm'.2.1
    rw [hm'.2.2] at he
    have hpos : 0 < ((balancedUnprunedFamily n).filter (fun x => x.1*x.2 = m)).card := by omega
    choose x hx using Finset.card_pos.mp hpos
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_image.mpr (Exists.intro x (Finset.mem_filter.mp hx))) he)

theorem balanced_pair_count_eq_triples_add_double {n : Nat} (hn : 2 <= n) :
    Finset.imageFiberPairs (balancedUnprunedFamily n) (fun x => x.1*x.2) =
      3*(balancedTripleProducts n).card+
        Finset.imageDoubleFibers (balancedUnprunedFamily n) (fun x => x.1*x.2) := by
  let G := balancedUnprunedFamily n
  let I := G.image (fun x => x.1*x.2)
  let k := fun m => (G.filter (fun x => x.1*x.2 = m)).card
  have hthree : forall m, k m <= 3 := by
    intro m
    apply line_family_product_fiber_card_le_three hn
    intro ell hp ho hs
    exact balancedOwnerScreen_complete hp ho (by omega)
  have hpoint : forall m, (k m).choose 2 =
      3*(if k m = 3 then 1 else 0)+(if k m = 2 then 1 else 0) := by
    intro m
    have hk := hthree m
    have hc : k m = 0 \/ k m = 1 \/ k m = 2 \/ k m = 3 := by omega
    rcases hc with h | h | h | h <;> simp [h]
  have ht : I.sum (fun m => if k m = 3 then (1 : Nat) else 0) =
      (balancedTripleProducts n).card := by
    rw [Finset.sum_boole]
    exact congrArg Finset.card (balanced_triple_fibers_eq_products hn)
  have hd : I.sum (fun m => if k m = 2 then (1 : Nat) else 0) =
      Finset.imageDoubleFibers G (fun x => x.1*x.2) := by
    rw [Finset.sum_boole]
    rfl
  change I.sum (fun m => (k m).choose 2) = _
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, <- Finset.mul_sum, ht, hd]

/-- Explicit joint logarithmic upper envelope. This is not a positive lower
bound on either collision count. -/
theorem balanced_pair_and_double_le_explicit_log {n : Nat} (hn : 4 <= n) :
    (Finset.imageFiberPairs (balancedUnprunedFamily n) (fun x => x.1*x.2) : Real)+
      2*(Finset.imageDoubleFibers (balancedUnprunedFamily n) (fun x => x.1*x.2) : Real) <=
        12*(n : Real)/(Real.log n-2*Real.log (Real.log n))+
          3*(n : Real)/(Real.log n)^2 := by
  let G := balancedUnprunedFamily n
  have hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem (balancedOwnerScreen n) ell := by
    intro ell hp ho hs
    exact balancedOwnerScreen_complete hp ho (by omega)
  have hc := Finset.imageFiberPairs_add_twice_double_le_three_support G
    (fun x => x.1*x.2) (squareRoughSurvivors n)
    (fun m => line_family_product_fiber_card_le_three (by omega : 2 <= n) hcut m)
    (fun m hm => line_family_nonrough_fiber_card_le_one (by omega : 2 <= n) hcut hm)
  have hcr : (Finset.imageFiberPairs G (fun x => x.1*x.2) : Real)+
      2*(Finset.imageDoubleFibers G (fun x => x.1*x.2) : Real) <=
        3*((squareRoughSurvivors n).card : Real) := by exact_mod_cast hc
  have hh := card_squareRoughSurvivors_le_explicit_log hn
  unfold Real.squareSieveDenominator at hh
  change (Finset.imageFiberPairs G (fun x => x.1*x.2) : Real)+
    2*(Finset.imageDoubleFibers G (fun x => x.1*x.2) : Real) <= _
  have hs := _root_.mul_le_mul_of_nonneg_left hh (by norm_num : (0 : Real) <= 3)
  have he : 3*(4*(n : Real)/(Real.log n-2*Real.log (Real.log n))+
      (n : Real)/(Real.log n)^2) =
      12*(n : Real)/(Real.log n-2*Real.log (Real.log n))+3*(n : Real)/(Real.log n)^2 := by ring
  rw [he] at hs
  exact hcr.trans hs

/-- Exact positive credit, with the cubic-scale N2 term separated. -/
theorem balanced_collision_credit_eq_triples_add_double {n : Nat} (hn : 2 <= n) :
    lineCollisionCredit (balancedUnprunedFamily n) =
      2*((balancedTripleProducts n).card : Real)+
        (Finset.imageDoubleFibers (balancedUnprunedFamily n) (fun x => x.1*x.2) : Real) := by
  have hnats := balanced_pair_count_eq_triples_add_double hn
  have hr : (Finset.imageFiberPairs (balancedUnprunedFamily n) (fun x => x.1*x.2) : Real) =
      3*((balancedTripleProducts n).card : Real)+
        (Finset.imageDoubleFibers (balancedUnprunedFamily n) (fun x => x.1*x.2) : Real) := by
    exact_mod_cast hnats
  unfold lineCollisionCredit
  linarith only [hr]

/-- End-to-end secondary coefficient ledger. Both analytic estimates are
explicit hypotheses: this theorem does not supply a positive triple count. -/
theorem balanced_prime_count_ge_given_secondary_bounds {n : Nat} (hn : 2 <= n)
    (a b Eg Et : Real)
    (hG : ((balancedUnprunedFamily n).card : Real) <=
      (384/1001 : Real)*n+b*(n : Real)/Real.log n+Eg)
    (hT : a*(n : Real)/Real.log n-Et <= ((balancedTripleProducts n).card : Real)) :
    (2*a-b)*(n : Real)/Real.log n-Eg-2*Et-31 <=
      ((squareIntervalPrimes n).card : Real) := by
  have hR : forall ell, Membership.mem (balancedOwnerScreen n) ell -> 2 <= ell := by
    intro ell he
    exact (Finset.mem_filter.mp he).2.1.two_le
  have hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem (balancedOwnerScreen n) ell := by
    intro ell hp ho hs
    exact balancedOwnerScreen_complete hp ho (by omega)
  have hc := actual_composites_le_exactPrefixAllowance
    (Gamma := fun _ _ => Finset.empty) hn hR hcut
  dsimp only at hc
  change 2*(n : Real)-((squareIntervalPrimes n).card : Real) <=
    2*(n : Real)-((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+
      ((balancedUnprunedFamily n).card : Real)-lineCollisionCredit (balancedUnprunedFamily n) at hc
  have hF := five_prime_prefix_card_lower n
  have hK := balanced_collision_credit_eq_triples_add_double hn
  have hN : (0 : Real) <=
      (Finset.imageDoubleFibers (balancedUnprunedFamily n) (fun x => x.1*x.2) : Real) :=
    Nat.cast_nonneg _
  have he : (2*a-b)*(n : Real)/Real.log n-Eg-2*Et-31 =
      2*(a*(n : Real)/Real.log n)-b*(n : Real)/Real.log n-Eg-2*Et-31 := by ring
  rw [he]
  linarith only [hc, hF, hK, hN, hG, hT]

/-- Pointwise ceiling on the complete positive credit in this geometry. -/
theorem balanced_credit_add_double_le_explicit_log {n : Nat} (hn : 4 <= n) :
    lineCollisionCredit (balancedUnprunedFamily n)+
      (Finset.imageDoubleFibers (balancedUnprunedFamily n) (fun x => x.1*x.2) : Real) <=
        8*(n : Real)/(Real.log n-2*Real.log (Real.log n))+2*(n : Real)/(Real.log n)^2 := by
  have h := balanced_pair_and_double_le_explicit_log hn
  calc
    _ = (2/3 : Real)*
        ((Finset.imageFiberPairs (balancedUnprunedFamily n) (fun x => x.1*x.2) : Real)+
          2*(Finset.imageDoubleFibers (balancedUnprunedFamily n) (fun x => x.1*x.2) : Real)) := by
      unfold lineCollisionCredit
      ring
    _ <= (2/3 : Real)*(12*(n : Real)/(Real.log n-2*Real.log (Real.log n))+
        3*(n : Real)/(Real.log n)^2) :=
      _root_.mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

/-- Even exact collision counts cannot make the retired coarse envelope
positive. This is a ceiling for that envelope, not for the actual prime count. -/
theorem balanced_coarse_credit_margin_nonpositive {n : Nat} (hn : 4 <= n) :
    lineCollisionCredit (balancedUnprunedFamily n)-
      (8*(n : Real)/(Real.log n-2*Real.log (Real.log n))+2*(n : Real)/(Real.log n)^2) <=
        -(Finset.imageDoubleFibers (balancedUnprunedFamily n) (fun x => x.1*x.2) : Real) := by
  have h := balanced_credit_add_double_le_explicit_log hn
  linarith only [h]

end Nat.PrimeSieve
