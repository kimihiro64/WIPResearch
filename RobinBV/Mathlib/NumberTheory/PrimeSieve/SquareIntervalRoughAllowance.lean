/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalLinearAllowance

/-!
# SquareIntervalRoughAllowance

Explicit finite interval estimates used in signed prime-candidate accounting.
All constants and endpoint conditions are retained; no prime-existence result
is claimed by a negative lower envelope.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

theorem line_family_nonrough_fiber_card_le_one
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T m : Nat} {S R : Finset Nat}
    (hn : 2 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem R ell)
    (hm : Not (Membership.mem (squareRoughSurvivors n) m)) :
    ((ownerLineFamilyHighFactorCells Gamma n T S R).filter
      (fun x => x.1*x.2 = m)).card <= 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  have hcanon : forall z, Membership.mem (ownerLineFamilyHighFactorCells Gamma n T S R) z ->
      z.1*z.2 = m -> z.1 = m.minFac := by
    intro z hz hzm
    by_contra hh
    have hne : Not ((z.1*z.2).minFac = z.1) := by
      rw [hzm]
      exact fun he => hh he.symm
    have hr := rough_of_screened_false_owner hn hcut hz hne
    rw [hzm] at hr
    exact hm hr
  have he : x.1 = y.1 := (hcanon x hx'.1 hx'.2).trans (hcanon y hy'.1 hy'.2).symm
  have hp : Nat.Prime x.1 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hx'.1).1).2
  have hprod := hx'.2.trans hy'.2.symm
  rw [<- he] at hprod
  exact Prod.ext he (Nat.eq_of_mul_eq_mul_left hp.pos hprod)

theorem line_family_product_mem_prefix
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell)
    {x : Prod Nat Nat}
    (hx : Membership.mem (ownerLineFamilyHighFactorCells Gamma n T S R) x) :
    Membership.mem (oddSievedOwnerInSquare n 1 S) (x.1*x.2) := by
  have hp := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1
  have hlo := hc.2.2.1
  have hhi := hc.2.2.2.1
  have ho : (x.1*x.2)%2 = 1 := by
    rw [Nat.mul_mod, hc.2.2.2.2.1, hc.2.2.2.2.2.1]
  apply Finset.mem_filter.mpr
  refine And.intro ?_ (And.intro (one_dvd _) ?_)
  next =>
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by nlinarith))
        (And.intro ho (one_dvd _)))) hlo)
  next =>
    intro ell hell hd
    have hav := hc.2.2.2.2.2.2 ell hell
    exact ((hS ell hell).dvd_mul.mp hd).elim hav.1 hav.2

/-- Only rough products can contribute the two additional representations.
This bounds the raw cell count before discarding either signed correction. -/
theorem line_family_card_le_prefix_add_two_rough
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 2 <= n)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem R ell) :
    (ownerLineFamilyHighFactorCells Gamma n T S R).card <=
      (oddSievedOwnerInSquare n 1 S).card+2*(squareRoughSurvivors n).card := by
  let G := ownerLineFamilyHighFactorCells Gamma n T S R
  let F := oddSievedOwnerInSquare n 1 S
  let H := squareRoughSurvivors n
  have hmap : (G : Set (Prod Nat Nat)).MapsTo (fun x => x.1*x.2) F :=
    fun x hx => line_family_product_mem_prefix hS hx
  have hpoint : forall m, Membership.mem F m ->
      (G.filter (fun x => x.1*x.2 = m)).card <=
        1+2*(if Membership.mem H m then 1 else 0) := by
    intro m _
    by_cases hm : Membership.mem H m
    next => simpa [hm] using line_family_product_fiber_card_le_three hn hcut m
    next => simpa [hm] using line_family_nonrough_fiber_card_le_one hn hcut hm
  have hind : F.sum (fun m => if Membership.mem H m then (1 : Nat) else 0) =
      (F.filter (fun m => Membership.mem H m)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hsub : F.filter (fun m => Membership.mem H m) <= H := by
    intro m hm
    exact (Finset.mem_filter.mp hm).2
  calc
    G.card = F.sum (fun m => (G.filter (fun x => x.1*x.2 = m)).card) :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ <= F.sum (fun m => 1+2*(if Membership.mem H m then 1 else 0)) :=
      Finset.sum_le_sum hpoint
    _ = F.card+2*(F.filter (fun m => Membership.mem H m)).card := by
      rw [Finset.sum_add_distrib, <- Finset.mul_sum, hind]
      simp
    _ <= F.card+2*H.card := by
      have hc := Finset.card_le_card hsub
      omega

end Nat.PrimeSieve
