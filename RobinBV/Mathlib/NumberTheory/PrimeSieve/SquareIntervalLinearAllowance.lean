/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalRoughFibers

/-!
# SquareIntervalLinearAllowance

Explicit finite interval estimates used in signed prime-candidate accounting.
All constants and endpoint conditions are retained; no prime-existence result
is claimed by a negative lower envelope.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

private theorem line_product_mem_odd
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    {x : Prod Nat Nat}
    (hx : Membership.mem (ownerLineFamilyHighFactorCells Gamma n T S R) x) :
    Membership.mem (oddMultiplesInSquare n 1) (x.1*x.2) := by
  have hp := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1
  have hlo := hc.2.2.1
  have hhi := hc.2.2.2.1
  have ho : (x.1*x.2)%2 = 1 := by
    rw [Nat.mul_mod, hc.2.2.2.2.1, hc.2.2.2.2.2.1]
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by nlinarith))
      (And.intro ho (one_dvd _)))) hlo)

/-- Square-root screening replaces the independent harmonic row sum by a linear bound on G. -/
theorem line_family_card_le_three_index
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 2 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem R ell) :
    (ownerLineFamilyHighFactorCells Gamma n T S R).card <= 3*n := by
  let G := ownerLineFamilyHighFactorCells Gamma n T S R
  let O := oddMultiplesInSquare n 1
  have hmap : (G : Set (Prod Nat Nat)).MapsTo (fun x => x.1*x.2) O :=
    fun x hx => line_product_mem_odd hx
  have he := Finset.card_eq_sum_card_fiberwise hmap
  have hc : O.card = n := by
    have h := card_oddMultiplesInSquare n (d := 1) (by decide)
    simp only [Nat.div_one] at h
    dsimp [O]
    omega
  calc
    G.card = O.sum (fun m => (G.filter (fun x => x.1*x.2 = m)).card) := he
    _ <= O.sum (fun _ => 3) := Finset.sum_le_sum (fun m _ =>
      line_family_product_fiber_card_le_three hn hcut m)
    _ = 3*n := by simp [hc, Nat.mul_comm]

private theorem odd_not_three_scaled_card (n : Nat) :
    3*((oddMultiplesInSquare n 1).filter (fun m => Not (Dvd.dvd 3 m))).card <= 2*n+2 := by
  have he : (oddMultiplesInSquare n 1).filter (fun m => Dvd.dvd 3 m) =
      oddMultiplesInSquare n 3 := by
    ext m
    simp only [oddMultiplesInSquare, oddMultiplesUpTo, Finset.mem_filter,
      Finset.mem_range, one_dvd, and_true]
    tauto
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := oddMultiplesInSquare n 1) (fun m => Dvd.dvd 3 m)
  rw [he] at hsplit
  have hodd := card_oddMultiplesInSquare n (d := 1) (by decide)
  simp only [Nat.div_one] at hodd
  have hthree := (count_owner_three_sharp_bounds n).1
  omega

/-- The same complete raw representation bound improves from 3n to 2n+2
when both factors avoid the already selected prime three. -/
theorem line_family_card_le_two_index
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 2 <= n) (h3 : Membership.mem S 3)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem R ell) :
    (ownerLineFamilyHighFactorCells Gamma n T S R).card <= 2*n+2 := by
  let G := ownerLineFamilyHighFactorCells Gamma n T S R
  let O := (oddMultiplesInSquare n 1).filter (fun m => Not (Dvd.dvd 3 m))
  have hmap : (G : Set (Prod Nat Nat)).MapsTo (fun x => x.1*x.2) O := by
    intro x hx
    have hp := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
    have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1
    have hav := hc.2.2.2.2.2.2 3 h3
    apply Finset.mem_filter.mpr
    refine And.intro (line_product_mem_odd hx) ?_
    intro hd
    rcases (show Nat.Prime 3 by decide).dvd_mul.mp hd with hleft | hright
    next => exact hav.1 hleft
    next => exact hav.2 hright
  have he := Finset.card_eq_sum_card_fiberwise hmap
  calc
    G.card = O.sum (fun m => (G.filter (fun x => x.1*x.2 = m)).card) := he
    _ <= O.sum (fun _ => 3) := Finset.sum_le_sum (fun m _ =>
      line_family_product_fiber_card_le_three hn hcut m)
    _ = 3*O.card := by simp [Nat.mul_comm]
    _ <= 2*n+2 := odd_not_three_scaled_card n

/-- A polynomial upper bound for the exact requested signed expression.
The lower estimates for both subtracted corrections are explicitly zero. -/
theorem line_family_signed_allowance_le_two_index
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 2 <= n) (h3 : Membership.mem S 3)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem R ell) :
    let G := ownerLineFamilyHighFactorCells Gamma n T S R
    (G.card : Real) -
      (2*(Finset.imageFiberPairs G (fun x => x.1*x.2) : Real) +
        (Finset.imageDoubleFibers G (fun x => x.1*x.2) : Real))/3 <=
      2*(n : Real)+2 := by
  dsimp only
  have hG : ((ownerLineFamilyHighFactorCells Gamma n T S R).card : Real) <=
      2*(n : Real)+2 := by
    exact_mod_cast line_family_card_le_two_index hn h3 hcut
  have hF : (0 : Real) <=
      (2*(Finset.imageFiberPairs (ownerLineFamilyHighFactorCells Gamma n T S R)
        (fun x => x.1*x.2) : Real) +
        (Finset.imageDoubleFibers (ownerLineFamilyHighFactorCells Gamma n T S R)
          (fun x => x.1*x.2) : Real))/3 := by positivity
  linarith

end Nat.PrimeSieve
