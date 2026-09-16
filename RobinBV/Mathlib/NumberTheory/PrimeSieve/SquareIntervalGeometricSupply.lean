/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalBalancedOwner
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalPrimeLogBound

/-!
# Geometric positive-supply assembly

The original candidate supply is retained against independently bounded
balanced owner cells. Lower owners and exact collision corrections remain
explicit. This is not a completed uniform positive prime-count estimate.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- The repaired full consumer keeps the existing positive prefix supply and
every collision credit, on one matched screen. The lower-owner count is
explicitly retained, NOT claimed to have a new closed analytic estimate. -/
theorem prime_count_ge_balanced_geometric_allowance
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) {n : Nat} (hn : 9 <= n) :
    let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix (balancedOwnerScreen n)
    (384/1001 : Real)*n-31-
      ((G.filter (fun x => 2*x.1 <= n)).card : Real)-
        balancedPrimeLogAllowance n+lineCollisionCredit G <=
          ((squareIntervalPrimes n).card : Real) := by
  let R := balancedOwnerScreen n
  let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R
  let low := G.filter (fun x => 2*x.1 <= n)
  let high := G.filter (fun x => n < 2*x.1)
  have hR : forall ell, Membership.mem R ell -> 2 <= ell := by
    intro ell he
    exact (Finset.mem_filter.mp he).2.1.two_le
  have hcomplete : forall ell, Nat.Prime ell -> ell%2 = 1 ->
      ell*ell <= 2*n+1 -> Membership.mem R ell := by
    intro ell hp ho hs
    exact balancedOwnerScreen_complete hp ho hs
  have hcut : forall ell, Nat.Prime ell -> ell%2 = 1 ->
      ell*ell <= n -> Membership.mem R ell := by
    intro ell hp ho hs
    exact hcomplete ell hp ho (by omega)
  have hcomp := actual_composites_le_exactPrefixAllowance (Gamma := Gamma)
    (by omega : 2 <= n) hR hcut
  dsimp only at hcomp
  change 2*(n : Real)-((squareIntervalPrimes n).card : Real) <=
    2*(n : Real)-((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+
      (G.card : Real)-lineCollisionCredit G at hcomp
  have hsplit : high.card+low.card = G.card := by
    have h := Finset.card_filter_add_card_filter_not (s := G) (fun x => n < 2*x.1)
    have he : G.filter (fun x => Not (n < 2*x.1)) = low := by
      change G.filter (fun x => Not (n < 2*x.1)) = G.filter (fun x => 2*x.1 <= n)
      simp only [not_lt]
    rw [he] at h
    exact h
  have hsplitR : (high.card : Real)+(low.card : Real) = (G.card : Real) := by
    exact_mod_cast hsplit
  have hhigh : (high.card : Real) <= balancedPrimeLogAllowance n :=
    screened_balanced_owner_card_le_explicit_log hn hcomplete
  have hF := five_prime_prefix_card_lower n
  change (384/1001 : Real)*n-31-(low.card : Real)-
    balancedPrimeLogAllowance n+lineCollisionCredit G <= _
  linarith only [hcomp, hsplitR, hhigh, hF]

/-- Bound every raw representation, not the product image or an unknown
prime count, by the three-representation theorem and the full prefix packet. -/
theorem line_family_card_le_three_prefix
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 2 <= n)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem R ell) :
    (ownerLineFamilyHighFactorCells Gamma n T S R).card <=
      3*(oddSievedOwnerInSquare n 1 S).card := by
  let G := ownerLineFamilyHighFactorCells Gamma n T S R
  let F := oddSievedOwnerInSquare n 1 S
  have hmap : (G : Set (Prod Nat Nat)).MapsTo (fun x => x.1*x.2) F :=
    fun x hx => line_family_product_mem_prefix hS hx
  calc
    G.card = F.sum (fun m => (G.filter (fun x => x.1*x.2 = m)).card) :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ <= F.sum (fun _ => 3) := Finset.sum_le_sum (fun m _ =>
      line_family_product_fiber_card_le_three hn hcut m)
    _ = 3*F.card := by simp [Nat.mul_comm]

/-- A complete independent linear bound for G on the same balanced screen.
The two collision corrections can subsequently be bounded below by zero. -/
theorem line_family_card_le_five_prefix_linear
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat}
    (hn : 2 <= n) :
    ((ownerLineFamilyHighFactorCells Gamma n T fivePrimePrefix
      (balancedOwnerScreen n)).card : Real) <= (1152/1001 : Real)*n+93 := by
  have hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem (balancedOwnerScreen n) ell := by
    intro ell hp ho hs
    exact balancedOwnerScreen_complete hp ho (by omega)
  have hG := line_family_card_le_three_prefix (Gamma := Gamma) (T := T) hn
    (fun ell he => fivePrimePrefix_prime he) hcut
  have hGr : ((ownerLineFamilyHighFactorCells Gamma n T fivePrimePrefix
      (balancedOwnerScreen n)).card : Real) <=
      3*((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real) := by
    exact_mod_cast hG
  have hF := five_prime_prefix_card_upper n
  linarith only [hGr, hF]

/-- Full supply-preserving prime lower bound. Its right-hand estimate contains
no unevaluated owner, collision, prime, or floor count. This negative envelope
does not prove prime existence and is not claimed stronger than the log bound. -/
theorem prime_count_ge_complete_prefix_linear {n : Nat} (hn : 2 <= n) :
    (384/1001 : Real)*n-31-((1152/1001 : Real)*n+93) <=
      ((squareIntervalPrimes n).card : Real) := by
  let Gamma : Nat -> Nat -> Finset (Prod Nat Nat) := fun _ _ => Finset.empty
  let R := balancedOwnerScreen n
  let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R
  have hR : forall ell, Membership.mem R ell -> 2 <= ell := by
    intro ell he
    exact (Finset.mem_filter.mp he).2.1.two_le
  have hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem R ell := by
    intro ell hp ho hs
    exact balancedOwnerScreen_complete hp ho (by omega)
  have hcomp := actual_composites_le_exactPrefixAllowance (Gamma := Gamma) hn hR hcut
  dsimp only at hcomp
  change 2*(n : Real)-((squareIntervalPrimes n).card : Real) <=
    2*(n : Real)-((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+
      (G.card : Real)-lineCollisionCredit G at hcomp
  have hG : (G.card : Real) <= (1152/1001 : Real)*n+93 :=
    line_family_card_le_five_prefix_linear hn
  have hF := five_prime_prefix_card_lower n
  have hK := lineCollisionCredit_nonneg G
  linarith only [hcomp, hG, hF, hK]

/-- Keeping the same prefix count coupled until the last step avoids charging
its rounding error twice. The full lower envelope improves by exactly 62. -/
theorem prime_count_ge_complete_prefix_joint_linear {n : Nat} (hn : 2 <= n) :
    -(768/1001 : Real)*n-62 <= ((squareIntervalPrimes n).card : Real) := by
  let Gamma : Nat -> Nat -> Finset (Prod Nat Nat) := fun _ _ => Finset.empty
  let R := balancedOwnerScreen n
  let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R
  let F := oddSievedOwnerInSquare n 1 fivePrimePrefix
  have hR : forall ell, Membership.mem R ell -> 2 <= ell := by
    intro ell he
    exact (Finset.mem_filter.mp he).2.1.two_le
  have hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n ->
      Membership.mem R ell := by
    intro ell hp ho hs
    exact balancedOwnerScreen_complete hp ho (by omega)
  have hcomp := actual_composites_le_exactPrefixAllowance (Gamma := Gamma) hn hR hcut
  dsimp only at hcomp
  change 2*(n : Real)-((squareIntervalPrimes n).card : Real) <=
    2*(n : Real)-(F.card : Real)+(G.card : Real)-lineCollisionCredit G at hcomp
  have hG := line_family_card_le_three_prefix (Gamma := Gamma) (T := 0) hn
    (fun ell he => fivePrimePrefix_prime he) hcut
  have hGr : (G.card : Real) <= 3*(F.card : Real) := by exact_mod_cast hG
  have hF : (F.card : Real) <= (384/1001 : Real)*n+31 :=
    five_prime_prefix_card_upper n
  have hK := lineCollisionCredit_nonneg G
  linarith only [hcomp, hGr, hF, hK]

end Nat.PrimeSieve
