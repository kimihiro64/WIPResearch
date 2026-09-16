/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalLogAllowance

/-!
# SquareIntervalPrimeLogBound

Explicit finite interval estimates used in signed prime-candidate accounting.
All constants and endpoint conditions are retained; no prime-existence result
is claimed by a negative lower envelope.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

private theorem fivePrimePrefix_dvd_period {p : Nat}
    (hp : Membership.mem fivePrimePrefix p) : Dvd.dvd p 15015 := by
  simp only [fivePrimePrefix, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem lowClockOwners_zero (S : Finset Nat) :
    lowClockOwners S 0 = Finset.empty := by
  apply Finset.ext
  intro p
  have hnot : Not (Membership.mem (lowClockOwners S 0) p) := by
    intro hp
    have hd := Finset.mem_filter.mp hp
    have hi := Finset.mem_range.mp hd.1
    have hp2 := hd.2.1.two_le
    omega
  simp [hnot, Finset.empty]

/-- Actual composites are bounded by the full exact-prefix signed allowance.
No measured prime count or prime-existence hypothesis supplies an estimate. -/
theorem actual_composites_le_exactPrefixAllowance
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n : Nat} {R : Finset Nat}
    (hn : 2 <= n)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R
    2*(n : Real)-((squareIntervalPrimes n).card : Real) <=
      exactPrefixCompositeAllowance n G := by
  have hc := prefix_survivors_line_collision_bound (n := n) (T := 0) (W := 15015)
    Gamma fivePrimePrefix R hR hcut hn (by norm_num)
    (fun ell he => fivePrimePrefix_dvd_period he)
  dsimp only at hc
  simp only [lowClockOwners_zero, Finset.empty] at hc
  let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R
  have hcr : 3*((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+
      2*(Finset.imageFiberPairs G (fun x => x.1*x.2) : Real)+
      (Finset.imageDoubleFibers G (fun x => x.1*x.2) : Real) <=
        3*((squareIntervalPrimes n).card : Real)+3*(G.card : Real) := by
    exact_mod_cast hc
  dsimp only
  unfold exactPrefixCompositeAllowance lineCollisionCredit
  change _ <= 2*(n : Real)-((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+
    (G.card : Real)-(2*(Finset.imageFiberPairs G (fun x => x.1*x.2) : Real)+
      (Finset.imageDoubleFibers G (fun x => x.1*x.2) : Real))/3
  linarith only [hcr]

/-- End-to-end prime lower bound: the exact positive prefix cancels only
after the actual representation count receives the explicit analytic bound. -/
theorem prime_count_ge_collision_sub_log
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n : Nat} {R : Finset Nat}
    (hn : 4 <= n)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R
    lineCollisionCredit G-roughLogAllowance n <= ((squareIntervalPrimes n).card : Real) := by
  have hcomp := actual_composites_le_exactPrefixAllowance (Gamma := Gamma)
    (by omega : 2 <= n) hR hcut
  have hbound := exactPrefixCompositeAllowance_le_log (Gamma := Gamma) (T := 0) hn hcut
  dsimp only at hcomp hbound
  dsimp only
  linarith only [hcomp, hbound]

/-- A fully closed logarithmic lower envelope for the actual prime count.
Its proof uses the complete analytic allowance, not prime-count nonnegativity. -/
theorem prime_count_ge_explicit_log {n : Nat} (hn : 4 <= n) :
    -8*(n : Real)/(Real.log n-2*Real.log (Real.log n))-
      2*(n : Real)/(Real.log n)^2 <= ((squareIntervalPrimes n).card : Real) := by
  let R := (Finset.range (n+1)).filter Nat.Prime
  let Gamma : Nat -> Nat -> Finset (Prod Nat Nat) := fun _ _ => Finset.empty
  have hR : forall ell, Membership.mem R ell -> 2 <= ell := by
    intro ell he
    exact (Finset.mem_filter.mp he).2.two_le
  have hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell := by
    intro ell hp _ hs
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_range.mpr ?_) hp
    have hp2 := hp.two_le
    nlinarith
  have hp := prime_count_ge_collision_sub_log (Gamma := Gamma) hn hR hcut
  have hcredit := lineCollisionCredit_nonneg
    (ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R)
  dsimp only at hp
  unfold roughLogAllowance Real.squareSieveDenominator at hp
  have he : -8*(n : Real)/(Real.log n-2*Real.log (Real.log n)) =
      -(8*(n : Real)/(Real.log n-2*Real.log (Real.log n))) := by ring
  rw [he]
  linarith only [hp, hcredit]

/-- The exact previously proposed on-paper formula, now supplied with a real
proof through a stronger exact-prefix composite allowance. -/
theorem prime_count_ge_promised_log {n : Nat} (hn : 169 <= n) :
    -8*(n : Real)/(Real.log n-2*Real.log (Real.log n))-
      2*(n : Real)/(Real.log n)^2-(36683/1001 : Real) <=
        ((squareIntervalPrimes n).card : Real) := by
  have h := prime_count_ge_explicit_log (by omega : 4 <= n)
  linarith only [h]

end Nat.PrimeSieve
