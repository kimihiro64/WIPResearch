/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Nat.ModEq
import RobinBV.Mathlib.NumberTheory.PrimeSieve.Scaled

/-!
# Prime-owner masses in arithmetic progressions

The weighted least-prime-owner packet transports exactly to its scaled
cofactors. Cancelling the owner prime changes the modulus by its gcd with
that prime; no coprimality hypothesis is silently imposed. The cofactor one
and repeated occurrences of the owner prime are retained.

These are finite identities, not distribution estimates. In particular, they
do not assert uniformity across inadmissible residue classes.
-/

set_option autoImplicit false

namespace Nat

/-- Exact two-way cancellation, including the noncoprime modulus. -/
theorem modEq_mul_iff_modEq_div_gcd {q p m b : Nat} (hq : 0 < q) :
    ModEq q (p * m) (p * b) <-> ModEq (q / gcd q p) m b := by
  constructor
  . exact ModEq.cancel_left_div_gcd hq
  . intro h
    have hdq : gcd q p * (q / gcd q p) = q :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left q p)
    have hdp : p / gcd q p * gcd q p = p :=
      Nat.div_mul_cancel (Nat.gcd_dvd_right q p)
    have hscaled : ModEq q (gcd q p * m) (gcd q p * b) := by
      simpa only [hdq] using h.mul_left' (gcd q p)
    simpa only [<- Nat.mul_assoc, hdp] using hscaled.mul_left (p / gcd q p)

namespace PrimeSieve

noncomputable section

/-- An arbitrary owner progression transports without any cancellation.
This form also handles residue classes not divisible by the local gcd. -/
theorem sum_ownerProgression_eq_scaledCongruence
    {A : Type*} [AddCommMonoid A] (F : Nat -> A)
    {p U : Nat} (hp : Nat.Prime p) (q a : Nat) :
    Finset.sum ((leastPrimeOwnerPacketAt p U).filter (fun n => ModEq q n a)) F =
      Finset.sum ((leastPrimeOwnerScaledCofactorsBefore p U).filter
        (fun m => ModEq q (p * m) a)) (fun m => F (p * m)) := by
  classical
  simp only [Finset.sum_filter]
  exact sum_leastPrimeOwnerPacketAt_eq_scaledCofactors
    (fun n => if ModEq q n a then F n else 0) hp

/-- The complete progression-weighted owner identity, with the exact
gcd-adjusted cofactor modulus. This accepts real or complex weights. -/
theorem sum_ownerProgression_eq_scaledCofactorProgression
    {A : Type*} [AddCommMonoid A] (F : Nat -> A)
    {p q U : Nat} (hp : Nat.Prime p) (hq : 0 < q) (b : Nat) :
    Finset.sum ((leastPrimeOwnerPacketAt p U).filter
        (fun n => ModEq q n (p * b))) F =
      Finset.sum ((leastPrimeOwnerScaledCofactorsBefore p U).filter
        (fun m => ModEq (q / gcd q p) m b)) (fun m => F (p * m)) := by
  classical
  rw [sum_ownerProgression_eq_scaledCongruence F hp q (p * b)]
  simp only [Nat.modEq_mul_iff_modEq_div_gcd hq]

/-- Equality between the integer residue and its least-prime-owner residue
is the cofactor-one progression, not generally the cofactor-one class mod q. -/
theorem sum_ownerMatchingResidue_eq_cofactorOne
    {A : Type*} [AddCommMonoid A] (F : Nat -> A)
    {p q U : Nat} (hp : Nat.Prime p) (hq : 0 < q) :
    Finset.sum ((leastPrimeOwnerPacketAt p U).filter
        (fun n => ModEq q n p)) F =
      Finset.sum ((leastPrimeOwnerScaledCofactorsBefore p U).filter
        (fun m => ModEq (q / gcd q p) m 1)) (fun m => F (p * m)) := by
  simpa only [Nat.mul_one] using
    sum_ownerProgression_eq_scaledCofactorProgression F hp hq 1

/-- A residue not divisible by the local gcd contains no integers owned by p.
This is a local obstruction, not an error term to be averaged by BV. -/
theorem ownerProgression_eq_empty_of_not_gcd_dvd
    {p q U a : Nat} (ha : Not (Dvd.dvd (gcd q p) a)) :
    (leastPrimeOwnerPacketAt p U).filter (fun n => ModEq q n a) =
      Finset.empty := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro n hn hcong
  have hpn : Dvd.dvd p n := (Finset.mem_filter.mp hn).2
  have hgn : Dvd.dvd (gcd q p) n := (Nat.gcd_dvd_right q p).trans hpn
  exact ha ((hcong.dvd_iff (Nat.gcd_dvd_left q p)).mp hgn)

end

end PrimeSieve
end Nat
