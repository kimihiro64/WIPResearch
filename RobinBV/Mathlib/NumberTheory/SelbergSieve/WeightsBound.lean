/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.SelbergSieve.DownsetMass
import RobinBV.Mathlib.NumberTheory.SelbergSieve.WeightFormula

/-!
# WeightsBound

Finite Selberg sieve input, proved from Mathlib primitives.
The classical sieve argument follows D. R. Heath-Brown, Lectures on sieves,
Sections 2-3 (https://arxiv.org/abs/math/0209360).
No prime-distribution or unproved analytic hypothesis is introduced.
-/

set_option autoImplicit false
open scoped Classical
namespace BoundingSieve

theorem finiteSelbergWeights_eq_zero_of_not_mem (s : BoundingSieve) (D : Finset Nat)
    (hD : forall e, Membership.mem D e -> Dvd.dvd e s.prodPrimes)
    (hdown : forall e, Membership.mem D e -> forall k, Dvd.dvd k e -> Membership.mem D k)
    {d : Nat} (hd : Dvd.dvd d s.prodPrimes) (hnot : Not (Membership.mem D d)) :
    s.finiteSelbergWeights D d = 0 := by
  rw [s.finiteSelbergWeights_explicit D hD hd]
  have hz : D.sum (fun e => if Dvd.dvd d e then s.selbergTerms e else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    exact if_neg (fun hde => hnot (hdown e he d hde))
  rw [hz, mul_zero]

/-- The constructed optimizer really has weights of absolute value at mostone.
No weight-size estimate is installed as an assumption. -/
theorem finiteSelbergWeights_abs_le_one (s : BoundingSieve) (D : Finset Nat)
    (hD : forall e, Membership.mem D e -> Dvd.dvd e s.prodPrimes)
    (hdown : forall e, Membership.mem D e -> forall k, Dvd.dvd k e -> Membership.mem D k)
    (h1 : Membership.mem D 1) {d : Nat} (hd : Dvd.dvd d s.prodPrimes) :
    abs (s.finiteSelbergWeights D d) <= 1 := by
  have hH := s.finiteSelbergDenominator_pos D hD h1
  have hH0 : Not (s.finiteSelbergDenominator D = 0) := ne_of_gt hH
  have hn : (0 : Real) <= Inv.inv (s.nu d) :=
    inv_nonneg.mpr (le_of_lt (s.nu_pos_of_dvd_prodPrimes hd))
  have htail : (0 : Real) <= D.sum (fun e => if Dvd.dvd d e then s.selbergTerms e else 0) := by
    apply Finset.sum_nonneg
    intro e he
    by_cases hde : Dvd.dvd d e
    next => simpa only [if_pos hde] using le_of_lt (s.selbergTerms_pos (hD e he))
    next => simp [hde]
  have hmu : abs (ArithmeticFunction.moebius d : Real) = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (s.squarefree_of_dvd_prodPrimes hd)
  have hmass := s.finiteSelberg_upper_divisor_mass D hD hdown hd
  rw [s.finiteSelbergWeights_explicit D hD hd, abs_mul, abs_div, abs_mul,
    hmu, abs_of_nonneg hn, abs_of_nonneg (le_of_lt hH), abs_of_nonneg htail, one_mul]
  calc
    Inv.inv (s.nu d)/s.finiteSelbergDenominator D *
        D.sum (fun e => if Dvd.dvd d e then s.selbergTerms e else 0) =
      (Inv.inv (s.nu d)*D.sum (fun e => if Dvd.dvd d e then s.selbergTerms e else 0))*
        Inv.inv (s.finiteSelbergDenominator D) := by ring
    _ <= s.finiteSelbergDenominator D*Inv.inv (s.finiteSelbergDenominator D) :=
      _root_.mul_le_mul_of_nonneg_right hmass (inv_nonneg.mpr (le_of_lt hH))
    _ = 1 := by simp [hH0]

/-- The complete weight L1 cost is at most the actual finite support size. -/
theorem sum_abs_finiteSelbergWeights_le_card (s : BoundingSieve) (D : Finset Nat)
    (hD : forall e, Membership.mem D e -> Dvd.dvd e s.prodPrimes)
    (hdown : forall e, Membership.mem D e -> forall k, Dvd.dvd k e -> Membership.mem D k)
    (h1 : Membership.mem D 1) :
    s.prodPrimes.divisors.sum (fun d => abs (s.finiteSelbergWeights D d)) <= (D.card : Real) := by
  have hsub : D <= s.prodPrimes.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr (And.intro (hD d hd) s.prodPrimes_ne_zero)
  calc
    s.prodPrimes.divisors.sum (fun d => abs (s.finiteSelbergWeights D d)) =
        D.sum (fun d => abs (s.finiteSelbergWeights D d)) := by
      symm
      apply Finset.sum_subset hsub
      intro d hd hnot
      rw [s.finiteSelbergWeights_eq_zero_of_not_mem D hD hdown (Nat.dvd_of_mem_divisors hd) hnot]
      exact abs_zero
    _ <= D.sum (fun _ => (1 : Real)) := Finset.sum_le_sum
      (fun d hd => s.finiteSelbergWeights_abs_le_one D hD hdown h1 (hD d hd))
    _ = (D.card : Real) := by simp

end BoundingSieve
