/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.SelbergSieve.FiniteWeights

/-!
# WeightFormula

Finite Selberg sieve input, proved from Mathlib primitives.
The classical sieve argument follows D. R. Heath-Brown, Lectures on sieves,
Sections 2-3 (https://arxiv.org/abs/math/0209360).
No prime-distribution or unproved analytic hypothesis is introduced.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat

theorem moebius_quotient_mul_of_squarefree {d e : Nat}
    (hs : Squarefree e) (hd : Dvd.dvd d e) :
    ArithmeticFunction.moebius (e/d)*ArithmeticFunction.moebius e =
      ArithmeticFunction.moebius d := by
  have hcop : Nat.Coprime d (e/d) := Nat.coprime_of_squarefree_mul (by
    rw [Nat.mul_div_cancel' hd]
    exact hs)
  have he := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  rw [Nat.mul_div_cancel' hd] at he
  have hsq := ArithmeticFunction.moebius_sq_eq_one_of_squarefree
    (Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hd) hs)
  calc
    ArithmeticFunction.moebius (e/d)*ArithmeticFunction.moebius e =
        ArithmeticFunction.moebius d*(ArithmeticFunction.moebius (e/d))^2 := by
      rw [he]
      ring
    _ = ArithmeticFunction.moebius d := by rw [hsq, mul_one]

end Nat

namespace BoundingSieve

theorem finiteSelbergWeights_explicit (s : BoundingSieve) (D : Finset Nat)
    (hD : forall e, Membership.mem D e -> Dvd.dvd e s.prodPrimes)
    {d : Nat} (hd : Dvd.dvd d s.prodPrimes) :
    s.finiteSelbergWeights D d =
      (ArithmeticFunction.moebius d : Real)*Inv.inv (s.nu d)/
        s.finiteSelbergDenominator D *
          D.sum (fun e => if Dvd.dvd d e then s.selbergTerms e else 0) := by
  have hP : 0 < s.prodPrimes := Nat.pos_of_ne_zero s.prodPrimes_ne_zero
  have hsub : D <= s.prodPrimes.divisors := by
    intro e he
    exact Nat.mem_divisors.mpr (And.intro (hD e he) s.prodPrimes_ne_zero)
  have hsum : Nat.upperDivisorMobius s.prodPrimes (s.finiteSelbergDiagonal D) d =
      (ArithmeticFunction.moebius d : Real)/s.finiteSelbergDenominator D *
        D.sum (fun e => if Dvd.dvd d e then s.selbergTerms e else 0) := by
    rw [Nat.upperDivisorMobius_eq_sum_quotient hP hd]
    calc
      s.prodPrimes.divisors.sum (fun e => if Dvd.dvd d e then
          (ArithmeticFunction.moebius (e/d) : Real)*s.finiteSelbergDiagonal D e else 0) =
        D.sum (fun e => if Dvd.dvd d e then
          (ArithmeticFunction.moebius (e/d) : Real)*s.finiteSelbergDiagonal D e else 0) := by
        symm
        apply Finset.sum_subset hsub
        intro e _ he
        simp [finiteSelbergDiagonal, he]
      _ = D.sum (fun e => (ArithmeticFunction.moebius d : Real)/s.finiteSelbergDenominator D *
          (if Dvd.dvd d e then s.selbergTerms e else 0)) := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases hde : Dvd.dvd d e
        next =>
          have hmu : (ArithmeticFunction.moebius (e/d) : Real)*
              (ArithmeticFunction.moebius e : Real) = (ArithmeticFunction.moebius d : Real) := by
            exact_mod_cast Nat.moebius_quotient_mul_of_squarefree
              (s.squarefree_of_dvd_prodPrimes (hD e he)) hde
          simp only [if_pos hde, finiteSelbergDiagonal, if_pos he]
          calc
            (ArithmeticFunction.moebius (e/d) : Real)*
                ((ArithmeticFunction.moebius e : Real)*s.selbergTerms e/
                  s.finiteSelbergDenominator D) =
              ((ArithmeticFunction.moebius (e/d) : Real)*(ArithmeticFunction.moebius e : Real))*
                s.selbergTerms e/s.finiteSelbergDenominator D := by ring
            _ = (ArithmeticFunction.moebius d : Real)/s.finiteSelbergDenominator D*
                s.selbergTerms e := by rw [hmu]; ring
        next => simp [hde]
      _ = (ArithmeticFunction.moebius d : Real)/s.finiteSelbergDenominator D *
          D.sum (fun e => if Dvd.dvd d e then s.selbergTerms e else 0) := by
        rw [Finset.mul_sum]
  unfold finiteSelbergWeights
  rw [hsum]
  ring

theorem finiteSelbergWeights_one (s : BoundingSieve) (D : Finset Nat)
    (hD : forall e, Membership.mem D e -> Dvd.dvd e s.prodPrimes)
    (h1 : Membership.mem D 1) : s.finiteSelbergWeights D 1 = 1 := by
  have hH0 : Not (s.finiteSelbergDenominator D = 0) :=
    ne_of_gt (s.finiteSelbergDenominator_pos D hD h1)
  rw [s.finiteSelbergWeights_explicit D hD (one_dvd _)]
  simp only [Nat.div_one, ArithmeticFunction.moebius_apply_one, Int.cast_one,
    s.nu_mult.map_one, inv_one, one_mul, one_dvd, if_true]
  change (1/s.finiteSelbergDenominator D)*s.finiteSelbergDenominator D = 1
  field_simp

end BoundingSieve
