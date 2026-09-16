/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.SelbergSieve
import RobinBV.Mathlib.NumberTheory.SelbergSieve.DualMobius

/-!
# FiniteWeights

Finite Selberg sieve input, proved from Mathlib primitives.
The classical sieve argument follows D. R. Heath-Brown, Lectures on sieves,
Sections 2-3 (https://arxiv.org/abs/math/0209360).
No prime-distribution or unproved analytic hypothesis is introduced.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat

theorem upperDivisorMobius_eq_sum_quotient {P d : Nat}
    (hP : 0 < P) (hd : Dvd.dvd d P) (f : Nat -> Real) :
    upperDivisorMobius P f d =
      P.divisors.sum (fun e =>
        if Dvd.dvd d e then (ArithmeticFunction.moebius (e/d) : Real)*f e else 0) := by
  rw [sum_divisors_above_eq_complement hP hd]
  unfold upperDivisorMobius divisorMobiusTransform
  change (P/d).divisorsAntidiagonal.sum (fun x =>
    (ArithmeticFunction.moebius x.1 : Real)*f (P/x.2)) = _
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a b =>
    (ArithmeticFunction.moebius a : Real)*f (P/b))]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Nat.div_div_eq_div_mul, Nat.mul_comm]

end Nat

namespace BoundingSieve

noncomputable def finiteSelbergDenominator (s : BoundingSieve) (D : Finset Nat) : Real :=
  D.sum s.selbergTerms

noncomputable def finiteSelbergDiagonal (s : BoundingSieve) (D : Finset Nat) (d : Nat) : Real :=
  if Membership.mem D d then
    (ArithmeticFunction.moebius d : Real)*s.selbergTerms d/s.finiteSelbergDenominator D
  else 0

noncomputable def finiteSelbergWeights (s : BoundingSieve) (D : Finset Nat) (d : Nat) : Real :=
  Inv.inv (s.nu d) * Nat.upperDivisorMobius s.prodPrimes (s.finiteSelbergDiagonal D) d

theorem finiteSelbergDenominator_pos (s : BoundingSieve) (D : Finset Nat)
    (hD : forall d, Membership.mem D d -> Dvd.dvd d s.prodPrimes)
    (h1 : Membership.mem D 1) : 0 < s.finiteSelbergDenominator D := by
  have hle := Finset.single_le_sum
    (fun d hd => le_of_lt (s.selbergTerms_pos (hD d hd))) h1
  exact lt_of_lt_of_le (s.selbergTerms_pos (one_dvd _)) hle

/-- The explicitly constructed weights attain their prescribed diagonal
coordinates by dual Mobius inversion. -/
theorem finiteSelbergWeights_projection (s : BoundingSieve) (D : Finset Nat)
    {d : Nat} (hd : Dvd.dvd d s.prodPrimes) :
    s.prodPrimes.divisors.sum (fun e =>
      if Dvd.dvd d e then s.nu e*s.finiteSelbergWeights D e else 0) =
        s.finiteSelbergDiagonal D d := by
  have hP : 0 < s.prodPrimes := Nat.pos_of_ne_zero s.prodPrimes_ne_zero
  calc
    s.prodPrimes.divisors.sum (fun e =>
        if Dvd.dvd d e then s.nu e*s.finiteSelbergWeights D e else 0) =
      s.prodPrimes.divisors.sum (fun e =>
        if Dvd.dvd d e then Nat.upperDivisorMobius s.prodPrimes
          (s.finiteSelbergDiagonal D) e else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      have hnz : Not (s.nu e = 0) := s.nu_ne_zero (Nat.dvd_of_mem_divisors he)
      by_cases hde : Dvd.dvd d e
      next => simp [hde, finiteSelbergWeights, hnz, mul_assoc]
      next => simp [hde]
    _ = s.finiteSelbergDiagonal D d := Nat.sum_upperDivisorMobius hP hd _

/-- The actual finite optimizer has exact main quadratic form1/H.
Normalization and weight-size bounds are separate construction lemmas. -/
theorem finiteSelbergWeights_main (s : BoundingSieve) (D : Finset Nat)
    (hD : forall d, Membership.mem D d -> Dvd.dvd d s.prodPrimes)
    (h1 : Membership.mem D 1) :
    s.mainSum (lambdaSquared (s.finiteSelbergWeights D)) =
      Inv.inv (s.finiteSelbergDenominator D) := by
  have hH0 : Not (s.finiteSelbergDenominator D = 0) :=
    ne_of_gt (s.finiteSelbergDenominator_pos D hD h1)
  have hsub : D <= s.prodPrimes.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr (And.intro (hD d hd) s.prodPrimes_ne_zero)
  have hfilter : s.prodPrimes.divisors.filter (fun d => Membership.mem D d) = D := by
    ext d
    simp only [Finset.mem_filter]
    exact Iff.intro (fun h => h.2) (fun h => And.intro (hsub h) h)
  calc
    s.mainSum (lambdaSquared (s.finiteSelbergWeights D)) =
        s.prodPrimes.divisors.sum (fun d => Inv.inv (s.selbergTerms d)*
          (s.finiteSelbergDiagonal D d)^2) := by
      rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
      apply Finset.sum_congr rfl
      intro d hd
      rw [s.finiteSelbergWeights_projection D (Nat.dvd_of_mem_divisors hd)]
    _ = s.prodPrimes.divisors.sum (fun d =>
        if Membership.mem D d then
          s.selbergTerms d/(s.finiteSelbergDenominator D)^2 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hg0 : Not (s.selbergTerms d = 0) :=
        ne_of_gt (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd))
      have hmu : (ArithmeticFunction.moebius d : Real)^2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_mem_divisors_prodPrimes hd)
      by_cases hm : Membership.mem D d
      next =>
        simp only [finiteSelbergDiagonal, if_pos hm]
        calc
          Inv.inv (s.selbergTerms d)*
              ((ArithmeticFunction.moebius d : Real)*s.selbergTerms d/
                s.finiteSelbergDenominator D)^2 =
            (ArithmeticFunction.moebius d : Real)^2*s.selbergTerms d/
              (s.finiteSelbergDenominator D)^2 := by
                field_simp [hg0, hH0] <;> ring
          _ = s.selbergTerms d/(s.finiteSelbergDenominator D)^2 := by rw [hmu, one_mul]
      next => simp [finiteSelbergDiagonal, hm]
    _ = D.sum (fun d => s.selbergTerms d/(s.finiteSelbergDenominator D)^2) := by
      rw [<- Finset.sum_filter, hfilter]
    _ = Inv.inv (s.finiteSelbergDenominator D) := by
      simp only [div_eq_mul_inv]
      rw [<- Finset.sum_mul]
      change s.finiteSelbergDenominator D*Inv.inv ((s.finiteSelbergDenominator D)^2) =
        Inv.inv (s.finiteSelbergDenominator D)
      field_simp

end BoundingSieve
