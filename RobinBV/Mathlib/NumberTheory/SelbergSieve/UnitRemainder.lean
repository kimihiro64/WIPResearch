/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.SelbergSieve.WeightsBound

/-!
# UnitRemainder

Finite Selberg sieve input, proved from Mathlib primitives.
The classical sieve argument follows D. R. Heath-Brown, Lectures on sieves,
Sections 2-3 (https://arxiv.org/abs/math/0209360).
No prime-distribution or unproved analytic hypothesis is introduced.
-/

set_option autoImplicit false
open scoped Classical
namespace BoundingSieve

/-- The finite rearrangement follows the private support-enlargement argument
in Mathlib.NumberTheory.SelbergSieve (Arend Mellendijk, Apache-2.0). -/
private theorem lambda_sum_larger_support (f : Nat -> Nat -> Nat -> Real) (P : Nat) :
    P.divisors.sum (fun d => d.divisors.sum (fun a => d.divisors.sum
      (fun b => if d = Nat.lcm a b then f a b d else 0))) =
    P.divisors.sum (fun d => P.divisors.sum (fun a => P.divisors.sum
      (fun b => if d = Nat.lcm a b then f a b d else 0))) := by
  apply Finset.sum_congr rfl
  intro d hd
  have hd' := Nat.mem_divisors.mp hd
  have hcond : forall a b, (Dvd.dvd a d /\ Dvd.dvd b d /\ d = Nat.lcm a b) =
      (d = Nat.lcm a b) := by
    intro a b
    apply propext
    constructor
    next => exact fun h => h.2.2
    next =>
      intro he
      rw [he]
      exact And.intro (Nat.dvd_lcm_left a b) (And.intro (Nat.dvd_lcm_right a b) rfl)
  simp_rw [<- Nat.divisors_filter_dvd_of_dvd hd'.2 hd'.1, Finset.sum_filter,
    Finset.ite_sum_zero, <- ite_and, hcond]

theorem sum_lambdaSquared_eq_square (P : Nat) (w : Nat -> Real) :
    P.divisors.sum (lambdaSquared w) = (P.divisors.sum w)^2 := by
  unfold lambdaSquared
  rw [lambda_sum_larger_support (fun a b _ => w a*w b) P]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  have hlcm : Membership.mem P.divisors (Nat.lcm a b) := Nat.mem_divisors.mpr
    (And.intro (Nat.lcm_dvd_iff.mpr
      (And.intro (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb)))
      (Nat.mem_divisors.mp ha).2)
  simp [hlcm, mul_comm]

theorem abs_lambdaSquared_le (w : Nat -> Real) (d : Nat) :
    abs (lambdaSquared w d) <= lambdaSquared (fun a => abs (w a)) d := by
  unfold lambdaSquared
  calc
    abs (d.divisors.sum (fun a => d.divisors.sum
        (fun b => if d = Nat.lcm a b then w a*w b else 0))) <=
      d.divisors.sum (fun a => abs (d.divisors.sum
        (fun b => if d = Nat.lcm a b then w a*w b else 0))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= d.divisors.sum (fun a => d.divisors.sum
        (fun b => abs (if d = Nat.lcm a b then w a*w b else 0))) :=
      Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ = d.divisors.sum (fun a => d.divisors.sum
        (fun b => if d = Nat.lcm a b then abs (w a)*abs (w b) else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases he : d = Nat.lcm a b <;> simp [he, abs_mul]

/-- Every divisor remainder is retained; the full quadratic error costs at
most the square of the complete weight L1 norm. -/
theorem errSum_lambdaSquared_le_square (s : BoundingSieve) (w : Nat -> Real)
    (hR : forall d, Membership.mem s.prodPrimes.divisors d -> abs (s.rem d) <= 1) :
    s.errSum (lambdaSquared w) <=
      (s.prodPrimes.divisors.sum (fun d => abs (w d)))^2 := by
  calc
    s.errSum (lambdaSquared w) =
        s.prodPrimes.divisors.sum (fun d => abs (lambdaSquared w d)*abs (s.rem d)) := rfl
    _ <= s.prodPrimes.divisors.sum (fun d => abs (lambdaSquared w d)*1) :=
      Finset.sum_le_sum (fun d hd => _root_.mul_le_mul_of_nonneg_left (hR d hd) (abs_nonneg _))
    _ = s.prodPrimes.divisors.sum (fun d => abs (lambdaSquared w d)) := by simp
    _ <= s.prodPrimes.divisors.sum (lambdaSquared (fun d => abs (w d))) :=
      Finset.sum_le_sum (fun d _ => abs_lambdaSquared_le w d)
    _ = (s.prodPrimes.divisors.sum (fun d => abs (w d)))^2 :=
      sum_lambdaSquared_eq_square _ _

/-- Full finite Selberg upper bound with actual constructed weights and
explicit unit-remainder error. No optimizer or weight bound is assumed. -/
theorem siftedSum_le_finiteSelbergDenominator_add_card_sq (s : BoundingSieve) (D : Finset Nat)
    (hD : forall e, Membership.mem D e -> Dvd.dvd e s.prodPrimes)
    (hdown : forall e, Membership.mem D e -> forall k, Dvd.dvd k e -> Membership.mem D k)
    (h1 : Membership.mem D 1)
    (hR : forall d, Membership.mem s.prodPrimes.divisors d -> abs (s.rem d) <= 1) :
    s.siftedSum <= s.totalMass/s.finiteSelbergDenominator D+(D.card : Real)^2 := by
  let w := s.finiteSelbergWeights D
  have hmain := s.finiteSelbergWeights_main D hD h1
  have hw1 : w 1 = 1 := s.finiteSelbergWeights_one D hD h1
  have hup := s.siftedSum_le_mainSum_errSum_of_upperMoebius
    (lambdaSquared w) (upperMoebius_lambdaSquared w hw1)
  change s.siftedSum <= s.totalMass*s.mainSum (lambdaSquared (s.finiteSelbergWeights D))+
    s.errSum (lambdaSquared w) at hup
  rw [hmain] at hup
  have herr := s.errSum_lambdaSquared_le_square w hR
  have hL1 : s.prodPrimes.divisors.sum (fun d => abs (w d)) <= (D.card : Real) :=
    s.sum_abs_finiteSelbergWeights_le_card D hD hdown h1
  have hsq : (s.prodPrimes.divisors.sum (fun d => abs (w d)))^2 <= (D.card : Real)^2 := by
    have h := _root_.mul_le_mul hL1 hL1
      (Finset.sum_nonneg (fun d _ => abs_nonneg (w d))) (by positivity : (0 : Real) <= D.card)
    simpa only [pow_two] using h
  calc
    s.siftedSum <= s.totalMass*Inv.inv (s.finiteSelbergDenominator D)+s.errSum (lambdaSquared w) := hup
    _ <= s.totalMass*Inv.inv (s.finiteSelbergDenominator D)+(D.card : Real)^2 :=
      _root_.add_le_add le_rfl (herr.trans hsq)
    _ = s.totalMass/s.finiteSelbergDenominator D+(D.card : Real)^2 := by rw [div_eq_mul_inv]

end BoundingSieve
