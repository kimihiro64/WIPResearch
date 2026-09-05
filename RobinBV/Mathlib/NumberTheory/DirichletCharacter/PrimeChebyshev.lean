/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.Chebyshev
import RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimePowerCorrection

/-!
# Prime Chebyshev sums with character weights

The weighted prime-power remainder is bounded by the entire unweighted
Chebyshev difference. Finite conductor corrections retain every excluded
prime. All estimates are elementary and uniform in the character.
-/

set_option autoImplicit false

namespace DirichletCharacter

noncomputable section

/-- The logarithmically weighted prime sum through an inclusive integer
cutoff, with the actual character values at nonunits. -/
def primeChebyshevSum {N : Nat} (chi : DirichletCharacter Complex N) (P : Nat) : Complex :=
  Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) * chi (p : ZMod N))

/-- The complete weighted contribution from higher prime powers is bounded
by the corresponding unweighted contribution, for every modulus and cutoff. -/
theorem norm_sum_vonMangoldt_sub_primeChebyshevSum_le
    {N : Nat} (chi : DirichletCharacter Complex N) (P : Nat) :
    norm (Finset.sum (Finset.Icc 1 P) (fun n =>
      (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod N)) -
        chi.primeChebyshevSum P) <= Chebyshev.psi (P : Real) - Chebyshev.theta (P : Real) := by
  classical
  let f : Nat -> Complex := fun n =>
    (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod N)
  have hSub : Nat.primesLE P <= Finset.Icc 1 P := by
    intro p hp
    have h := Nat.mem_primesLE.mp hp
    exact Finset.mem_Icc.mpr (And.intro h.2.one_lt.le h.1)
  have hPrime : Finset.sum (Nat.primesLE P) f = chi.primeChebyshevSum P := by
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [f]
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.mem_primesLE.mp hp).2]
  have hRealPrime : Finset.sum (Nat.primesLE P) ArithmeticFunction.vonMangoldt =
      Chebyshev.theta (P : Real) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    apply Finset.sum_congr rfl
    intro p hp
    exact ArithmeticFunction.vonMangoldt_apply_prime (Nat.mem_primesLE.mp hp).2
  have hTotal : Finset.sum (Finset.Icc 1 P) ArithmeticFunction.vonMangoldt <=
      Chebyshev.psi (P : Real) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    next =>
      intro n hn
      exact Finset.mem_Icc.mpr (And.intro (Nat.zero_le _) (Finset.mem_Icc.mp hn).2)
    next =>
      intro n _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hSplit := Finset.sum_sdiff (f := f) hSub
  rw [hPrime] at hSplit
  have hRealSplit := Finset.sum_sdiff (f := ArithmeticFunction.vonMangoldt) hSub
  rw [hRealPrime] at hRealSplit
  have hRemainder : norm (Finset.sum (SDiff.sdiff (Finset.Icc 1 P) (Nat.primesLE P)) f) <=
      Finset.sum (SDiff.sdiff (Finset.Icc 1 P) (Nat.primesLE P))
        ArithmeticFunction.vonMangoldt := by
    calc
      _ <= Finset.sum _ (fun n => norm (f n)) := norm_sum_le _ _
      _ <= _ := by
        apply Finset.sum_le_sum
        intro n _
        dsimp only [f]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (chi.norm_le_one _) ArithmeticFunction.vonMangoldt_nonneg
  have hEq : Finset.sum (Finset.Icc 1 P) f - chi.primeChebyshevSum P =
      Finset.sum (SDiff.sdiff (Finset.Icc 1 P) (Nat.primesLE P)) f := by
    rw [<- hSplit]
    ring
  change norm (Finset.sum (Finset.Icc 1 P) f - chi.primeChebyshevSum P) <= _
  rw [hEq]
  linarith

/-- The prime sum changes by a bounded finite amount on passage to the
primitive inducing character. The bound includes all prime divisors of the
ambient modulus and is independent of the prime cutoff. -/
theorem norm_primeChebyshevSum_sub_primitive_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (P : Nat) :
    norm (chi.primeChebyshevSum P - chi.primitiveCharacter.primeChebyshevSum P) <=
      Finset.sum N.primeFactors (fun p => Real.log p) := by
  classical
  let S := Finset.filter (fun p => Not (Nat.Coprime p N)) (Nat.primesLE P)
  have hSub : S <= N.primeFactors := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    have hPrime := (Nat.mem_primesLE.mp h.1).2
    have hDvd : Dvd.dvd p N := by
      by_contra hNot
      exact h.2 (hPrime.coprime_iff_not_dvd.mpr hNot)
    exact Nat.mem_primeFactors.mpr (And.intro hPrime (And.intro hDvd (NeZero.ne N)))
  have hBound : norm (chi.primeChebyshevSum P - chi.primitiveCharacter.primeChebyshevSum P) <=
      Finset.sum S (fun p => Real.log p) := by
    unfold primeChebyshevSum
    rw [<- Finset.sum_sub_distrib]
    calc
      _ <= Finset.sum (Nat.primesLE P) (fun p => norm ((Real.log p : Complex) * chi (p : ZMod N) -
          (Real.log p : Complex) * chi.primitiveCharacter (p : ZMod chi.conductor))) := norm_sum_le _ _
      _ <= Finset.sum (Nat.primesLE P) (fun p => if Nat.Coprime p N then 0 else Real.log p) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [<- mul_sub, chi.natCast_sub_primitiveCharacter_eq]
        by_cases h : Nat.Coprime p N
        case pos =>
          rw [if_pos h, if_pos h, mul_zero, norm_zero]
        case neg =>
          rw [if_neg h, if_neg h, norm_mul, norm_neg, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg
              (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le))]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (chi.primitiveCharacter.norm_le_one _)
            (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le))
      _ = _ := by simp only [S, Finset.sum_filter, ite_not]
  exact hBound.trans (Finset.sum_le_sum_of_subset_of_nonneg hSub (fun p hp _ =>
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)))

end

end DirichletCharacter
