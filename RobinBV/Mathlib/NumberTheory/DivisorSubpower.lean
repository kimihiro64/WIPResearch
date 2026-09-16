/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# An explicit subpower bound for the divisor count

For epsilon>0 put q=2^epsilon, A=q/(q-1), and K=ceil(2^(1/epsilon)).
The full prime-factor product gives card(divisors(n)) <= A^K*n^epsilon
for every positive integer n. Small primes cost one geometric-ratio
factor each; large primes are absorbed into n^epsilon. No eventual
threshold, finite verification, or asymptotic remainder is used.
-/

set_option autoImplicit false

namespace Real

/-- The geometric-ratio reserve is at least one. -/
theorem one_le_geometric_ratio {q : Real} (hq : 1 < q) :
    1 <= q/(q-1) := by
  have hd : 0 < q-1 := by linarith
  have hh := div_le_div_of_nonneg_right (show q-1 <= q by linarith) (le_of_lt hd)
  rw [div_self (ne_of_gt hd)] at hh
  exact hh

/-- A geometric sum uniformly absorbs every natural exponent plus one. -/
theorem nat_add_one_le_geometric_ratio {q : Real} (hq : 1 < q) (v : Nat) :
    (v : Real)+1 <= (q/(q-1))*q^v := by
  have hd : 0 < q-1 := by linarith
  have hsum : (v : Real)+1 <= (Finset.range (v+1)).sum (fun j => q^j) := by
    calc
      _ = (Finset.range (v+1)).sum (fun _ => (1 : Real)) := by simp
      _ <= _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hh := Real.one_le_rpow (le_of_lt hq) (Nat.cast_nonneg j)
        simpa only [Real.rpow_natCast] using hh
  have hmul := mul_le_mul_of_nonneg_right hsum (le_of_lt hd)
  rw [geom_sum_mul] at hmul
  have hcancel : ((q/(q-1))*q^v)*(q-1) = q^(v+1) := by
    rw [pow_succ]
    field_simp
  nlinarith

/-- The elementary exponential majorant used for large prime factors. -/
theorem nat_add_one_le_two_pow (v : Nat) :
    (v : Real)+1 <= (2 : Real)^v := by
  induction v with
  | zero => norm_num
  | succ v ih =>
    rw [Nat.cast_succ, pow_succ]
    have hv : (0 : Real) <= v := Nat.cast_nonneg v
    linarith

end Real

namespace Nat

/-- Bound the full divisor product at any admissible prime cutoff. -/
theorem card_divisors_le_rpow_of_cutoff {epsilon : Real} (hepsilon : 0 < epsilon)
    (K : Nat) (hK : (2 : Real) <= (K : Real)^epsilon)
    {n : Nat} (hn : Not (n = 0)) :
    (n.divisors.card : Real) <=
      (((2 : Real)^epsilon)/((2 : Real)^epsilon-1))^K*(n : Real)^epsilon := by
  let A : Real := ((2 : Real)^epsilon)/((2 : Real)^epsilon-1)
  have hq : 1 < (2 : Real)^epsilon := Real.one_lt_rpow (by norm_num) hepsilon
  have hA : 1 <= A := Real.one_le_geometric_ratio hq
  have hA0 : 0 <= A := le_trans zero_le_one hA
  have hfactor : forall p, (n.primeFactors : Set Nat) p ->
      (n.factorization p : Real)+1 <=
        (if p < K then A else 1)*(((p : Real)^(n.factorization p))^epsilon) := by
    intro p hp
    have hp2 : (2 : Real) <= p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : Real) <= p := Nat.cast_nonneg p
    have hswap : ((p : Real)^epsilon)^(n.factorization p) =
        ((p : Real)^(n.factorization p))^epsilon := by
      rw [<- Real.rpow_mul_natCast hp0, mul_comm epsilon, Real.rpow_natCast_mul hp0]
    by_cases hpk : p < K
    next =>
      rw [if_pos hpk]
      calc
        _ <= A*((2 : Real)^epsilon)^(n.factorization p) :=
          Real.nat_add_one_le_geometric_ratio hq _
        _ <= A*((p : Real)^epsilon)^(n.factorization p) := by
          apply _root_.mul_le_mul_of_nonneg_left _ hA0
          have hh := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) epsilon)
            (Real.rpow_le_rpow (by norm_num) hp2 (le_of_lt hepsilon))
            (Nat.cast_nonneg (n.factorization p))
          simpa only [Real.rpow_natCast] using hh
        _ = _ := by rw [hswap]
    next =>
      rw [if_neg hpk, one_mul]
      have hKp : (K : Real) <= p := by exact_mod_cast (Nat.le_of_not_gt hpk)
      have htwo : (2 : Real) <= (p : Real)^epsilon :=
        hK.trans (Real.rpow_le_rpow (Nat.cast_nonneg K) hKp (le_of_lt hepsilon))
      calc
        _ <= (2 : Real)^(n.factorization p) := Real.nat_add_one_le_two_pow _
        _ <= ((p : Real)^epsilon)^(n.factorization p) := by
          have hh := Real.rpow_le_rpow (by norm_num) htwo
            (Nat.cast_nonneg (n.factorization p))
          simpa only [Real.rpow_natCast] using hh
        _ = _ := hswap
  have hmain : n.primeFactors.prod
      (fun p => ((p : Real)^(n.factorization p))^epsilon) = (n : Real)^epsilon := by
    rw [Real.finsetProd_rpow _ _ (fun p hp => _root_.pow_nonneg (Nat.cast_nonneg p) _)]
    have he : n.primeFactors.prod (fun p => (p : Real)^(n.factorization p)) = (n : Real) := by
      exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
    rw [he]
  have hsmall : n.primeFactors.prod (fun p => if p < K then A else 1) <= A^K := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    have hcard : (n.primeFactors.filter (fun p => p < K)).card <= K := by
      calc
        _ <= (Finset.range K).card := Finset.card_le_card
          (fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        _ = K := Finset.card_range K
    have hh := Real.rpow_le_rpow_of_exponent_le hA
      (show (((n.primeFactors.filter (fun p => p < K)).card : Nat) : Real) <= (K : Real) by
        exact_mod_cast hcard)
    simpa only [Real.rpow_natCast] using hh
  calc
    (n.divisors.card : Real) =
        n.primeFactors.prod (fun p => (n.factorization p : Real)+1) := by
      rw [Nat.card_divisors hn, Nat.cast_prod]
      simp only [Nat.cast_add, Nat.cast_one]
    _ <= n.primeFactors.prod (fun p =>
        (if p < K then A else 1)*(((p : Real)^(n.factorization p))^epsilon)) :=
      Finset.prod_le_prod (fun p hp => by positivity) hfactor
    _ = (n.primeFactors.prod (fun p => if p < K then A else 1))*(n : Real)^epsilon := by
      rw [Finset.prod_mul_distrib, hmain]
    _ <= A^K*(n : Real)^epsilon :=
      _root_.mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- An explicit subpower majorant holds for every positive integer. -/
theorem card_divisors_le_rpow_explicit {epsilon : Real} (hepsilon : 0 < epsilon)
    {n : Nat} (hn : Not (n = 0)) :
    (n.divisors.card : Real) <=
      (((2 : Real)^epsilon)/((2 : Real)^epsilon-1))^(Nat.ceil ((2 : Real)^(1/epsilon)))*
        (n : Real)^epsilon := by
  apply card_divisors_le_rpow_of_cutoff hepsilon _ _ hn
  have hh := Real.rpow_le_rpow
    (Real.rpow_nonneg (by norm_num : (0 : Real) <= 2) _) (Nat.le_ceil ((2 : Real)^(1/epsilon)))
    (le_of_lt hepsilon)
  rw [<- Real.rpow_mul (by norm_num : (0 : Real) <= 2)] at hh
  rw [show (1/epsilon)*epsilon = 1 by field_simp, Real.rpow_one] at hh
  exact hh

end Nat
