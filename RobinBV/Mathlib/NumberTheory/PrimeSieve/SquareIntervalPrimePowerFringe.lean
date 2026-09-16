/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import RobinBV.Mathlib.NumberTheory.PrimePow.FiniteSum
import RobinBV.Mathlib.NumberTheory.PrimePow.LogCutoff
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalEndpointWeights

/-!
# Exact prime-power corrections on quadratic endpoint fringes

Reindex the complete noncoprime Mangoldt fringe mass over prime divisors of
the modulus and all admitted positive powers. Both the actual fringe
multiplicity and the cutoff position are retained before applying the proved
pointwise row capacity. No distribution or prime-supply hypothesis is used.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- A zero-valued initial weight removes the zero term of an ordinary prefix. -/
theorem squarePrefix_eq_Icc_of_zero (n : Nat) (F : Nat -> Real) (hF : F 0 = 0) :
    squarePrefix F n = Finset.sum (Finset.Icc 1 n) F := by
  have hs : Finset.range (n+1) = insert 0 (Finset.Icc 1 n) := by
    apply Finset.ext
    intro r
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [squarePrefix, hs, Finset.sum_insert (by simp), hF, zero_add]

/-- The full actual fringe mass of prime powers meeting the modulus. -/
noncomputable def squareThirdNoncoprimeMass (n q : Nat) : Real :=
  Finset.sum (squareThirdFringeSupport n) (fun r =>
    ((squareThirdFringeRows n r).card : Real)*
      (if Nat.Coprime r q then 0 else ArithmeticFunction.vonMangoldt r))

/-- The exact unweighted noncoprime fringe mass is nonnegative. -/
theorem squareThirdNoncoprimeMass_nonneg (n q : Nat) :
    0 <= squareThirdNoncoprimeMass n q := by
  apply Finset.sum_nonneg
  intro r hr
  apply mul_nonneg (Nat.cast_nonneg _)
  split_ifs
  next => exact le_refl 0
  next => exact ArithmeticFunction.vonMangoldt_nonneg

/-- The supported fringe mass equals its complete interval sum with zero extension. -/
theorem squareThirdNoncoprimeMass_eq_Icc {n : Nat} (hn : 100 <= n) (q : Nat) :
    squareThirdNoncoprimeMass n q =
      Finset.sum (Finset.Icc 1 n) (fun r =>
        if Nat.Coprime r q then 0 else
          ((squareThirdFringeRows n r).card : Real)*ArithmeticFunction.vonMangoldt r) := by
  let F : Nat -> Real := fun r => if Nat.Coprime r q then 0 else ArithmeticFunction.vonMangoldt r
  have heq := sum_squareThirdPrefix_eq_supported_fringe hn F
  rw [sum_squareThirdPrefix_eq_fringe] at heq
  have hzero : ((squareThirdFringeRows n 0).card : Real)*F 0 = 0 := by simp [F]
  have hi := squarePrefix_eq_Icc_of_zero n (fun r => ((squareThirdFringeRows n r).card : Real)*F r) hzero
  change Finset.sum (Finset.range (n+1)) _ = _ at hi
  change Finset.sum (squareThirdFringeSupport n) (fun r => ((squareThirdFringeRows n r).card : Real)*F r) = _
  rw [<- heq, hi]
  apply Finset.sum_congr rfl
  intro r hr
  dsimp [F]
  split_ifs <;> simp

/-- Reindex the actual noncoprime fringe mass by every admitted positive prime power. -/
theorem squareThirdNoncoprimeMass_eq_primePowers {n q : Nat} (hn : 100 <= n)
    (hq : Not (q = 0)) :
    squareThirdNoncoprimeMass n q =
      Finset.sum q.primeFactors (fun p =>
        Finset.sum (Finset.Icc 1 (Nat.log p n)) (fun k =>
          ((squareThirdFringeRows n (p^k)).card : Real)*Real.log p)) := by
  let F : Nat -> Real := fun r =>
    ((squareThirdFringeRows n r).card : Real)*ArithmeticFunction.vonMangoldt r
  have hF : forall r : Nat, Not (IsPrimePow r) -> F r = 0 := by
    intro r hr
    dsimp [F]
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hr, mul_zero]
  rw [squareThirdNoncoprimeMass_eq_Icc hn,
    Nat.sum_nonCoprime_eq_sum_primeFactors_sum_pow F hF hq n]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro k hk
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hk0 : Not (k = 0) := by have hi := Finset.mem_Icc.mp hk; omega
  dsimp [F]
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk0,
    ArithmeticFunction.vonMangoldt_apply_prime hprime]

/-- Positive prime-power indices lying above the actual rounded cube-cutoff support. -/
noncomputable def squareThirdPrimePowerIndices (n p : Nat) : Finset Nat :=
  (Finset.Icc 1 (Nat.log p n)).filter
    (fun k => Nat.nthRoot 3 (n*n+2*n)-4 <= p^k)

/-- Only prime powers in the actual rounded support contribute to the correction. -/
theorem squareThirdNoncoprimeMass_eq_supported_primePowers {n q : Nat} (hn : 100 <= n)
    (hq : Not (q = 0)) :
    squareThirdNoncoprimeMass n q =
      Finset.sum q.primeFactors (fun p =>
        Finset.sum (squareThirdPrimePowerIndices n p) (fun k =>
          ((squareThirdFringeRows n (p^k)).card : Real)*Real.log p)) := by
  rw [squareThirdNoncoprimeMass_eq_primePowers hn hq]
  apply Finset.sum_congr rfl
  intro p hp
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k hk hnot
  have hlo : Not (Nat.nthRoot 3 (n*n+2*n)-4 <= p^k) := by
    intro he
    exact hnot (Finset.mem_filter.mpr (And.intro hk he))
  have hempty : squareThirdFringeRows n (p^k) = ({} : Finset Nat) := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro h hh
    exact hlo (Finset.mem_Icc.mp (squareThirdFringeRows_bounds hn hh).2).1
  simp only [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]

/-- The pointwise fringe capacity bounds the exact supported prime-power correction. -/
theorem squareThirdNoncoprimeMass_le_supported_primePowers {n q : Nat} (hn : 100 <= n)
    (hq : Not (q = 0)) :
    squareThirdNoncoprimeMass n q <=
      Finset.sum q.primeFactors (fun p =>
        Finset.sum (squareThirdPrimePowerIndices n p) (fun k =>
          (2*(n/(3*p^k)+1) : Nat)*Real.log p)) := by
  rw [squareThirdNoncoprimeMass_eq_supported_primePowers hn hq]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hlog : 0 <= Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_le)
  apply Finset.sum_le_sum
  intro k hk
  have hbound := card_squareThirdFringeRows_le (r := p^k) hn (Nat.pow_pos hprime.pos)
  apply mul_le_mul_of_nonneg_right _ hlog
  exact_mod_cast hbound

/-- The rounded lower support is positive throughout the uniform row regime. -/
theorem squareThirdFringeSupport_lower_pos {n : Nat} (hn : 100 <= n) :
    0 < Nat.nthRoot 3 (n*n+2*n)-4 := by
  have hroot : 5 <= Nat.nthRoot 3 (n*n+2*n) := by
    by_contra hnot
    have hlt : Nat.nthRoot 3 (n*n+2*n) < 5 := by omega
    have hcube := (Nat.nthRoot_lt_iff (by decide : Not (3 = 0))).mp hlt
    nlinarith only [hn, hcube]
  omega

/-- Every admitted prime power has reciprocal capacity at most the lower-support capacity. -/
theorem squareThirdPrimePower_div_le {n p k : Nat} (hn : 100 <= n)
    (hk : Membership.mem (squareThirdPrimePowerIndices n p) k) :
    n/(3*p^k) <= n/(3*(Nat.nthRoot 3 (n*n+2*n)-4)) := by
  let Y := Nat.nthRoot 3 (n*n+2*n)-4
  have hY : 0 < Y := squareThirdFringeSupport_lower_pos hn
  have hlo := (Finset.mem_filter.mp hk).2
  have hmul := Nat.div_mul_le_self n (3*p^k)
  have hden := Nat.mul_le_mul_left (n/(3*p^k)) (show 3*Y <= 3*p^k by omega)
  apply (Nat.le_div_iff_mul_le (show 0 < 3*Y by omega)).mpr
  nlinarith only [hmul, hden]

/-- The complete supported capacity for one prime base is bounded by the cutoff capacity times log n. -/
theorem sum_squareThirdPrimePower_capacity_le_log {n p : Nat} (hn : 100 <= n)
    (hp : p.Prime) :
    Finset.sum (squareThirdPrimePowerIndices n p) (fun k =>
      (2*(n/(3*p^k)+1) : Nat)*Real.log p) <=
      (2*(n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1) : Nat)*Real.log n := by
  let B : Nat := 2*(n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1)
  have hB : 0 <= (B : Real) := Nat.cast_nonneg _
  have hlogp : 0 <= Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hcount : (squareThirdPrimePowerIndices n p).card <= Nat.log p n := by
    have h := Finset.card_le_card (show squareThirdPrimePowerIndices n p <= Finset.Icc 1 (Nat.log p n)
      from Finset.filter_subset _ _)
    simpa using h
  have hcountR : ((squareThirdPrimePowerIndices n p).card : Real) <= (Nat.log p n : Real) := by
    exact_mod_cast hcount
  have hlogpower : (Nat.log p n : Real)*Real.log p <= Real.log n := by
    have h := Nat.log_sub_log_floor_mul_log_bounds hp.one_lt (show (1:Real) <= n by exact_mod_cast (show 1 <= n by omega))
    simpa using sub_nonneg.mp h.1
  calc
    _ <= Finset.sum (squareThirdPrimePowerIndices n p) (fun _ => (B:Real)*Real.log p) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_right _ hlogp
      have hdiv := squareThirdPrimePower_div_le hn hk
      have hnat : 2*(n/(3*p^k)+1) <= B := by dsimp [B]; omega
      exact_mod_cast hnat
    _ = ((squareThirdPrimePowerIndices n p).card : Real)*((B:Real)*Real.log p) := by simp
    _ <= (Nat.log p n : Real)*((B:Real)*Real.log p) :=
      mul_le_mul_of_nonneg_right hcountR (mul_nonneg hB hlogp)
    _ = (B:Real)*((Nat.log p n : Real)*Real.log p) := by ring
    _ <= _ := mul_le_mul_of_nonneg_left hlogpower hB

/-- An explicit finite logarithmic bound for the actual noncoprime fringe mass. -/
theorem squareThirdNoncoprimeMass_le_log {n q : Nat} (hn : 100 <= n)
    (hq : Not (q = 0)) :
    squareThirdNoncoprimeMass n q <=
      (q.primeFactors.card : Real)*
        (2*(n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1) : Nat)*Real.log n := by
  apply le_trans (squareThirdNoncoprimeMass_le_supported_primePowers hn hq)
  calc
    _ <= Finset.sum q.primeFactors (fun _ =>
        (2*(n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1) : Nat)*Real.log n) := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_squareThirdPrimePower_capacity_le_log hn (Nat.prime_of_mem_primeFactors hp)
    _ = _ := by simp [mul_assoc]

end Nat.PrimeSieve
