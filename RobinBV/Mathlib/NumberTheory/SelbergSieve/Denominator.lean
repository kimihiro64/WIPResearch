/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Harmonic.Bounds
import RobinBV.Mathlib.NumberTheory.SelbergSieve.RadicalFiber

/-!
# Denominator

Finite Selberg sieve input, proved from Mathlib primitives.
The classical sieve argument follows D. R. Heath-Brown, Lectures on sieves,
Sections 2-3 (https://arxiv.org/abs/math/0209360).
No prime-distribution or unproved analytic hypothesis is introduced.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat

noncomputable def squarefreeReciprocalTotientSum (Q : Nat) : Real :=
  ((Finset.Icc 1 Q).filter Squarefree).sum (fun d => (d.totient : Real)^(-1 : Int))

private theorem prime_kernel_squarefree (m : Nat) :
    Squarefree (m.primeFactors.prod (fun p => p)) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  next =>
    intro p hp q hq hne
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hne)
  next =>
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).squarefree

/-- The truncated Selberg denominator dominates the full harmonic sum.
Every integer is assigned to its exact squarefree prime kernel; each fiber
is bounded by its reciprocal totient using the finite Euler product. -/
theorem harmonic_le_squarefreeReciprocalTotientSum (Q : Nat) :
    (harmonic Q : Real) <= squarefreeReciprocalTotientSum Q := by
  let A := Finset.Icc 1 Q
  let D := (Finset.Icc 1 Q).filter Squarefree
  let kernel := fun m : Nat => m.primeFactors.prod (fun p => p)
  have hkernel : forall m, Membership.mem A m -> Membership.mem D (kernel m) := by
    intro m hm
    have hmb := Finset.mem_Icc.mp hm
    have hpos : 0 < kernel m := Finset.prod_pos
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    have hle : kernel m <= m := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd m)
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_Icc.mpr (And.intro (by omega) (by omega))) (prime_kernel_squarefree m))
  have hfiber : forall d, Membership.mem D d ->
      (A.filter (fun m => kernel m = d)).sum (fun m => (m : Real)^(-1 : Int)) <=
        (d.totient : Real)^(-1 : Int) := by
    intro d _
    have hdiv : forall m, Membership.mem (A.filter (fun m => kernel m = d)) m ->
        Dvd.dvd d m := by
      intro m hm
      rw [<- (Finset.mem_filter.mp hm).2]
      exact Nat.prod_primeFactors_dvd m
    apply sum_reciprocal_fiber_le_inv_totient _ d hdiv
    intro m hm
    have hd := Finset.mem_filter.mp hm
    have hmb := Finset.mem_Icc.mp hd.1
    have hpf : d.primeFactors = m.primeFactors := by
      rw [<- hd.2]
      exact Nat.primeFactors_prod_primeFactors m
    rw [hpf]
    exact Nat.mem_factoredNumbers_of_dvd
      (Nat.mem_factoredNumbers_of_primeFactors_subset (by omega) (by intro p hp; exact hp))
      (Nat.div_dvd_of_dvd (hdiv m hm))
  have he : A.sum (fun m => (m : Real)^(-1 : Int)) =
      D.sum (fun d => (A.filter (fun m => kernel m = d)).sum
        (fun m => (m : Real)^(-1 : Int))) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    simp [hkernel m hm]
  have hhar : (harmonic Q : Real) = A.sum (fun m => (m : Real)^(-1 : Int)) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, zpow_neg_one, A]
  calc
    (harmonic Q : Real) = A.sum (fun m => (m : Real)^(-1 : Int)) := hhar
    _ = D.sum (fun d => (A.filter (fun m => kernel m = d)).sum
        (fun m => (m : Real)^(-1 : Int))) := he
    _ <= D.sum (fun d => (d.totient : Real)^(-1 : Int)) := Finset.sum_le_sum hfiber
    _ = squarefreeReciprocalTotientSum Q := rfl

theorem log_succ_le_squarefreeReciprocalTotientSum (Q : Nat) :
    Real.log ((Q : Real)+1) <= squarefreeReciprocalTotientSum Q := by
  have h := (log_add_one_le_harmonic Q).trans (harmonic_le_squarefreeReciprocalTotientSum Q)
  simpa only [Nat.cast_add, Nat.cast_one] using h

end Nat
