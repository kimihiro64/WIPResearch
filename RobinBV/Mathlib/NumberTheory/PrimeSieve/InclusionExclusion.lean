/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Squarefree

/-!
# Complete finite prime-sieve inclusion-exclusion

The expansion retains every subset and accepts arbitrary ring-valued weights.
The divisor modulus is the product of the selected distinct primes. This
supplies the exact arithmetic coefficients needed by owner-resolved sieve
estimates; no truncation remainder is discarded.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- A product of distinct primes divides n exactly when every selected prime
does. The statement includes n = 0 and the empty prime set. -/
theorem prod_primes_dvd_iff {s : Finset Nat}
    (hs : forall p, Membership.mem s p -> Nat.Prime p) (n : Nat) :
    Dvd.dvd (Finset.prod s (fun p => p)) n <->
      forall p, Membership.mem s p -> Dvd.dvd p n := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp
  case neg =>
    have h := Nat.prod_primeFactors_dvd_iff (n := Finset.prod s (fun p => p)) hn
    rw [Nat.primeFactors_prod hs] at h
    rw [h]
    constructor
    . intro hsub p hp
      exact ((Nat.mem_primeFactors_of_ne_zero hn).mp (hsub hp)).2
    . intro hdiv p hp
      exact (Nat.mem_primeFactors_of_ne_zero hn).mpr (And.intro (hs p hp) (hdiv p hp))

/-- Exact pointwise inclusion-exclusion, with products rather than an
uninstantiated abstract intersection predicate. -/
theorem primeSieve_indicator_eq_powerset
    {R : Type*} [CommRing R] {s : Finset Nat}
    (hs : forall p, Membership.mem s p -> Nat.Prime p) (n : Nat) :
    (if (forall p, Membership.mem s p -> Not (Dvd.dvd p n)) then (1 : R) else 0) =
      Finset.sum s.powerset (fun t =>
        (-1 : R) ^ t.card * (if Dvd.dvd (Finset.prod t (fun p => p)) n then 1 else 0)) := by
  have hprod :
      Finset.prod s (fun p => (1 : R) - (if Dvd.dvd p n then 1 else 0)) =
        if (forall p, Membership.mem s p -> Not (Dvd.dvd p n)) then 1 else 0 := by
    calc
      Finset.prod s (fun p => (1 : R) - (if Dvd.dvd p n then 1 else 0)) =
          Finset.prod s (fun p => if Not (Dvd.dvd p n) then (1 : R) else 0) := by
        apply Finset.prod_congr rfl
        intro p hp
        by_cases hpn : Dvd.dvd p n <;> simp [hpn]
      _ = _ := Finset.prod_boole
  rw [<- hprod, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Finset.prod_boole]
  apply Finset.sum_congr rfl
  intro t ht
  have htPrime : forall p, Membership.mem t p -> Nat.Prime p :=
    fun p hp => hs p ((Finset.mem_powerset.mp ht) hp)
  simp only [prod_primes_dvd_iff htPrime]

/-- Complete arbitrary-weight sieve expansion over an arbitrary finite
integer domain. Signed and complex weights are allowed. -/
theorem sum_primeSieve_eq_powerset
    {R : Type*} [CommRing R] (F : Nat -> R) (domain : Finset Nat)
    {s : Finset Nat} (hs : forall p, Membership.mem s p -> Nat.Prime p) :
    Finset.sum (domain.filter
      (fun n => forall p, Membership.mem s p -> Not (Dvd.dvd p n))) F =
      Finset.sum s.powerset (fun t => (-1 : R) ^ t.card *
        Finset.sum (domain.filter (fun n => Dvd.dvd (Finset.prod t (fun p => p)) n)) F) := by
  simp only [Finset.sum_filter]
  calc
    Finset.sum domain (fun n =>
        if (forall p, Membership.mem s p -> Not (Dvd.dvd p n)) then F n else 0) =
        Finset.sum domain (fun n => F n *
          (if (forall p, Membership.mem s p -> Not (Dvd.dvd p n)) then (1 : R) else 0)) := by
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = Finset.sum domain (fun n => F n *
        Finset.sum s.powerset (fun t => (-1 : R) ^ t.card *
          (if Dvd.dvd (Finset.prod t (fun p => p)) n then 1 else 0))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [primeSieve_indicator_eq_powerset hs]
    _ = Finset.sum s.powerset (fun t => (-1 : R) ^ t.card *
        Finset.sum domain (fun n =>
          if Dvd.dvd (Finset.prod t (fun p => p)) n then F n else 0)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp [mul_comm]

/-- Adding a new prime to a squarefree divisor modulus combines the two
divisibility conditions without losing repeated factors of the integer n. -/
theorem ownerProd_dvd_iff {p : Nat} {s : Finset Nat}
    (hp : Nat.Prime p) (hs : forall r, Membership.mem s r -> Nat.Prime r)
    (hpNot : Not (Membership.mem s p)) (n : Nat) :
    Dvd.dvd (p * Finset.prod s (fun r => r)) n <->
      And (Dvd.dvd p n) (Dvd.dvd (Finset.prod s (fun r => r)) n) := by
  have hInsert : forall r, Membership.mem (insert p s) r -> Nat.Prime r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hrp | hrs
    . subst r
      exact hp
    . exact hs r hrs
  have h := prod_primes_dvd_iff hInsert n
  rw [Finset.prod_insert hpNot] at h
  simp only [Finset.forall_mem_insert] at h
  simpa only [prod_primes_dvd_iff hs n] using h

/-- Exact owner expansion: the selected prime divides n, and every earlier
prime in s is excluded. Every subset appears with its actual product modulus. -/
theorem sum_ownerPrimeSieve_eq_powerset
    {R : Type*} [CommRing R] (F : Nat -> R) (domain : Finset Nat)
    {p : Nat} {s : Finset Nat} (hp : Nat.Prime p)
    (hs : forall r, Membership.mem s r -> And (Nat.Prime r) (r < p)) :
    Finset.sum (domain.filter (fun n => And (Dvd.dvd p n)
      (forall r, Membership.mem s r -> Not (Dvd.dvd r n)))) F =
      Finset.sum s.powerset (fun t => (-1 : R) ^ t.card *
        Finset.sum (domain.filter
          (fun n => Dvd.dvd (p * Finset.prod t (fun r => r)) n)) F) := by
  have hsPrime : forall r, Membership.mem s r -> Nat.Prime r := fun r hr => (hs r hr).1
  calc
    Finset.sum (domain.filter (fun n => And (Dvd.dvd p n)
        (forall r, Membership.mem s r -> Not (Dvd.dvd r n)))) F =
        Finset.sum ((domain.filter (fun n => Dvd.dvd p n)).filter
          (fun n => forall r, Membership.mem s r -> Not (Dvd.dvd r n))) F := by
      rw [Finset.filter_filter]
    _ = Finset.sum s.powerset (fun t => (-1 : R) ^ t.card *
        Finset.sum ((domain.filter (fun n => Dvd.dvd p n)).filter
          (fun n => Dvd.dvd (Finset.prod t (fun r => r)) n)) F) :=
      sum_primeSieve_eq_powerset F (domain.filter (fun n => Dvd.dvd p n)) hsPrime
    _ = Finset.sum s.powerset (fun t => (-1 : R) ^ t.card *
        Finset.sum (domain.filter
          (fun n => Dvd.dvd (p * Finset.prod t (fun r => r)) n)) F) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htSub := Finset.mem_powerset.mp ht
      have htPrime : forall r, Membership.mem t r -> Nat.Prime r :=
        fun r hr => (hs r (htSub hr)).1
      have hpNot : Not (Membership.mem t p) :=
        fun h => (lt_irrefl p) (hs p (htSub h)).2
      have hSets :
          ((domain.filter (fun n => Dvd.dvd p n)).filter
            (fun n => Dvd.dvd (Finset.prod t (fun r => r)) n)) =
          domain.filter (fun n => Dvd.dvd (p * Finset.prod t (fun r => r)) n) := by
        ext n
        simp only [Finset.mem_filter, ownerProd_dvd_iff hp htPrime hpNot, and_assoc]
      rw [hSets]

end Nat.PrimeSieve
