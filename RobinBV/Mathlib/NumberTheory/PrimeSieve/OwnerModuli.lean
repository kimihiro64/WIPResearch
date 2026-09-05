/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Squarefree

/-!
# Unique product moduli for prime-owner expansions

A branch has modulus p times a product of distinct primes below p. Equality
of two such moduli forces equality of both the owner prime and its selected
prime set. The full universe product also bounds every branch modulus.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

/-- Distinct owner/subset pairs give distinct squarefree product moduli. -/
theorem ownerModulus_injective
    {p q : Nat} {s t : Finset Nat} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hs : forall r, Membership.mem s r -> And (Nat.Prime r) (r < p))
    (ht : forall r, Membership.mem t r -> And (Nat.Prime r) (r < q))
    (hEq : p * Finset.prod s (fun r => r) = q * Finset.prod t (fun r => r)) :
    And (p = q) (s = t) := by
  have hpNot : Not (Membership.mem s p) := fun h => (lt_irrefl p) (hs p h).2
  have hqNot : Not (Membership.mem t q) := fun h => (lt_irrefl q) (ht q h).2
  have hps : forall r, Membership.mem (insert p s) r -> Nat.Prime r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hrp | hrs
    . subst r
      exact hp
    . exact (hs r hrs).1
  have hqt : forall r, Membership.mem (insert q t) r -> Nat.Prime r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hrq | hrt
    . subst r
      exact hq
    . exact (ht r hrt).1
  have hProduct :
      Finset.prod (insert p s) (fun r => r) =
        Finset.prod (insert q t) (fun r => r) := by
    simpa only [Finset.prod_insert hpNot, Finset.prod_insert hqNot] using hEq
  have hSets := congrArg Nat.primeFactors hProduct
  rw [Nat.primeFactors_prod hps, Nat.primeFactors_prod hqt] at hSets
  have hpIn : Membership.mem (insert q t) p := by
    rw [<- hSets]
    exact Finset.mem_insert_self p s
  have hqIn : Membership.mem (insert p s) q := by
    rw [hSets]
    exact Finset.mem_insert_self q t
  have hpq : p <= q := by
    rcases Finset.mem_insert.mp hpIn with h | h
    . exact le_of_eq h
    . exact (ht p h).2.le
  have hqp : q <= p := by
    rcases Finset.mem_insert.mp hqIn with h | h
    . exact le_of_eq h
    . exact (hs q h).2.le
  have hOwner : p = q := le_antisymm hpq hqp
  refine And.intro hOwner ?_
  subst q
  simpa only [Finset.erase_insert hpNot, Finset.erase_insert hqNot] using
    congrArg (fun u : Finset Nat => u.erase p) hSets

/-- Bounding the complete universe product bounds every branch modulus.
No assertion is made that a larger sieve cutoff fits the BV range. -/
theorem ownerModulus_le_product
    {p : Nat} {s primeSet : Finset Nat}
    (hp : Membership.mem primeSet p)
    (hs : forall r, Membership.mem s r -> Membership.mem primeSet r)
    (hpNot : Not (Membership.mem s p))
    (hOne : forall r, Membership.mem primeSet r -> 1 <= r) :
    p * Finset.prod s (fun r => r) <=
      Finset.prod primeSet (fun r => r) := by
  have hSubset : forall r, Membership.mem (insert p s) r -> Membership.mem primeSet r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with hrp | hrs
    . subst r
      exact hp
    . exact hs r hrs
  calc
    p * Finset.prod s (fun r => r) =
        Finset.prod (insert p s) (fun r => r) :=
      (Finset.prod_insert (f := fun r : Nat => r) hpNot).symm
    _ <= Finset.prod primeSet (fun r => r) :=
      Finset.prod_le_prod_of_subset_of_one_le (fun {r} hr => hSubset r hr)
        (fun r _ => Nat.zero_le r) (fun r hr _ => hOne r hr)

end Nat.PrimeSieve
