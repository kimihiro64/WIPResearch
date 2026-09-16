/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.SelbergSieve.Denominator
import RobinBV.Mathlib.NumberTheory.SelbergSieve.UnitRemainder

/-!
# IntervalSetup

Finite Selberg sieve input, proved from Mathlib primitives.
The classical sieve argument follows D. R. Heath-Brown, Lectures on sieves,
Sections 2-3 (https://arxiv.org/abs/math/0209360).
No prime-distribution or unproved analytic hypothesis is introduced.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat

noncomputable def selbergPrimeSet (Q : Nat) : Finset Nat :=
  (Finset.Icc 1 Q).filter Nat.Prime

noncomputable def selbergPrimeProduct (Q : Nat) : Nat :=
  (selbergPrimeSet Q).prod (fun p => p)

noncomputable def selbergDivisorSupport (Q : Nat) : Finset Nat :=
  (Finset.Icc 1 Q).filter Squarefree

theorem mem_selbergPrimeSet {Q p : Nat} :
    Membership.mem (selbergPrimeSet Q) p <-> Nat.Prime p /\ p <= Q := by
  simp only [selbergPrimeSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  next => exact fun h => And.intro h.2 h.1.2
  next =>
    intro h
    exact And.intro (And.intro (by have := h.1.two_le; omega) h.2) h.1

theorem selbergPrimeProduct_squarefree (Q : Nat) : Squarefree (selbergPrimeProduct Q) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  next =>
    intro p hp q hq hne
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (mem_selbergPrimeSet.mp hp).1
        (mem_selbergPrimeSet.mp hq).1).mpr hne)
  next =>
    intro p hp
    exact (mem_selbergPrimeSet.mp hp).1.squarefree

theorem primeFactors_selbergPrimeProduct (Q : Nat) :
    (selbergPrimeProduct Q).primeFactors = selbergPrimeSet Q :=
  Nat.primeFactors_prod (fun p hp => (mem_selbergPrimeSet.mp hp).1)

theorem prime_dvd_selbergPrimeProduct_iff {Q p : Nat} (hp : Nat.Prime p) :
    Dvd.dvd p (selbergPrimeProduct Q) <-> p <= Q := by
  constructor
  next =>
    intro hd
    have hm := Nat.mem_primeFactors.mpr
      (And.intro hp (And.intro hd (selbergPrimeProduct_squarefree Q).ne_zero))
    rw [primeFactors_selbergPrimeProduct] at hm
    exact (mem_selbergPrimeSet.mp hm).2
  next =>
    intro hq
    have hm := mem_selbergPrimeSet.mpr (And.intro hp hq)
    rw [<- primeFactors_selbergPrimeProduct Q] at hm
    exact Nat.dvd_of_mem_primeFactors hm

theorem selbergDivisorSupport_dvd {Q d : Nat}
    (hd : Membership.mem (selbergDivisorSupport Q) d) :
    Dvd.dvd d (selbergPrimeProduct Q) := by
  have hs := Finset.mem_filter.mp hd
  have hb := Finset.mem_Icc.mp hs.1
  have hsub : d.primeFactors <= (selbergPrimeProduct Q).primeFactors := by
    rw [primeFactors_selbergPrimeProduct]
    intro p hp
    apply mem_selbergPrimeSet.mpr
    refine And.intro (Nat.prime_of_mem_primeFactors hp) ?_
    exact le_trans (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)) hb.2
  have hrad : Dvd.dvd (d.primeFactors.prod (fun p => p)) (selbergPrimeProduct Q) :=
    (Nat.prod_primeFactors_dvd_iff (selbergPrimeProduct_squarefree Q).ne_zero).mpr hsub
  simpa only [Nat.prod_primeFactors_of_squarefree hs.2] using hrad

theorem selbergDivisorSupport_down {Q e : Nat}
    (he : Membership.mem (selbergDivisorSupport Q) e) {k : Nat} (hk : Dvd.dvd k e) :
    Membership.mem (selbergDivisorSupport Q) k := by
  have hs := Finset.mem_filter.mp he
  have hb := Finset.mem_Icc.mp hs.1
  have he0 : Not (e = 0) := by omega
  have hk0 : 0 < k := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr (And.intro hk he0))
  have hke : k <= e := Nat.le_of_dvd (by omega) hk
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_Icc.mpr (And.intro (by omega) (by omega)))
    (Squarefree.squarefree_of_dvd hk hs.2))

theorem one_mem_selbergDivisorSupport {Q : Nat} (hQ : 1 <= Q) :
    Membership.mem (selbergDivisorSupport Q) 1 := by
  simp [selbergDivisorSupport, hQ]

theorem card_selbergDivisorSupport_le (Q : Nat) :
    (selbergDivisorSupport Q).card <= Q := by
  calc
    (selbergDivisorSupport Q).card <= (Finset.Icc 1 Q).card := Finset.card_filter_le _ _
    _ = Q := by simp

noncomputable def selbergReciprocalNu : ArithmeticFunction Real where
  toFun d := Inv.inv (d : Real)
  map_zero' := by simp

theorem selbergReciprocalNu_multiplicative : selbergReciprocalNu.IsMultiplicative := by
  constructor
  next => simp [selbergReciprocalNu]
  next =>
    intro m n _
    simp [selbergReciprocalNu, Nat.cast_mul, mul_comm]

private theorem selbergReciprocalNu_prime_lt_one {p : Nat} (hp : Nat.Prime p) :
    selbergReciprocalNu p < 1 := by
  change Inv.inv (p : Real) < 1
  have hp0 : Not ((p : Real) = 0) := by exact_mod_cast hp.ne_zero
  have he : (p : Real)*Inv.inv (p : Real) = 1 := by field_simp
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  by_contra hh
  have hge : (1 : Real) <= Inv.inv (p : Real) := not_lt.mp hh
  have hm := _root_.mul_le_mul_of_nonneg_left hge (show (0 : Real) <= p by positivity)
  nlinarith

/-- The actual full integer interval, with reciprocal divisibility density. -/
noncomputable def intervalReciprocalSieve (L U Q : Nat) : BoundingSieve where
  support := Finset.Ioc L U
  prodPrimes := selbergPrimeProduct Q
  prodPrimes_squarefree := selbergPrimeProduct_squarefree Q
  weights := fun _ => 1
  weights_nonneg := fun _ => by norm_num
  totalMass := (U : Real)-L
  nu := selbergReciprocalNu
  nu_mult := selbergReciprocalNu_multiplicative
  nu_pos_of_prime := fun p hp _ => by
    change (0 : Real) < Inv.inv (p : Real)
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := fun p hp _ => selbergReciprocalNu_prime_lt_one hp

theorem intervalReciprocalSieve_terms (L U Q d : Nat) :
    (intervalReciprocalSieve L U Q).selbergTerms d = Inv.inv (d.totient : Real) := by
  rw [BoundingSieve.selbergTerms_apply]
  change Inv.inv (d : Real)*d.primeFactors.prod (fun p => Inv.inv (1-Inv.inv (p : Real))) =
    Inv.inv (d.totient : Real)
  simpa only [zpow_neg_one] using Nat.reciprocal_totient_euler_identity d

theorem intervalReciprocalSieve_denominator (L U Q : Nat) :
    (intervalReciprocalSieve L U Q).finiteSelbergDenominator (selbergDivisorSupport Q) =
      squarefreeReciprocalTotientSum Q := by
  unfold BoundingSieve.finiteSelbergDenominator squarefreeReciprocalTotientSum selbergDivisorSupport
  apply Finset.sum_congr rfl
  intro d _
  simpa only [zpow_neg_one] using intervalReciprocalSieve_terms L U Q d

end Nat
