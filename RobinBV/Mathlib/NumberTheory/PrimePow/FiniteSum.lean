/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.Interval.Finset.Nat

/-!
# Complete finite reindexing of prime-power-supported sums

A weight supported on positive prime powers can be summed over the integers
that meet a modulus by summing over all prime divisors of that modulus and
every admissible positive exponent. The cutoff is exact, including zero.
-/

set_option autoImplicit false

namespace Nat

/-- The complete finite prime-power carrier is in bijection with its unique
prime base and positive exponent. Arbitrary additive weights are preserved. -/
theorem sum_nonCoprime_primePowers_eq
    {R : Type*} [AddCommMonoid R] (f : Nat -> R)
    {N : Nat} (hN : Not (N = 0)) (x : Nat) :
    Finset.sum ((Finset.Icc 1 x).filter
      (fun n => And (Not (Nat.Coprime n N)) (IsPrimePow n))) f =
      Finset.sum N.primeFactors (fun p =>
        Finset.sum (Finset.Icc 1 (Nat.log p x)) (fun k => f (p ^ k))) := by
  classical
  by_cases hx : x = 0
  case pos =>
    subst x
    simp
  case neg =>
    let S : Finset (Sigma (fun _ : Nat => Nat)) :=
      N.primeFactors.sigma (fun p => Finset.Icc 1 (Nat.log p x))
    let T : Finset Nat := (Finset.Icc 1 x).filter
      (fun n => And (Not (Nat.Coprime n N)) (IsPrimePow n))
    have hReindex : Finset.sum S (fun a => f (a.1 ^ a.2)) = Finset.sum T f := by
      apply Finset.sum_bij (fun a _ => a.1 ^ a.2)
      next =>
        intro a ha
        have hData := Finset.mem_sigma.mp ha
        have hp := Nat.mem_primeFactors.mp hData.1
        have hk := Finset.mem_Icc.mp hData.2
        have hkPos : 0 < a.2 := by omega
        have hPowPos : 0 < a.1 ^ a.2 := Nat.pow_pos hp.1.pos
        have hPowLe : a.1 ^ a.2 <= x := Nat.pow_le_of_le_log hx hk.2
        have hBad : Not (Nat.Coprime (a.1 ^ a.2) N) := by
          intro hCoprime
          exact (hp.1.coprime_iff_not_dvd.mp
            (hCoprime.of_dvd_left (dvd_pow_self a.1 hkPos.ne'))) hp.2.1
        have hPrimePow : IsPrimePow (a.1 ^ a.2) :=
          (isPrimePow_nat_iff _).2 (Exists.intro a.1 (Exists.intro a.2
            (And.intro hp.1 (And.intro hkPos rfl))))
        exact Finset.mem_filter.mpr (And.intro
          (Finset.mem_Icc.mpr (And.intro (by omega) hPowLe))
          (And.intro hBad hPrimePow))
      next =>
        intro a ha b hb hEq
        have haData := Finset.mem_sigma.mp ha
        have hbData := Finset.mem_sigma.mp hb
        have hp := (Nat.mem_primeFactors.mp haData.1).1
        have hq := (Nat.mem_primeFactors.mp hbData.1).1
        have hk : Not (a.2 = 0) := by have h := (Finset.mem_Icc.mp haData.2).1; omega
        have hl : Not (b.2 = 0) := by have h := (Finset.mem_Icc.mp hbData.2).1; omega
        have hUnique := hp.pow_inj' hq hk hl hEq
        exact Sigma.ext hUnique.1 (heq_of_eq hUnique.2)
      next =>
        intro n hn
        have hnData := Finset.mem_filter.mp hn
        have hnRange := Finset.mem_Icc.mp hnData.1
        have hWitness := (isPrimePow_nat_iff n).1 hnData.2.2
        choose p k hp hk hPow using hWitness
        have hpDiv : Dvd.dvd p N := by
          by_contra hNot
          have hCoprime := (hp.coprime_iff_not_dvd.mpr hNot).pow_left k
          rw [hPow] at hCoprime
          exact hnData.2.1 hCoprime
        have hpMem : Membership.mem N.primeFactors p :=
          Nat.mem_primeFactors.mpr (And.intro hp (And.intro hpDiv hN))
        have hkLe : k <= Nat.log p x :=
          Nat.le_log_of_pow_le hp.one_lt (hPow.trans_le hnRange.2)
        let a : Sigma (fun _ : Nat => Nat) := Sigma.mk p k
        have ha : Membership.mem S a :=
          Finset.mem_sigma.mpr (And.intro hpMem
            (Finset.mem_Icc.mpr (And.intro (show 1 <= k by omega) hkLe)))
        exact Exists.intro a (Exists.intro ha hPow)
      next =>
        intro a ha
        rfl
    rw [Finset.sum_sigma] at hReindex
    exact hReindex.symm

/-- Remove non-prime-power indices from a supported weight and reindex every
remaining noncoprime term by its unique prime divisor of the modulus. -/
theorem sum_nonCoprime_eq_sum_primeFactors_sum_pow
    {R : Type*} [AddCommMonoid R] (f : Nat -> R)
    (hSupport : forall n : Nat, Not (IsPrimePow n) -> f n = 0)
    {N : Nat} (hN : Not (N = 0)) (x : Nat) :
    Finset.sum (Finset.Icc 1 x) (fun n =>
      if Nat.Coprime n N then 0 else f n) =
        Finset.sum N.primeFactors (fun p =>
          Finset.sum (Finset.Icc 1 (Nat.log p x)) (fun k => f (p ^ k))) := by
  classical
  rw [<- sum_nonCoprime_primePowers_eq f hN x, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hCoprime : Nat.Coprime n N
  case pos =>
    rw [if_pos hCoprime, if_neg (fun h => h.1 hCoprime)]
  case neg =>
    by_cases hPower : IsPrimePow n
    case pos =>
      rw [if_neg hCoprime, if_pos (And.intro hCoprime hPower)]
    case neg =>
      rw [if_neg hCoprime, if_neg (fun h => hPower h.2), hSupport n hPower]

end Nat
