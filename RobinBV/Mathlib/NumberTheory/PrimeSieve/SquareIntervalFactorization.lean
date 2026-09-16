/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareInterval

/-!
# The prime, two-prime and three-prime partition

Excluding prime divisors whose square is at most the interval index leaves
at most three prime factors, counted with multiplicity.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

/-- Extract the least prime factor of a composite, retaining a nontrivial cofactor. -/
theorem exists_minFac_mul {m : Nat} (hm : 2 <= m) (hc : Not (Nat.Prime m)) :
    exists a : Nat, 2 <= a /\ m = m.minFac * a := by
  have hp : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
  choose a ha using Nat.minFac_dvd m
  refine Exists.intro a (And.intro ?_ ha)
  have ha0 : Not (a = 0) := by
    intro hz
    simp [hz] at ha
    omega
  have ha1 : Not (a = 1) := by
    intro ho
    apply hc
    have hmEq : m = m.minFac := by simpa only [ho, Nat.mul_one] using ha
    rw [hmEq]
    exact hp
  omega

/-- A rough integer below the next square has no divisor with four prime factors. -/
theorem not_four_prime_factors {n m p q r s : Nat} (hm : 0 < m)
    (hhi : m < (n + 1) * (n + 1))
    (hrough : forall t : Nat, Nat.Prime t -> Dvd.dvd t m -> n < t * t)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) (hs : Nat.Prime s) :
    Not (Dvd.dvd ((p * q) * (r * s)) m) := by
  intro hd
  have hpd : Dvd.dvd p m := dvd_trans
    (show Dvd.dvd p ((p * q) * (r * s)) from
      Exists.intro (q * (r * s)) (by ac_rfl)) hd
  have hqd : Dvd.dvd q m := dvd_trans
    (show Dvd.dvd q ((p * q) * (r * s)) from
      Exists.intro (p * (r * s)) (by ac_rfl)) hd
  have hrd : Dvd.dvd r m := dvd_trans
    (show Dvd.dvd r ((p * q) * (r * s)) from
      Exists.intro (p * q * s) (by ac_rfl)) hd
  have hsd : Dvd.dvd s m := dvd_trans
    (show Dvd.dvd s ((p * q) * (r * s)) from
      Exists.intro (p * q * r) (by ac_rfl)) hd
  have hbound := four_factor_lower_bound
    (hrough p hp hpd) (hrough q hq hqd) (hrough r hr hrd) (hrough s hs hsd)
  have hle := Nat.le_of_dvd hm hd
  omega

/-- Exact factorization alternatives at the square-root-of-index sieve cutoff. -/
theorem rough_prime_or_two_or_three {n m : Nat} (hm : 2 <= m)
    (hhi : m < (n + 1) * (n + 1))
    (hrough : forall t : Nat, Nat.Prime t -> Dvd.dvd t m -> n < t * t) :
    Nat.Prime m \/
      (exists p q : Nat, Nat.Prime p /\ Nat.Prime q /\ p <= q /\ m = p * q) \/
      (exists p q r : Nat, Nat.Prime p /\ Nat.Prime q /\ Nat.Prime r /\
        p <= q /\ q <= r /\ m = p * q * r) := by
  by_cases hmp : Nat.Prime m
  next => exact Or.inl hmp
  next =>
    choose a ha using exists_minFac_mul hm hmp
    let p := m.minFac
    have hp : Nat.Prime p := Nat.minFac_prime (by omega)
    have hma : m = p * a := ha.2
    have had : Dvd.dvd a m := by rw [hma]; exact dvd_mul_left a p
    have hpa : p <= a := Nat.minFac_le_of_dvd ha.1 had
    by_cases hap : Nat.Prime a
    next =>
      exact Or.inr (Or.inl (Exists.intro p (Exists.intro a
        (And.intro hp (And.intro hap (And.intro hpa hma))))))
    next =>
      choose b hb using exists_minFac_mul ha.1 hap
      let q := a.minFac
      have hq : Nat.Prime q := Nat.minFac_prime (by omega)
      have hab : a = q * b := hb.2
      have hqd : Dvd.dvd q m := dvd_trans (Nat.minFac_dvd a) had
      have hpq : p <= q := Nat.minFac_le_of_dvd hq.two_le hqd
      have hbd : Dvd.dvd b a := by rw [hab]; exact dvd_mul_left b q
      have hqb : q <= b := Nat.minFac_le_of_dvd hb.1 hbd
      by_cases hbp : Nat.Prime b
      next =>
        apply Or.inr
        apply Or.inr
        refine Exists.intro p (Exists.intro q (Exists.intro b
          (And.intro hp (And.intro hq (And.intro hbp
            (And.intro hpq (And.intro hqb ?_)))))))
        rw [hma, hab, Nat.mul_assoc]
      next =>
        choose c hc using exists_minFac_mul hb.1 hbp
        let r := b.minFac
        let s := c.minFac
        have hr : Nat.Prime r := Nat.minFac_prime (by omega)
        have hs : Nat.Prime s := Nat.minFac_prime (by omega)
        have hbc : b = r * c := hc.2
        choose d hd using Nat.minFac_dvd c
        have hfour : Dvd.dvd ((p * q) * (r * s)) m := by
          apply Exists.intro d
          calc
            m = p * (q * (r * (s * d))) := by rw [hma, hab, hbc, hd]
            _ = (p * q) * (r * s) * d := by simp [Nat.mul_assoc]
        exact False.elim (not_four_prime_factors (by omega) hhi hrough hp hq hr hs hfour)

/-- Exactly two ordered prime factors, counted with multiplicity. -/
def IsTwoPrime (m : Nat) : Prop :=
  exists p q : Nat, Nat.Prime p /\ Nat.Prime q /\ p <= q /\ m = p * q

/-- Exactly three ordered prime factors, counted with multiplicity. -/
def IsThreePrime (m : Nat) : Prop :=
  exists p q r : Nat, Nat.Prime p /\ Nat.Prime q /\ Nat.Prime r /\
    p <= q /\ q <= r /\ m = p * q * r

/-- A product of two nontrivial natural numbers is not prime. -/
theorem not_prime_of_two_factors {p q : Nat} (hp : 2 <= p) (hq : 2 <= q) :
    Not (Nat.Prime (p * q)) := by
  apply Nat.not_prime_of_dvd_of_ne (dvd_mul_right p q) (by omega)
  nlinarith

/-- The two-prime and prime alternatives are disjoint. -/
theorem IsTwoPrime.not_prime {m : Nat} (h : IsTwoPrime m) : Not (Nat.Prime m) := by
  choose p q hp using h
  rw [hp.2.2.2]
  exact not_prime_of_two_factors hp.1.two_le hp.2.1.two_le

/-- The three-prime and prime alternatives are disjoint. -/
theorem IsThreePrime.not_prime {m : Nat} (h : IsThreePrime m) : Not (Nat.Prime m) := by
  choose p q r hp using h
  rw [hp.2.2.2.2.2, Nat.mul_assoc]
  apply not_prime_of_two_factors hp.1.two_le
  have hq := hp.2.1.two_le
  have hr := hp.2.2.1.two_le
  nlinarith

/-- Two prime factors cannot equal three prime factors, even with repetitions. -/
theorem two_prime_product_ne_three {p q r s t : Nat}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hs : Nat.Prime s) (ht : Nat.Prime t) : Not (p * q = r * s * t) := by
  intro heq
  have hrd : Dvd.dvd r (p * q) := by
    rw [heq]
    exact Exists.intro (s * t) (by ac_rfl)
  rcases hr.dvd_mul.mp hrd with hrp | hrq
  next =>
    have hrep : r = p := (hp.eq_one_or_self_of_dvd r hrp).resolve_left hr.ne_one
    subst r
    have hqeq : q = s * t := Nat.eq_of_mul_eq_mul_left hp.pos (by
      simpa only [Nat.mul_assoc] using heq)
    apply not_prime_of_two_factors hs.two_le ht.two_le
    rw [hqeq] at hq
    exact hq
  next =>
    have hreq : r = q := (hq.eq_one_or_self_of_dvd r hrq).resolve_left hr.ne_one
    subst r
    have hpeq : p = s * t := Nat.eq_of_mul_eq_mul_left hq.pos (by
      calc
        q * p = p * q := Nat.mul_comm q p
        _ = q * (s * t) := by simpa only [Nat.mul_assoc] using heq)
    apply not_prime_of_two_factors hs.two_le ht.two_le
    rw [hpeq] at hp
    exact hp

/-- The two-prime and three-prime alternatives are disjoint. -/
theorem IsTwoPrime.not_threePrime {m : Nat} (h2 : IsTwoPrime m) :
    Not (IsThreePrime m) := by
  intro h3
  choose p q hp using h2
  choose r s t hr using h3
  apply two_prime_product_ne_three hp.1 hp.2.1 hr.1 hr.2.1 hr.2.2.1
  exact hp.2.2.2.symm.trans hr.2.2.2.2.2

end Nat.PrimeSieve
