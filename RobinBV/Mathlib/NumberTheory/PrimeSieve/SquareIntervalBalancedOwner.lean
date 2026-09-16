/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalBandCoverage
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalLogAllowance

/-!
# Screened balanced owners

Actual owner cells above half the square index have prime cofactors after a
finite square-root screen. Their cofactor injection gives an independent
explicit logarithmic upper bound, without charging all prefix candidates.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

theorem squareBalanced_cofactor_le {n p q : Nat}
    (hp : n < 2*p) (hprod : p*q <= n*n+2*n) : q <= 2*n+1 := by
  by_contra h
  have hq : 2*n+2 <= q := by omega
  have hn : n+1 <= 2*p := by omega
  have hmul := Nat.mul_le_mul_left p hq
  have hmul' := Nat.mul_le_mul_right (n+1) hn
  nlinarith

/-- The full balanced family injects into its prime cofactor interval. -/
theorem card_squareBalancedPairs_le_prime_cofactors {n : Nat}
    (s : Finset (Prod Nat Nat))
    (hs : forall x, Membership.mem s x ->
      x.1%2 = 1 /\ x.1 <= n /\ n < 2*x.1 /\ Nat.Prime x.2 /\
      n*n < x.1*x.2 /\ x.1*x.2 <= n*n+2*n) :
    s.card <= ((Finset.Icc (n+1) (2*n+1)).filter Nat.Prime).card := by
  have hlarge (x : Prod Nat Nat) (hx : Membership.mem s x) : n < x.2 := by
    have hh := hs x hx
    by_contra h
    have hq : x.2 <= n := by omega
    have hpq := Nat.mul_le_mul hh.2.1 hq
    omega
  apply Finset.card_le_card_of_injOn Prod.snd
  next =>
    intro x hx
    have hh := hs x hx
    have hq := hlarge x hx
    have hu := squareBalanced_cofactor_le hh.2.2.1 hh.2.2.2.2.2
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_Icc.mpr (And.intro (by omega) hu)) hh.2.2.2.1)
  next =>
    intro x hx y hy he
    have hh := hs x hx
    have hk := hs y hy
    have hlo : n*n < x.2*x.1 := by nlinarith [hh.2.2.2.2.1]
    have hhi : x.2*x.1 < (n+1)*(n+1) := by nlinarith [hh.2.2.2.2.2]
    have hlo' : n*n < x.2*y.1 := by rw [he]; nlinarith [hk.2.2.2.2.1]
    have hhi' : x.2*y.1 < (n+1)*(n+1) := by rw [he]; nlinarith [hk.2.2.2.2.2]
    have hp := odd_cofactor_unique (hlarge x hx) hh.1 hk.1 hlo hhi hlo' hhi'
    exact Prod.ext hp he

/-- A finite square-root screen, not the all-primes screen that annihilates
every collision in the complete family. -/
noncomputable def balancedOwnerScreen (n : Nat) : Finset Nat :=
  (Finset.range (2*n+2)).filter (fun p =>
    Nat.Prime p /\ p%2 = 1 /\ p*p <= 2*n+1)

theorem balancedOwnerScreen_complete {n p : Nat} (hp : Nat.Prime p)
    (ho : p%2 = 1) (hs : p*p <= 2*n+1) : Membership.mem (balancedOwnerScreen n) p := by
  apply Finset.mem_filter.mpr
  refine And.intro (Finset.mem_range.mpr ?_) (And.intro hp (And.intro ho hs))
  nlinarith [Nat.mul_le_mul_left p hp.two_le]

/-- In the balanced owner band, screening all small factors of the cofactor
proves actual cofactor primality; it is not an extra source assumption. -/
theorem screened_balanced_owner_cofactor_prime
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T p q : Nat} {S R : Finset Nat}
    (hn : 9 <= n)
    (hR : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= 2*n+1 -> Membership.mem R ell)
    (hx : Membership.mem (ownerLineFamilyHighFactorCells Gamma n T S R) (Prod.mk p q))
    (hbal : n < 2*p) : Nat.Prime q := by
  have hpCell := Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hoCell := Finset.mem_filter.mp hpCell.1
  have hc := Finset.mem_filter.mp hoCell.1
  have hpn : p <= n := by
    have h := Finset.mem_range.mp (Finset.mem_product.mp hc.1).1
    omega
  have hlo : n*n < p*q := hc.2.2.1
  have hhi : p*q <= n*n+2*n := by have h := hc.2.2.2.1; nlinarith
  have hqn : n < q := by
    by_contra h
    have hh := Nat.mul_le_mul hpn (show q <= n by omega)
    omega
  have hqtop := squareBalanced_cofactor_le hbal hhi
  have hqodd : q%2 = 1 := hc.2.2.2.2.2.1
  by_contra hcomp
  choose a ha using exists_minFac_mul (show 2 <= q by omega) hcomp
  have hr : Nat.Prime q.minFac := Nat.minFac_prime (by omega)
  have had : Dvd.dvd a q := by rw [ha.2]; exact dvd_mul_left a q.minFac
  have hra : q.minFac <= a := Nat.minFac_le_of_dvd ha.1 had
  have hrsq : q.minFac*q.minFac <= q := by
    have h := Nat.mul_le_mul_left q.minFac hra
    rw [<- ha.2] at h
    exact h
  have hrodd : q.minFac%2 = 1 := hr.eq_two_or_odd.resolve_left (by
    intro he
    have hd := Nat.minFac_dvd q
    rw [he] at hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega)
  have hp5 : 5 <= p := by omega
  have hpp : 2*n+1 < p*p := by
    nlinarith [Nat.mul_le_mul_left p hp5]
  have hrp : q.minFac < p := by
    by_contra hh
    have hm := Nat.mul_le_mul (show p <= q.minFac by omega) (show p <= q.minFac by omega)
    omega
  exact (hoCell.2 q.minFac (hR q.minFac hr hrodd (by omega))).2 hrp (Nat.minFac_dvd q)

/-- Apply the existing balanced cofactor injection to actual screened cells.
No candidate is charged merely for belonging to the prefix survivor set. -/
theorem screened_balanced_owner_card_le_prime_cofactors
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 9 <= n)
    (hR : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= 2*n+1 -> Membership.mem R ell) :
    ((ownerLineFamilyHighFactorCells Gamma n T S R).filter
      (fun x => n < 2*x.1)).card <=
        ((Finset.Icc (n+1) (2*n+1)).filter Nat.Prime).card := by
  apply card_squareBalancedPairs_le_prime_cofactors
  intro x hx
  have hd := Finset.mem_filter.mp hx
  have hpCell := Finset.mem_filter.mp (Finset.mem_filter.mp hd.1).1
  have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hpCell.1).1
  have hpn : x.1 <= n := by
    have h := Finset.mem_range.mp (Finset.mem_product.mp hc.1).1
    omega
  have hprime := screened_balanced_owner_cofactor_prime hn hR hd.1 hd.2
  refine And.intro hc.2.2.2.2.1 (And.intro hpn (And.intro hd.2
    (And.intro hprime (And.intro hc.2.2.1 ?_))))
  have h := hc.2.2.2.1
  nlinarith

theorem balanced_prime_cofactors_le_log_sieve {n Q : Nat}
    (hQ1 : 1 <= Q) (hQn : Q <= n) :
    (((Finset.Icc (n+1) (2*n+1)).filter Nat.Prime).card : Real) <=
      ((n : Real)+1)/Real.log ((Q : Real)+1)+(Q : Real)^2 := by
  have hsub : (Finset.Icc (n+1) (2*n+1)).filter Nat.Prime <=
      (Finset.Ioc n (2*n+1)).filter (fun m => Nat.Coprime (Nat.selbergPrimeProduct Q) m) := by
    intro m hm
    have hd := Finset.mem_filter.mp hm
    have hi := Finset.mem_Icc.mp hd.1
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_Ioc.mpr (And.intro (by omega) hi.2)) ?_
    apply Nat.coprime_of_dvd
    intro p hp hpP hpm
    have hpQ := (Nat.prime_dvd_selbergPrimeProduct_iff hp).mp hpP
    have he := (hd.2.eq_one_or_self_of_dvd p hpm).resolve_left hp.ne_one
    omega
  have hc : (((Finset.Icc (n+1) (2*n+1)).filter Nat.Prime).card : Real) <=
      (((Finset.Ioc n (2*n+1)).filter
        (fun m => Nat.Coprime (Nat.selbergPrimeProduct Q) m)).card : Real) := by
    exact_mod_cast Finset.card_le_card hsub
  have hs := Nat.card_sifted_interval_le_log_sieve (L := n) (U := 2*n+1) (by omega) hQ1
  push_cast at hs
  have he : 2*(n : Real)+1-n = n+1 := by ring
  rw [he] at hs
  exact hc.trans hs

noncomputable def balancedPrimeLogAllowance (n : Nat) : Real :=
  2*((n : Real)+1)/Real.squareSieveDenominator n+(n : Real)/(Real.log n)^2

/-- An explicit independent upper bound for the prime cofactor interval. -/
theorem balanced_prime_cofactors_le_explicit_log {n : Nat} (hn : 4 <= n) :
    (((Finset.Icc (n+1) (2*n+1)).filter Nat.Prime).card : Real) <=
      balancedPrimeLogAllowance n := by
  have hn4 : (4 : Real) <= n := by exact_mod_cast hn
  have hn1 : (1 : Real) < n := by linarith
  let Q := Real.squareSieveCutoff (n : Real)
  have hQ1 : 1 <= Q := Real.one_le_squareSieveCutoff hn1
  have hQsq := Real.squareSieveCutoff_sq_le_self hn4
  have hQ : Q*Q <= n := by
    have hQr : (Q : Real)*(Q : Real) <= n := by simpa only [pow_two] using hQsq
    exact_mod_cast hQr
  have hQn : Q <= n := by
    have h := Nat.mul_le_mul_left Q hQ1
    nlinarith
  have hs := balanced_prime_cofactors_le_log_sieve hQ1 hQn
  have hD := Real.squareSieveDenominator_pos hn1
  have hlog := Real.squareSieveCutoff_log_lower hn1
  have hmain : ((n : Real)+1)/Real.log ((Q : Real)+1) <=
      ((n : Real)+1)/(Real.squareSieveDenominator n/2) :=
    _root_.div_le_div_of_nonneg_left (by positivity)
      (_root_.div_pos hD (by norm_num)) hlog
  have herr := Real.squareSieveCutoff_sq_bound hn1
  have he : ((n : Real)+1)/(Real.squareSieveDenominator n/2) =
      2*((n : Real)+1)/Real.squareSieveDenominator n := by ring
  rw [he] at hmain
  exact hs.trans (_root_.add_le_add hmain herr)

/-- This bounds actual geometric owner cells, not all prefix candidates. -/
theorem screened_balanced_owner_card_le_explicit_log
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 9 <= n)
    (hR : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= 2*n+1 -> Membership.mem R ell) :
    (((ownerLineFamilyHighFactorCells Gamma n T S R).filter
      (fun x => n < 2*x.1)).card : Real) <= balancedPrimeLogAllowance n := by
  have hc : (((ownerLineFamilyHighFactorCells Gamma n T S R).filter
      (fun x => n < 2*x.1)).card : Real) <=
        (((Finset.Icc (n+1) (2*n+1)).filter Nat.Prime).card : Real) := by
    exact_mod_cast screened_balanced_owner_card_le_prime_cofactors hn hR
  exact hc.trans (balanced_prime_cofactors_le_explicit_log (by omega))

end Nat.PrimeSieve
