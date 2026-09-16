/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalDivisorError
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalRoughAllowance

/-!
# SquareIntervalFivePrimePrefix

Explicit finite interval estimates used in signed prime-candidate accounting.
All constants and endpoint conditions are retained; no prime-existence result
is claimed by a negative lower envelope.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

noncomputable def fivePrimePrefix : Finset Nat := {3,5,7,11,13}

theorem fivePrimePrefix_prime {p : Nat} (hp : Membership.mem fivePrimePrefix p) :
    Nat.Prime p := by
  simp only [fivePrimePrefix, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide

/-- All five prefix primes and all31 nonempty subset errors are retained.
The finite subset expansion leaves n universally quantified. -/
theorem five_prime_prefix_card_upper (n : Nat) :
    ((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real) <=
      (384/1001 : Real)*n+31 := by
  have hi := prefix_card_eq_signed_packet fivePrimePrefix n
    (fun p hp => fivePrimePrefix_prime hp)
  have hr := congrArg (fun v : Int => (v : Real)) hi
  have hpow : fivePrimePrefix.powerset =
      {(Finset.empty : Finset Nat), {3}, {5}, {3,5}, {7}, {3,7}, {5,7}, {3,5,7}, {11}, {3,11}, {5,11}, {3,5,11}, {7,11}, {3,7,11}, {5,7,11}, {3,5,7,11}, {13}, {3,13}, {5,13}, {3,5,13}, {7,13}, {3,7,13}, {5,7,13}, {3,5,7,13}, {11,13}, {3,11,13}, {5,11,13}, {3,5,11,13}, {7,11,13}, {3,7,11,13}, {5,7,11,13}, {3,5,7,11,13}} := by decide
  rw [signedOddSquarePacket, hpow] at hr
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton] at hr
  norm_num [Finset.prod_insert, Finset.empty] at hr
  push_cast at hr
  have h1 : (oddMultiplesInSquare n 1).card = n := by
    have h := card_oddMultiplesInSquare n (d := 1) (by decide)
    simp only [Nat.div_one] at h
    omega
  have h1r : ((oddMultiplesInSquare n 1).card : Real) = n := by exact_mod_cast h1
  have h3 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 3) (by decide))).1
  have h5 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 5) (by decide))).1
  have h15 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 15) (by decide))).2
  have h7 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 7) (by decide))).1
  have h21 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 21) (by decide))).2
  have h35 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 35) (by decide))).2
  have h105 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 105) (by decide))).1
  have h11 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 11) (by decide))).1
  have h33 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 33) (by decide))).2
  have h55 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 55) (by decide))).2
  have h165 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 165) (by decide))).1
  have h77 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 77) (by decide))).2
  have h231 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 231) (by decide))).1
  have h385 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 385) (by decide))).1
  have h1155 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 1155) (by decide))).2
  have h13 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 13) (by decide))).1
  have h39 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 39) (by decide))).2
  have h65 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 65) (by decide))).2
  have h195 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 195) (by decide))).1
  have h91 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 91) (by decide))).2
  have h273 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 273) (by decide))).1
  have h455 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 455) (by decide))).1
  have h1365 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 1365) (by decide))).2
  have h143 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 143) (by decide))).2
  have h429 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 429) (by decide))).1
  have h715 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 715) (by decide))).1
  have h2145 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 2145) (by decide))).2
  have h1001 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 1001) (by decide))).1
  have h3003 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 3003) (by decide))).2
  have h5005 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 5005) (by decide))).2
  have h15015 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 15015) (by decide))).1
  linarith only [hr, h1r, h3, h5, h15, h7, h21, h35, h105, h11, h33, h55, h165, h77, h231, h385, h1155, h13, h39, h65, h195, h91, h273, h455, h1365, h143, h429, h715, h2145, h1001, h3003, h5005, h15015]


/-- Explicit lower supply from all31 nonempty prefix corrections; n is arbitrary. -/
theorem five_prime_prefix_card_lower (n : Nat) :
    (384/1001 : Real)*n-31 <=
      ((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real) := by
  have hi := prefix_card_eq_signed_packet fivePrimePrefix n
    (fun p hp => fivePrimePrefix_prime hp)
  have hr := congrArg (fun v : Int => (v : Real)) hi
  have hpow : fivePrimePrefix.powerset =
      {(Finset.empty : Finset Nat), {3}, {5}, {3,5}, {7}, {3,7}, {5,7}, {3,5,7}, {11}, {3,11}, {5,11}, {3,5,11}, {7,11}, {3,7,11}, {5,7,11}, {3,5,7,11}, {13}, {3,13}, {5,13}, {3,5,13}, {7,13}, {3,7,13}, {5,7,13}, {3,5,7,13}, {11,13}, {3,11,13}, {5,11,13}, {3,5,11,13}, {7,11,13}, {3,7,11,13}, {5,7,11,13}, {3,5,7,11,13}} := by decide
  rw [signedOddSquarePacket, hpow] at hr
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton] at hr
  norm_num [Finset.prod_insert, Finset.empty] at hr
  have h1 : (oddMultiplesInSquare n 1).card = n := by
    have h := card_oddMultiplesInSquare n (d := 1) (by decide)
    simp only [Nat.div_one] at h
    omega
  have h1r : ((oddMultiplesInSquare n 1).card : Real) = n := by exact_mod_cast h1
  have h3 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 3) (by decide))).2
  have h5 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 5) (by decide))).2
  have h15 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 15) (by decide))).1
  have h7 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 7) (by decide))).2
  have h21 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 21) (by decide))).1
  have h35 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 35) (by decide))).1
  have h105 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 105) (by decide))).2
  have h11 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 11) (by decide))).2
  have h33 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 33) (by decide))).1
  have h55 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 55) (by decide))).1
  have h165 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 165) (by decide))).2
  have h77 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 77) (by decide))).1
  have h231 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 231) (by decide))).2
  have h385 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 385) (by decide))).2
  have h1155 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 1155) (by decide))).1
  have h13 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 13) (by decide))).2
  have h39 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 39) (by decide))).1
  have h65 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 65) (by decide))).1
  have h195 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 195) (by decide))).2
  have h91 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 91) (by decide))).1
  have h273 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 273) (by decide))).2
  have h455 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 455) (by decide))).2
  have h1365 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 1365) (by decide))).1
  have h143 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 143) (by decide))).1
  have h429 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 429) (by decide))).2
  have h715 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 715) (by decide))).2
  have h2145 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 2145) (by decide))).1
  have h1001 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 1001) (by decide))).2
  have h3003 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 3003) (by decide))).1
  have h5005 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 5005) (by decide))).1
  have h15015 := (abs_lt.mp (odd_interval_abs_unit_error n (d := 15015) (by decide))).2
  linarith only [hr, h1r, h3, h5, h15, h7, h21, h35, h105, h11, h33, h55, h165, h77, h231, h385, h1155, h13, h39, h65, h195, h91, h273, h455, h1365, h143, h429, h715, h2145, h1001, h3003, h5005, h15015]

theorem five_prime_prefix_card_pos {n : Nat} (hn : 81 <= n) :
    0 < (oddSievedOwnerInSquare n 1 fivePrimePrefix).card := by
  have h := five_prime_prefix_card_lower n
  have hnR : (81 : Real) <= n := by exact_mod_cast hn
  have hp : (0 : Real) < (oddSievedOwnerInSquare n 1 fivePrimePrefix).card := by
    linarith only [h, hnR]
  exact_mod_cast hp

end Nat.PrimeSieve
