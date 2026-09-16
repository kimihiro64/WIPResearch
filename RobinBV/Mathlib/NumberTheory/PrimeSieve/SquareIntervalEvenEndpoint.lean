/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalSuccessorReflection

/-!
# Exact quadratic classification of the even successor endpoint

The endpoint is (n+1)(n+3). Its actual rough-sieve weight is negative precisely
at p^2(p^2-2), with both p and p^2-2 prime. Applying this classification to the
full reflected comparison removes every other prime-admission endpoint loss.
The retained paired-sum positivity is not asserted.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- The full point weight equals the incidence polynomial on an actual rough survivor. -/
theorem squareJointPointWeight_eq_on_rough {n m : Nat} (hn : 2<=n)
    (hm : Membership.mem (squareRoughSurvivors n) m) :
    squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n) m =
      jointIncidenceWeight (mediumPrimeCount n m) := by
  have hs := hm
  rw [rough_survivors_eq_small_sieve hn] at hs
  unfold squareJointPointWeight mediumPrimeCount
  rw [if_pos (Finset.mem_filter.mp hs).2, <- mediumPrimeDivisors_eq_medium_filter hm]

/-- An even unpaired rough endpoint has a prime first factor and a prime or prime-square second factor. -/
theorem squareSuccessorUnpaired_even_rough_factors {n : Nat} (hn : 2<=n)
    (he : n%2=0) (hm : Membership.mem (squareRoughSurvivors (n+1)) (squareSuccessorUnpaired n)) :
    Nat.Prime (n+1) /\ (Nat.Prime (n+3) \/ exists p : Nat, Nat.Prime p /\ p*p=n+3) := by
  have hcut := (Finset.mem_filter.mp hm).2.2.2.2
  have hqprime : Nat.Prime (n+1) := by
    by_contra hc
    have hsq := Nat.minFac_sq_le_self (show 0<n+1 by omega) hc
    have hpf := Nat.minFac_prime (show Not (n+1=1) by omega)
    have hd : Dvd.dvd (n+1).minFac (squareSuccessorUnpaired n) := by
      rw [squareSuccessorUnpaired_even he]
      exact dvd_mul_of_dvd_left (Nat.minFac_dvd (n+1)) (n+3)
    have hlo := hcut _ hpf hd
    nlinarith
  refine And.intro hqprime ?_
  by_cases hc : Nat.Prime (n+3)
  next => exact Or.inl hc
  next =>
    let p := (n+3).minFac
    have hp : Nat.Prime p := Nat.minFac_prime (show Not (n+3=1) by omega)
    have hsq : p*p<=n+3 := by
      have hh := Nat.minFac_sq_le_self (show 0<n+3 by omega) hc
      simpa only [p, pow_two] using hh
    have hd : Dvd.dvd p (squareSuccessorUnpaired n) := by
      rw [squareSuccessorUnpaired_even he]
      exact dvd_mul_of_dvd_right (Nat.minFac_dvd (n+3)) (n+1)
    have hlo := hcut p hp hd
    have hodd : p%2=1 := by
      apply hp.eq_two_or_odd.resolve_left
      intro hp2
      rw [hp2] at hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      have ho := (Finset.mem_filter.mp hm).2.2.2.1
      omega
    have hsqodd : (p*p)%2=1 := by rw [Nat.mul_mod, hodd]
    exact Or.inr (Exists.intro p (And.intro hp (by omega)))

/-- A twin-prime endpoint is a semiprime of native weight zero. -/
theorem squareSuccessorUnpaired_twin_weight {n : Nat} (hn : 2<=n) (he : n%2=0)
    (hm : Membership.mem (squareRoughSurvivors (n+1)) (squareSuccessorUnpaired n))
    (hp : Nat.Prime (n+1)) (hq : Nat.Prime (n+3)) :
    squareJointPointWeight (squareSmallOddPrimes (n+1)) (squareMediumOddPrimes (n+1))
      (squareSuccessorUnpaired n)=0 := by
  have hb := mem_oddMultiplesInSquare_one_iff.mp (squareSuccessorUnpaired_mem n)
  rw [squareSuccessorUnpaired_even he] at hb
  rw [squareJointPointWeight_eq_on_rough (by omega) hm, mediumPrimeCount,
    squareSuccessorUnpaired_even he,
    mediumPrimeDivisors_two hp hq (by omega) hb.1 hb.2.1]
  norm_num [jointIncidenceWeight]

/-- The prime-square exceptional endpoint satisfies every actual roughness restriction. -/
theorem squareSuccessorUnpaired_square_rough {n p : Nat} (hn : 2<=n) (he : n%2=0)
    (hq : Nat.Prime (n+1)) (hp : Nat.Prime p) (hsq : p*p=n+3) :
    Membership.mem (squareRoughSurvivors (n+1)) (squareSuccessorUnpaired n) := by
  have hb := mem_oddMultiplesInSquare_one_iff.mp (squareSuccessorUnpaired_mem n)
  have heq : squareSuccessorUnpaired n=p*p*(n+1) := by
    rw [squareSuccessorUnpaired_even he, hsq]
    ring
  apply Finset.mem_filter.mpr
  refine And.intro (Finset.mem_range.mpr hb.2.1)
    (And.intro (by nlinarith [hb.1]) (And.intro hb.1 (And.intro hb.2.2 ?_)))
  intro r hr hd
  rw [heq] at hd
  rcases hr.dvd_mul.mp hd with hleft | hright
  next =>
    have hrp : Dvd.dvd r p := (hr.dvd_mul.mp hleft).elim id id
    have h := (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
    rw [h, hsq]
    omega
  next =>
    have h := (Nat.prime_dvd_prime_iff_eq hr hq).mp hright
    rw [h]
    nlinarith

/-- The exceptional quadratic endpoint has native weight exactly minus one. -/
theorem squareSuccessorUnpaired_square_weight {n p : Nat} (hn : 2<=n) (he : n%2=0)
    (hq : Nat.Prime (n+1)) (hp : Nat.Prime p) (hsq : p*p=n+3) :
    squareJointPointWeight (squareSmallOddPrimes (n+1)) (squareMediumOddPrimes (n+1))
      (squareSuccessorUnpaired n) = -1 := by
  have hm := squareSuccessorUnpaired_square_rough hn he hq hp hsq
  have heq : squareSuccessorUnpaired n=p*p*(n+1) := by
    rw [squareSuccessorUnpaired_even he, hsq]
    ring
  have hhi := (mem_oddMultiplesInSquare_one_iff.mp (squareSuccessorUnpaired_mem n)).2.1
  rw [heq] at hhi
  have hne : Not (p=n+1) := by nlinarith
  rw [squareJointPointWeight_eq_on_rough (by omega) hm, mediumPrimeCount, heq,
    mediumPrimeDivisors_three hp hp hq le_rfl (by nlinarith) hhi (by omega) (by omega)]
  simp [jointIncidenceWeight, hne]

/-- The entire even endpoint loss is exactly the stated prime-square indicator. -/
theorem squareSuccessorUnpaired_even_weight {n : Nat} (hn : 2<=n) (he : n%2=0) :
    squareJointPointWeight (squareSmallOddPrimes (n+1)) (squareMediumOddPrimes (n+1))
      (squareSuccessorUnpaired n) =
      if Nat.Prime (n+1) /\ (exists p : Nat, Nat.Prime p /\ p*p=n+3) then -1 else 0 := by
  by_cases hex : Nat.Prime (n+1) /\ (exists p : Nat, Nat.Prime p /\ p*p=n+3)
  next =>
    rw [if_pos hex]
    choose p hp using hex.2
    exact squareSuccessorUnpaired_square_weight hn he hex.1 hp.1 hp.2
  next =>
    rw [if_neg hex]
    by_cases hs : forall p, Membership.mem (squareSmallOddPrimes (n+1)) p ->
        Not (Dvd.dvd p (squareSuccessorUnpaired n))
    next =>
      have hm : Membership.mem (squareRoughSurvivors (n+1)) (squareSuccessorUnpaired n) := by
        rw [rough_survivors_eq_small_sieve (by omega)]
        exact Finset.mem_filter.mpr (And.intro (squareSuccessorUnpaired_mem n) hs)
      have hc := squareSuccessorUnpaired_even_rough_factors hn he hm
      rcases hc.2 with htwin | hsquare
      next => exact squareSuccessorUnpaired_twin_weight hn he hm hc.1 htwin
      next => exact False.elim (hex (And.intro hc.1 hsquare))
    next => simp only [squareJointPointWeight, hs, if_false]

/-- At prime successors the full native joint comparison has only the explicit prime-square endpoint loss. -/
theorem successor_joint_floor_reflection_prime_exact {n : Nat} (hn : 2<=n)
    (hp : Nat.Prime (n+1)) :
    2*(3*squareIncidenceFloor (n+1) 0-3*squareIncidenceFloor (n+1) 1+
      2*squareIncidenceFloor (n+1) 2) -
      (3*squareIncidenceFloor n 0-3*squareIncidenceFloor n 1+2*squareIncidenceFloor n 2) =
    (oddMultiplesInSquare n 1).sum (fun m =>
      2*squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n)
          (squareSuccessorReflection n m)-
        squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n) m) -
      (if exists p : Nat, Nat.Prime p /\ p*p=n+3 then 2 else 0) := by
  have hodd := hp.eq_two_or_odd.resolve_left (show Not (n+1=2) by omega)
  have he : n%2=0 := by omega
  have h := squareJointPacket_prime_reflection_exact hn hp
  rw [squareJointPacket_actual (show 2<=n+1 by omega),
    squareSuccessorUnpaired_even_weight hn he] at h
  simp only [hp, true_and] at h
  simp only [Finset.sum_sub_distrib, <- Finset.mul_sum]
  rw [<- squareJointPacket_eq_point_sum, squareJointPacket_actual hn]
  split_ifs at * <;> omega

end Nat.PrimeSieve
