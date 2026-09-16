/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalSuccessor

/-!
# Reflected ownership in the full joint successor comparison

The old odd candidates reflect across the common square onto all but one of the
new odd candidates. Both least-owner histories, the extra endpoint and every
signed incidence weight are retained. No positivity assertion is assumed.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- Reflection across the common square of two adjacent square intervals. -/
def squareSuccessorReflection (n m : Nat) : Nat := 2*((n+1)*(n+1))-m

/-- The single odd successor candidate outside the reflected predecessor interval. -/
def squareSuccessorUnpaired (n : Nat) : Nat := n*n+4*n+3-n%2

/-- The complete open-square interval condition for odd candidates. -/
theorem mem_oddMultiplesInSquare_one_iff {n m : Nat} :
    Membership.mem (oddMultiplesInSquare n 1) m <->
      n*n < m /\ m < (n+1)*(n+1) /\ m%2=1 := by
  simp only [oddMultiplesInSquare, oddMultiplesUpTo, Finset.mem_filter,
    Finset.mem_range, one_dvd, and_true]
  have hi : (n+1)*(n+1)=n*n+2*n+1 := by ring
  rw [hi]
  omega

/-- An actual reflected pair sums to twice the common square. -/
theorem squareSuccessorReflection_add {n m : Nat}
    (hm : Membership.mem (oddMultiplesInSquare n 1) m) :
    m+squareSuccessorReflection n m=2*((n+1)*(n+1)) := by
  have h := mem_oddMultiplesInSquare_one_iff.mp hm
  unfold squareSuccessorReflection
  omega

/-- Reflection sends every predecessor odd candidate into the successor interval. -/
theorem squareSuccessorReflection_mem {n m : Nat}
    (hm : Membership.mem (oddMultiplesInSquare n 1) m) :
    Membership.mem (oddMultiplesInSquare (n+1) 1) (squareSuccessorReflection n m) := by
  have h := mem_oddMultiplesInSquare_one_iff.mp hm
  have heq := squareSuccessorReflection_add hm
  apply mem_oddMultiplesInSquare_one_iff.mpr
  have hi : (n+1+1)*(n+1+1) = n*n+4*n+4 := by ring
  have hj : (n+1)*(n+1) = n*n+2*n+1 := by ring
  unfold squareSuccessorReflection at *
  simp only [hi, hj] at *
  omega

/-- The unpaired odd endpoint is always an actual successor candidate. -/
theorem squareSuccessorUnpaired_mem (n : Nat) :
    Membership.mem (oddMultiplesInSquare (n+1) 1) (squareSuccessorUnpaired n) := by
  apply mem_oddMultiplesInSquare_one_iff.mpr
  have hmod : n*n%2=n%2 := by
    rw [Nat.mul_mod]
    have h := Nat.mod_lt n (by decide : 0<2)
    by_cases hz : n%2=0
    next => rw [hz]
    next => rw [show n%2=1 by omega]
  unfold squareSuccessorUnpaired
  have hi : (n+1+1)*(n+1+1) = n*n+4*n+4 := by ring
  have hj : (n+1)*(n+1) = n*n+2*n+1 := by ring
  rw [hi, hj]
  omega

/-- No reflected predecessor candidate equals the unpaired endpoint. -/
theorem squareSuccessorReflection_ne_unpaired {n m : Nat}
    (hm : Membership.mem (oddMultiplesInSquare n 1) m) :
    Not (squareSuccessorReflection n m = squareSuccessorUnpaired n) := by
  have h := mem_oddMultiplesInSquare_one_iff.mp hm
  have heq := squareSuccessorReflection_add hm
  have hmod : n*n%2=n%2 := by
    rw [Nat.mul_mod]
    have h := Nat.mod_lt n (by decide : 0<2)
    by_cases hz : n%2=0
    next => rw [hz]
    next => rw [show n%2=1 by omega]
  have hj : (n+1)*(n+1) = n*n+2*n+1 := by ring
  rw [hj] at heq
  unfold squareSuccessorUnpaired
  omega

/-- The exact reflection image retains every successor candidate except one. -/
theorem squareSuccessorReflection_image (n : Nat) :
    (oddMultiplesInSquare n 1).image (squareSuccessorReflection n) =
      (oddMultiplesInSquare (n+1) 1).erase (squareSuccessorUnpaired n) := by
  ext r
  constructor
  next =>
    intro hr
    choose m hm using Finset.mem_image.mp hr
    rw [<- hm.2]
    exact Finset.mem_erase.mpr (And.intro (squareSuccessorReflection_ne_unpaired hm.1)
      (squareSuccessorReflection_mem hm.1))
  next =>
    intro hr
    have hr' := Finset.mem_erase.mp hr
    have h := mem_oddMultiplesInSquare_one_iff.mp hr'.2
    have hmod : n*n%2=n%2 := by
      rw [Nat.mul_mod]
      have hh := Nat.mod_lt n (by decide : 0<2)
      by_cases hz : n%2=0
      next => rw [hz]
      next => rw [show n%2=1 by omega]
    have hi : (n+1+1)*(n+1+1) = n*n+4*n+4 := by ring
    have hj : (n+1)*(n+1) = n*n+2*n+1 := by ring
    unfold squareSuccessorUnpaired at hr'
    rw [hi, hj] at h
    apply Finset.mem_image.mpr
    refine Exists.intro (2*((n+1)*(n+1))-r) (And.intro ?_ ?_)
    next =>
      apply mem_oddMultiplesInSquare_one_iff.mpr
      rw [hj]
      omega
    next => unfold squareSuccessorReflection; rw [hj]; omega

/-- Arbitrary integer weights reindex with the single endpoint retained. -/
theorem sum_squareSuccessor_reflection (n : Nat) (F : Nat -> Int) :
    (oddMultiplesInSquare (n+1) 1).sum F =
      (oddMultiplesInSquare n 1).sum (fun m => F (squareSuccessorReflection n m)) +
        F (squareSuccessorUnpaired n) := by
  have hinj : Set.InjOn (squareSuccessorReflection n) (oddMultiplesInSquare n 1) := by
    intro a ha b hb heq
    have ha' := squareSuccessorReflection_add ha
    have hb' := squareSuccessorReflection_add hb
    omega
  have himage := Finset.sum_image hinj (f := F)
  rw [squareSuccessorReflection_image] at himage
  rw [<- himage]
  exact (Finset.sum_erase_add _ _ (squareSuccessorUnpaired_mem n)).symm

/-- Every divisor of the common square root preserves divisibility across the pair. -/
theorem squareSuccessorReflection_dvd_iff {n m p : Nat}
    (hm : Membership.mem (oddMultiplesInSquare n 1) m) (hp : Dvd.dvd p (n+1)) :
    Dvd.dvd p (squareSuccessorReflection n m) <-> Dvd.dvd p m := by
  have heq := squareSuccessorReflection_add hm
  have hs : Dvd.dvd p (m+squareSuccessorReflection n m) := by
    rw [heq]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hp (n+1)) 2
  constructor
  next => intro hr; exact (Nat.dvd_add_iff_left hr).mpr hs
  next => intro hl; exact (Nat.dvd_add_iff_right hl).mpr hs

/-- Unequal least prime owners cannot have their smaller owner divide the center root. -/
theorem squareSuccessorReflection_unequal_owners {n m : Nat} (hn : 2<=n)
    (hm : Membership.mem (oddMultiplesInSquare n 1) m)
    (hne : Not (m.minFac=(squareSuccessorReflection n m).minFac)) :
    Not (Dvd.dvd (min m.minFac (squareSuccessorReflection n m).minFac) (n+1)) := by
  have hlo := (mem_oddMultiplesInSquare_one_iff.mp hm).1
  have hrlo := (mem_oddMultiplesInSquare_one_iff.mp (squareSuccessorReflection_mem hm)).1
  have hm2 := (Nat.minFac_prime (show Not (m=1) by nlinarith)).two_le
  have hr2 := (Nat.minFac_prime
    (show Not (squareSuccessorReflection n m=1) by nlinarith)).two_le
  intro hd
  by_cases hle : m.minFac <= (squareSuccessorReflection n m).minFac
  next =>
    rw [min_eq_left hle] at hd
    have h := Nat.minFac_le_of_dvd hm2
      ((squareSuccessorReflection_dvd_iff hm hd).mpr (Nat.minFac_dvd m))
    exact hne (by omega)
  next =>
    rw [min_eq_right (by omega)] at hd
    have h := Nat.minFac_le_of_dvd hr2
      ((squareSuccessorReflection_dvd_iff hm hd).mp
        (Nat.minFac_dvd (squareSuccessorReflection n m)))
    exact hne (by omega)

/-- The reflection of an old prime avoids every nonunit divisor of the center root. -/
theorem squareSuccessorReflection_prime_avoids_center {n m p : Nat} (hn : 2<=n)
    (hm : Membership.mem (oddMultiplesInSquare n 1) m) (hprime : Nat.Prime m)
    (hp : 2<=p) (hd : Dvd.dvd p (n+1)) :
    Not (Dvd.dvd p (squareSuccessorReflection n m)) := by
  intro hr
  have hpm := (squareSuccessorReflection_dvd_iff hm hd).mp hr
  have heq := (Nat.dvd_prime_two_le hprime hp).mp hpm
  have hle := Nat.le_of_dvd (show 0<n+1 by omega) hd
  have hlo := (mem_oddMultiplesInSquare_one_iff.mp hm).1
  nlinarith

/-- For even index the extra odd candidate has an explicit quadratic factorization. -/
theorem squareSuccessorUnpaired_even {n : Nat} (hn : n%2=0) :
    squareSuccessorUnpaired n=(n+1)*(n+3) := by
  simp only [squareSuccessorUnpaired, hn, Nat.sub_zero]
  ring

/-- The even-index unpaired candidate is composite. -/
theorem squareSuccessorUnpaired_even_not_prime {n : Nat} (hn : 2<=n)
    (heven : n%2=0) : Not (Nat.Prime (squareSuccessorUnpaired n)) := by
  rw [squareSuccessorUnpaired_even heven]
  exact not_prime_of_two_factors (by omega) (by omega)

/-- For odd index the extra odd candidate is two below the next square. -/
theorem squareSuccessorUnpaired_odd {n : Nat} (hn : n%2=1) :
    squareSuccessorUnpaired n+2=(n+2)*(n+2) := by
  unfold squareSuccessorUnpaired
  rw [hn]
  have hi : (n+2)*(n+2)=n*n+4*n+4 := by ring
  rw [hi]
  omega

/-- The complete signed incidence weight with all small-prime exclusions retained. -/
noncomputable def squareJointPointWeight (a b : Finset Nat) (m : Nat) : Int :=
  if forall p, Membership.mem a p -> Not (Dvd.dvd p m) then
    jointIncidenceWeight ((b.filter (fun q => Dvd.dvd q m)).card) else 0

/-- The actual packet is the sum of its zero-extended point weights. -/
theorem squareJointPacket_eq_point_sum (x : Nat) (a b : Finset Nat) :
    squareJointPacket x a b =
      (oddMultiplesInSquare x 1).sum (squareJointPointWeight a b) := by
  unfold squareJointPacket squareJointPointWeight
  rw [Finset.sum_filter]

/-- Exact joint successor comparison on one paired domain, without termwise estimates. -/
theorem squareJointPacket_successor_reflection (n : Nat) (a b : Finset Nat) :
    2*squareJointPacket (n+1) a b-squareJointPacket n a b =
      (oddMultiplesInSquare n 1).sum (fun m =>
        2*squareJointPointWeight a b (squareSuccessorReflection n m)-
          squareJointPointWeight a b m) +
        2*squareJointPointWeight a b (squareSuccessorUnpaired n) := by
  simp only [squareJointPacket_eq_point_sum, Finset.sum_sub_distrib, <- Finset.mul_sum]
  rw [sum_squareSuccessor_reflection]
  ring

/-- The complete native joint comparison retains the reflected sum and cutoff cost. -/
theorem successor_joint_floor_reflection_lower {n : Nat} (hn : 2<=n) :
    (oddMultiplesInSquare n 1).sum (fun m =>
      2*squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n)
          (squareSuccessorReflection n m)-
        squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n) m) +
      2*squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n)
        (squareSuccessorUnpaired n) - (if Nat.Prime (n+1) then 6 else 0) <=
      2*(3*squareIncidenceFloor (n+1) 0-3*squareIncidenceFloor (n+1) 1+
        2*squareIncidenceFloor (n+1) 2) -
        (3*squareIncidenceFloor n 0-3*squareIncidenceFloor n 1+2*squareIncidenceFloor n 2) := by
  rw [<- squareJointPacket_successor_reflection, <- squareJointPacket_actual hn]
  have h := successor_joint_floor_cutoff_lower hn
  split_ifs at * <;> omega

/-- The complete incidence polynomial is never less than minus one. -/
theorem jointIncidenceWeight_neg_one_le (v : Nat) : -1<=jointIncidenceWeight v := by
  induction v with
  | zero => norm_num [jointIncidenceWeight]
  | succ v ih =>
    rw [jointIncidenceWeight_succ]
    by_cases h0 : v=0
    next => subst v; norm_num [jointIncidenceWeight]
    next =>
      by_cases h1 : v=1
      next => subst v; norm_num [jointIncidenceWeight]
      next => omega

/-- Keeping or excluding a point preserves the universal lower weight bound. -/
theorem squareJointPointWeight_neg_one_le (a b : Finset Nat) (m : Nat) :
    -1<=squareJointPointWeight a b m := by
  unfold squareJointPointWeight
  split_ifs
  next => exact jointIncidenceWeight_neg_one_le _
  next => omega

/-- No old odd candidate is divisible by the odd successor index. -/
theorem odd_upper_index_not_dvd {n m : Nat}
    (hm : Membership.mem (oddMultiplesInSquare n 1) m) (hodd : (n+1)%2=1) :
    Not (Dvd.dvd (n+1) m) := by
  have h := mem_oddMultiplesInSquare_one_iff.mp hm
  intro hd
  choose k hk using hd
  have hkodd : k%2=1 := by rw [hk, Nat.mul_mod, hodd] at h; simpa using h.2.2
  have hklo : n<=k := by
    by_contra hc
    have hh := Nat.mul_le_mul_left (n+1) (show k+1<=n by omega)
    nlinarith
  have hkhi : k<=n := by
    by_contra hc
    have hh := Nat.mul_le_mul_left (n+1) (show n+1<=k by omega)
    nlinarith
  omega

/-- No reflected old odd candidate meets the newly admitted odd index. -/
theorem squareSuccessorReflection_not_dvd_upper {n m : Nat}
    (hm : Membership.mem (oddMultiplesInSquare n 1) m) (hodd : (n+1)%2=1) :
    Not (Dvd.dvd (n+1) (squareSuccessorReflection n m)) := by
  intro hd
  exact odd_upper_index_not_dvd hm hodd
    ((squareSuccessorReflection_dvd_iff hm (dvd_refl (n+1))).mp hd)

/-- Prime admission changes no actual reflected point weight. -/
theorem squareJointPointWeight_reflection_prime {n m : Nat} (hn : 2<=n)
    (hp : Nat.Prime (n+1)) (hm : Membership.mem (oddMultiplesInSquare n 1) m) :
    squareJointPointWeight (squareSmallOddPrimes (n+1)) (squareMediumOddPrimes (n+1))
      (squareSuccessorReflection n m) =
    squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n)
      (squareSuccessorReflection n m) := by
  have hodd := hp.eq_two_or_odd.resolve_left (show Not (n+1=2) by omega)
  have hnd := squareSuccessorReflection_not_dvd_upper hm hodd
  have hno : Not (exists r : Nat, Nat.Prime r /\ r%2=1 /\ r*r=n+1) := by
    intro h
    choose r hr using h
    apply not_prime_of_two_factors hr.1.two_le hr.1.two_le
    rw [hr.2.2]
    exact hp
  unfold squareJointPointWeight
  rw [squareSmallOddPrimes_succ_no_square hno, squareMediumOddPrimes_succ_prime hn hp]
  simp only [Finset.filter_insert, hnd, if_false]

/-- At a prime successor the exact endpoint is the only cutoff update. -/
theorem squareJointPacket_prime_reflection_exact {n : Nat} (hn : 2<=n)
    (hp : Nat.Prime (n+1)) :
    squareJointPacket (n+1) (squareSmallOddPrimes (n+1)) (squareMediumOddPrimes (n+1)) =
      (oddMultiplesInSquare n 1).sum (fun m =>
        squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n)
          (squareSuccessorReflection n m)) +
        squareJointPointWeight (squareSmallOddPrimes (n+1)) (squareMediumOddPrimes (n+1))
          (squareSuccessorUnpaired n) := by
  rw [squareJointPacket_eq_point_sum, sum_squareSuccessor_reflection]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  exact squareJointPointWeight_reflection_prime hn hp hm

/-- After exact cutoff cancellation the full reflected sum loses at most one. -/
theorem successor_joint_floor_reflected_sum_lower {n : Nat} (hn : 2<=n) :
    (oddMultiplesInSquare n 1).sum (fun m =>
      squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n)
        (squareSuccessorReflection n m))-1 <=
      3*squareIncidenceFloor (n+1) 0-3*squareIncidenceFloor (n+1) 1+
        2*squareIncidenceFloor (n+1) 2 := by
  by_cases hp : Nat.Prime (n+1)
  next =>
    rw [<- squareJointPacket_actual (show 2<=n+1 by omega),
      squareJointPacket_prime_reflection_exact hn hp]
    have h := squareJointPointWeight_neg_one_le (squareSmallOddPrimes (n+1))
      (squareMediumOddPrimes (n+1)) (squareSuccessorUnpaired n)
    omega
  next =>
    have h := successor_joint_floor_cutoff_lower hn
    rw [if_neg hp, sub_zero, squareJointPacket_eq_point_sum,
      sum_squareSuccessor_reflection] at h
    have he := squareJointPointWeight_neg_one_le (squareSmallOddPrimes n)
      (squareMediumOddPrimes n) (squareSuccessorUnpaired n)
    omega

/-- The complete native joint comparison loses at most two after endpoint cancellation. -/
theorem successor_joint_floor_reflection_minus_two {n : Nat} (hn : 2<=n) :
    (oddMultiplesInSquare n 1).sum (fun m =>
      2*squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n)
          (squareSuccessorReflection n m)-
        squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n) m)-2 <=
      2*(3*squareIncidenceFloor (n+1) 0-3*squareIncidenceFloor (n+1) 1+
        2*squareIncidenceFloor (n+1) 2) -
        (3*squareIncidenceFloor n 0-3*squareIncidenceFloor n 1+2*squareIncidenceFloor n 2) := by
  simp only [Finset.sum_sub_distrib, <- Finset.mul_sum]
  rw [<- squareJointPacket_eq_point_sum, squareJointPacket_actual hn]
  have h := successor_joint_floor_reflected_sum_lower hn
  omega

end Nat.PrimeSieve
