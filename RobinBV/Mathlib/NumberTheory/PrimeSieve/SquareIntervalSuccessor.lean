/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalIncidenceFloors

/-!
# Joint successor cutoff comparisons

The full combination 3 F0 - 3 F1 + 2 F2 is retained throughout. Moving an odd
prime into the small sieve cannot lower this combination; admitting the new
upper prime costs at most three. The final theorem bounds every cutoff update
against the complete packet with the predecessor's prime sets held fixed.
It does not assert positivity or bound the change caused by moving the interval.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- There is exactly one odd multiple of an odd index in its open square interval. -/
theorem card_oddMultiplesInSquare_diagonal {n : Nat} (hn : n % 2 = 1) :
    (oddMultiplesInSquare n n).card = 1 := by
  have hn0 : 0 < n := by omega
  have h := card_oddMultiplesInSquare n hn
  have hlo : n * n / n = n := by simp [hn0.ne']
  have hhi : (n * n + 2 * n) / n = n + 2 := by
    rw [show n * n + 2 * n = (n + 2) * n by ring]
    simp [hn0.ne']
  rw [hlo, hhi] at h
  omega

/-- Admitting the upper odd index costs at most three in the full signed combination. -/
theorem sum_jointIncidenceWeight_insert_upper_index {n : Nat} (hn : n % 2 = 1)
    (s b : Finset Nat) (hs : forall m, Membership.mem s m ->
      Membership.mem (oddMultiplesInSquare n 1) m)
    (hb : Not (Membership.mem b n)) :
    s.sum (fun m => jointIncidenceWeight ((b.filter (fun q => Dvd.dvd q m)).card)) - 3 <=
      s.sum (fun m => jointIncidenceWeight (((insert n b).filter (fun q => Dvd.dvd q m)).card)) := by
  have hsub : forall m, Membership.mem (s.filter (fun m => Dvd.dvd n m)) m ->
      Membership.mem (oddMultiplesInSquare n n) m := by
    intro m hm
    rw [<- oddMultiplesInSquare_one_filter]
    exact Finset.mem_filter.mpr (And.intro (hs m (Finset.mem_filter.mp hm).1)
      (Finset.mem_filter.mp hm).2)
  have hcard := Finset.card_le_card hsub
  rw [card_oddMultiplesInSquare_diagonal hn] at hcard
  have hcast : ((s.filter (fun m => Dvd.dvd n m)).card : Int) <= 1 := by
    exact_mod_cast hcard
  have h := sum_jointIncidenceWeight_insert_lower s b n hb
  omega

/-- The combined divisor weight is exactly the complete three-incidence floor expression. -/
theorem sum_jointIncidenceWeight_eq_signed_floors {n : Nat} (hn : 2 <= n) :
    (squareRoughSurvivors n).sum (fun m => jointIncidenceWeight
      (((squareMediumOddPrimes n).filter (fun q => Dvd.dvd q m)).card)) =
      3 * squareIncidenceFloor n 0 - 3 * squareIncidenceFloor n 1 +
        2 * squareIncidenceFloor n 2 := by
  have heq : (squareRoughSurvivors n).sum (fun m => jointIncidenceWeight
      (((squareMediumOddPrimes n).filter (fun q => Dvd.dvd q m)).card)) =
      (squareRoughSurvivors n).sum (fun m => jointIncidenceWeight (mediumPrimeCount n m)) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [mediumPrimeCount, mediumPrimeDivisors_eq_medium_filter hm]
  rw [heq, squareIncidenceFloor_zero hn, squareIncidenceFloor_one hn,
    squareIncidenceFloor_two hn]
  simp only [jointIncidenceWeight, firstIncidence, secondIncidence,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- A prime successor admits precisely one new medium prime and promotes none. -/
theorem squareMediumOddPrimes_succ_prime {n : Nat} (hn : 2 <= n)
    (hp : Nat.Prime (n + 1)) :
    squareMediumOddPrimes (n + 1) = insert (n + 1) (squareMediumOddPrimes n) := by
  ext q
  simp only [squareMediumOddPrimes, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
  constructor
  next =>
    intro h
    by_cases heq : q = n + 1
    next => exact Or.inl heq
    next => exact Or.inr (And.intro (by omega)
      (And.intro h.2.1 (And.intro h.2.2.1 (by omega))))
  next =>
    intro h
    rcases h with heq | h
    next =>
      subst q
      have hodd := hp.eq_two_or_odd.resolve_left (show Not (n + 1 = 2) by omega)
      exact And.intro (by omega) (And.intro hp (And.intro hodd (by nlinarith)))
    next =>
      have hsq : Not (q * q = n + 1) := by
        intro heq
        apply not_prime_of_two_factors h.2.1.two_le h.2.1.two_le
        rw [heq]
        exact hp
      exact And.intro (by omega) (And.intro h.2.1 (And.intro h.2.2.1 (by omega)))

/-- The complete joint incidence sum with independently specified small and medium prime sets. -/
noncomputable def squareJointPacket (x : Nat) (a b : Finset Nat) : Int :=
  ((oddMultiplesInSquare x 1).filter (fun m =>
    forall p, Membership.mem a p -> Not (Dvd.dvd p m))).sum (fun m =>
      jointIncidenceWeight ((b.filter (fun q => Dvd.dvd q m)).card))

/-- At the actual cutoffs the joint packet equals three times F0 minus three times F1 plus twice F2. -/
theorem squareJointPacket_actual {n : Nat} (hn : 2 <= n) :
    squareJointPacket n (squareSmallOddPrimes n) (squareMediumOddPrimes n) =
      3 * squareIncidenceFloor n 0 - 3 * squareIncidenceFloor n 1 +
        2 * squareIncidenceFloor n 2 := by
  unfold squareJointPacket
  rw [<- rough_survivors_eq_small_sieve hn]
  exact sum_jointIncidenceWeight_eq_signed_floors hn

/-- The small-prime set is unchanged unless the successor is an odd prime square. -/
theorem squareSmallOddPrimes_succ_no_square {n : Nat}
    (hno : Not (exists r : Nat, Nat.Prime r /\ r % 2 = 1 /\ r * r = n + 1)) :
    squareSmallOddPrimes (n + 1) = squareSmallOddPrimes n := by
  ext q
  simp only [squareSmallOddPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  next =>
    intro h
    have hcut : q * q <= n := by
      by_contra hc
      exact hno (Exists.intro q (And.intro h.2.1 (And.intro h.2.2.1 (by omega))))
    exact And.intro (by have hq := h.2.1.two_le; nlinarith)
      (And.intro h.2.1 (And.intro h.2.2.1 hcut))
  next =>
    intro h
    exact And.intro (by omega) (And.intro h.2.1 (And.intro h.2.2.1 (by omega)))

/-- Without a prime admission or odd-prime-square promotion the medium set is unchanged. -/
theorem squareMediumOddPrimes_succ_no_event {n : Nat}
    (hp : Not (Nat.Prime (n + 1)))
    (hno : Not (exists r : Nat, Nat.Prime r /\ r % 2 = 1 /\ r * r = n + 1)) :
    squareMediumOddPrimes (n + 1) = squareMediumOddPrimes n := by
  ext q
  simp only [squareMediumOddPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  next =>
    intro h
    have hne : Not (q = n + 1) := by intro heq; rw [heq] at h; exact hp h.2.1
    exact And.intro (by omega) (And.intro h.2.1 (And.intro h.2.2.1 (by omega)))
  next =>
    intro h
    have hcut : n + 1 < q * q := by
      by_contra hc
      exact hno (Exists.intro q (And.intro h.2.1 (And.intro h.2.2.1 (by omega))))
    exact And.intro (by omega) (And.intro h.2.1 (And.intro h.2.2.1 hcut))

/-- An odd-prime-square successor adds exactly that prime to the small-prime sieve. -/
theorem squareSmallOddPrimes_succ_square {n r : Nat} (hp : Nat.Prime r)
    (hodd : r % 2 = 1) (heq : r * r = n + 1) :
    squareSmallOddPrimes (n + 1) = insert r (squareSmallOddPrimes n) := by
  ext q
  simp only [squareSmallOddPrimes, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
  constructor
  next =>
    intro h
    by_cases hcut : q * q <= n
    next => exact Or.inr (And.intro (by have hq := h.2.1.two_le; nlinarith)
      (And.intro h.2.1 (And.intro h.2.2.1 hcut)))
    next => apply Or.inl; nlinarith [h.2.2.2]
  next =>
    intro h
    rcases h with h | h
    next =>
      subst q
      exact And.intro (by have hr := hp.two_le; nlinarith)
        (And.intro hp (And.intro hodd (by omega)))
    next => exact And.intro (by omega) (And.intro h.2.1 (And.intro h.2.2.1 (by omega)))

/-- A prime-square successor removes exactly its square root from the medium set. -/
theorem squareMediumOddPrimes_succ_square {n r : Nat} (hp : Nat.Prime r)
    (heq : r * r = n + 1) :
    squareMediumOddPrimes (n + 1) = (squareMediumOddPrimes n).erase r := by
  have hnp : Not (Nat.Prime (n + 1)) := by
    rw [<- heq]
    exact not_prime_of_two_factors hp.two_le hp.two_le
  ext q
  simp only [squareMediumOddPrimes, Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
  constructor
  next =>
    intro h
    have hqr : Not (q = r) := by intro hq; subst q; omega
    have hqn : Not (q = n + 1) := by intro hq; rw [hq] at h; exact hnp h.2.1
    exact And.intro hqr (And.intro (by omega) (And.intro h.2.1
      (And.intro h.2.2.1 (by omega))))
  next =>
    intro h
    have hcut : n + 1 < q * q := by
      by_contra hc
      have hqr : q = r := by nlinarith [h.2.2.2.2]
      exact h.1 hqr
    exact And.intro (by omega) (And.intro h.2.2.1 (And.intro h.2.2.2.1 hcut))

/-- Promoting the boundary odd prime cannot lower the complete signed packet. -/
theorem squareJointPacket_promote_prime {n r : Nat} (hp : Nat.Prime r)
    (hodd : r % 2 = 1) (heq : r * r = n + 1) :
    squareJointPacket (n + 1) (squareSmallOddPrimes n) (squareMediumOddPrimes n) <=
      squareJointPacket (n + 1) (squareSmallOddPrimes (n + 1))
        (squareMediumOddPrimes (n + 1)) := by
  have hr3 : 3 <= r := by have h := hp.two_le; omega
  let s := (oddMultiplesInSquare (n + 1) 1).filter (fun m =>
    forall p, Membership.mem (squareSmallOddPrimes n) p -> Not (Dvd.dvd p m))
  have hs : forall m, Membership.mem s m ->
      0 < m /\ m < (r * r + 1) * (r * r + 1) := by
    intro m hm
    have hinterval := (Finset.mem_filter.mp hm).1
    have hlo := (Finset.mem_filter.mp hinterval).2
    have hhi := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hinterval).1).1
    exact And.intro (by nlinarith) (by nlinarith)
  have hprime : forall p, Membership.mem (squareMediumOddPrimes n) p -> Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1
  have hlow : forall p, Membership.mem (squareMediumOddPrimes n) p -> r <= p := by
    intro p hp
    have hcut := (Finset.mem_filter.mp hp).2.2.2
    nlinarith
  have hrb : Membership.mem (squareMediumOddPrimes n) r := by
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by nlinarith))
      (And.intro hp (And.intro hodd (by omega))))
  have h := sum_jointIncidenceWeight_erase_sieve_square hr3 s
    (squareMediumOddPrimes n) hs hprime hlow hrb
  have hset : (oddMultiplesInSquare (n + 1) 1).filter (fun m =>
      forall p, Membership.mem (insert r (squareSmallOddPrimes n)) p -> Not (Dvd.dvd p m)) =
      s.filter (fun m => Not (Dvd.dvd r m)) := by
    ext m
    simp only [s, Finset.mem_filter, Finset.forall_mem_insert]
    constructor
    next => intro h; exact And.intro (And.intro h.1 h.2.2) h.2.1
    next => intro h; exact And.intro h.1.1 (And.intro h.2 h.1.2)
  unfold squareJointPacket
  rw [squareSmallOddPrimes_succ_square hp hodd heq,
    squareMediumOddPrimes_succ_square hp heq, hset]
  exact h

/-- All successor cutoff changes together cost at most three, and only at a prime successor. -/
theorem successor_joint_floor_cutoff_lower {n : Nat} (hn : 2 <= n) :
    squareJointPacket (n + 1) (squareSmallOddPrimes n) (squareMediumOddPrimes n) -
        (if Nat.Prime (n + 1) then (3 : Int) else 0) <=
      3 * squareIncidenceFloor (n + 1) 0 - 3 * squareIncidenceFloor (n + 1) 1 +
        2 * squareIncidenceFloor (n + 1) 2 := by
  have hn1 : 2 <= n + 1 := by omega
  rw [<- squareJointPacket_actual hn1]
  by_cases hp : Nat.Prime (n + 1)
  next =>
    have hno : Not (exists r : Nat, Nat.Prime r /\ r % 2 = 1 /\ r * r = n + 1) := by
      intro h
      choose r hr using h
      apply not_prime_of_two_factors hr.1.two_le hr.1.two_le
      rw [hr.2.2]
      exact hp
    rw [if_pos hp, squareSmallOddPrimes_succ_no_square hno,
      squareMediumOddPrimes_succ_prime hn hp]
    unfold squareJointPacket
    apply sum_jointIncidenceWeight_insert_upper_index
      (hp.eq_two_or_odd.resolve_left (show Not (n + 1 = 2) by omega))
    next => intro m hm; exact (Finset.mem_filter.mp hm).1
    next => intro h; have hq := Finset.mem_range.mp (Finset.mem_filter.mp h).1; omega
  next =>
    rw [if_neg hp, sub_zero]
    by_cases he : exists r : Nat, Nat.Prime r /\ r % 2 = 1 /\ r * r = n + 1
    next =>
      choose r hr using he
      exact squareJointPacket_promote_prime hr.1 hr.2.1 hr.2.2
    next => rw [squareSmallOddPrimes_succ_no_square he,
      squareMediumOddPrimes_succ_no_event hp he]

end Nat.PrimeSieve
