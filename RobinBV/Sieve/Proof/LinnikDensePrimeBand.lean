/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import PrimeNumberTheoremAnd.Consequences
import RobinBV.Mathlib.Analysis.Complex.LinnikPrimeBand

/-!
# Dense prime bands for the project Linnik VMVT recurrence

The prime number theorem supplies arbitrarily many primes in `(y, 2*y]`.
This module extracts an exact finite band of positive prime moduli and feeds
it immediately into the complete Linnik recurrence.  Consequently the
modulus ceiling is `2 * nthRoot k X`, replacing the exponentially larger
ceiling obtained by iterating Bertrand's postulate.
-/

open Filter

/-- The number of primes in `(y, 2*y]` eventually exceeds every fixed
natural number, in a subtraction-free form convenient for cardinalities. -/
theorem eventually_primeCounting_two_mul_sub_gt (M : Nat) :
    Filter.Eventually
      (fun y : Nat => M + Nat.primeCounting y < Nat.primeCounting (2 * y))
      atTop := by
  have hlim := (tendsto_by_squeeze 1 (by norm_num)).comp
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun y : Nat => (y : Real)) atTop atTop)
  have hlarge := hlim.eventually (eventually_gt_atTop (M : Real))
  filter_upwards [hlarge] with y hy
  norm_num at hy
  have hcast : (2 : Real) * (y : Real) = ((2 * y : Nat) : Real) := by
    norm_num
  rw [hcast] at hy
  simp only [Nat.floor_natCast] at hy
  have hsum : (M : Real) + Nat.primeCounting y < Nat.primeCounting (2 * y) := by
    linarith
  exact_mod_cast hsum

/-- For every fixed cardinality, sufficiently large dyadic intervals contain
an exact finite set of that many positive prime moduli. -/
theorem eventually_exists_linnikDensePrimeBand (M : Nat) :
    Filter.Eventually
      (fun y : Nat =>
        exists P : Finset {p : Nat // 0 < p},
          P.card = M /\
            (forall p, Membership.mem P p ->
              p.val.Prime /\ y < p.val /\ p.val <= 2 * y))
      atTop := by
  filter_upwards [eventually_primeCounting_two_mul_sub_gt M] with y hcount
  let s := (Nat.primesLE (2 * y)).filter (fun p => y < p)
  have hsmall : Nat.primesLE y <= Nat.primesLE (2 * y) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    rw [Nat.mem_primesLE]
    exact And.intro (by omega) hp.2
  have hsEq : s = Nat.primesLE (2 * y) \ Nat.primesLE y := by
    ext p
    simp only [s, Finset.mem_filter, Nat.mem_primesLE, Finset.mem_sdiff]
    constructor
    next =>
      intro hp
      apply And.intro (And.left hp)
      intro hpSmall
      exact (not_le_of_gt (And.right hp)) (And.left hpSmall)
    next =>
      intro hp
      apply And.intro (And.left hp)
      apply lt_of_not_ge
      intro hle
      exact (And.right hp) (And.intro hle (And.right (And.left hp)))
  have hsCard : s.card = Nat.primeCounting (2 * y) - Nat.primeCounting y := by
    rw [hsEq, Finset.card_sdiff, Finset.inter_eq_left.mpr hsmall]
    simp only [Nat.primesLE_card_eq_primeCounting]
  have hMCard : M <= s.card := by
    rw [hsCard]
    omega
  cases Finset.exists_subset_card_eq hMCard with
  | intro t ht =>
      let e : {q : Nat // Membership.mem t q} -> {p : Nat // 0 < p} := fun q =>
        Subtype.mk q.val (by
          have hqs : Membership.mem s q.val := ht.1 q.property
          have hqPrime : q.val.Prime := (Nat.mem_primesLE.mp
            (Finset.mem_filter.mp hqs).1).2
          exact hqPrime.pos)
      have heInj : Function.Injective e := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun p : {p : Nat // 0 < p} => p.val) hab
      let emb : Function.Embedding {q : Nat // Membership.mem t q}
          {p : Nat // 0 < p} := Function.Embedding.mk e heInj
      let P : Finset {p : Nat // 0 < p} := t.attach.map emb
      refine Exists.intro P (And.intro ?_ ?_)
      next =>
        simpa [P] using (show t.card = M by omega)
      next =>
        intro p hp
        change Membership.mem (t.attach.map emb) p at hp
        rw [Finset.mem_map] at hp
        choose q hqAttach hqEq using hp
        have hpEq : emb q = p := hqEq
        subst p
        have hqs : Membership.mem s q.val := ht.1 q.property
        have hqMem := Finset.mem_filter.mp hqs
        have hqPrime : q.val.Prime := (Nat.mem_primesLE.mp hqMem.1).2
        have hqUpper : q.val <= 2 * y := (Nat.mem_primesLE.mp hqMem.1).1
        exact And.intro hqPrime (And.intro hqMem.2 hqUpper)

namespace Finset

/-- The complete Linnik recurrence with a dense dyadic prime band.  The
statement has no free modulus, prime set, packet count, or Fourier parameter. -/
theorem eventually_vinogradovMeanValue_le_nthRoot_dense_recurrence
    (k r : Nat) (hk : 0 < k) (hr : 1 < r) (hm : 2 <= k * r) :
    Filter.Eventually
      (fun X : Nat =>
        vinogradovMeanValue k (k * r) X <=
          max
            (4 * ((k ^ 3 + 1) ^ 2 *
              ((2 * Nat.nthRoot k X) ^ (2 * (k * (r - 1))) *
                ((X ^ k * (k.factorial *
                    (2 * Nat.nthRoot k X) ^ (k * (k - 1) / 2))) *
                  vinogradovMeanValue k (k * (r - 1))
                    (1 + X / (Nat.nthRoot k X + 1))))))
            (4 ^ (k * r) * k ^ (4 * (k * r))))
      atTop := by
  have hband := eventually_exists_linnikDensePrimeBand (k ^ 3 + 1)
  rw [eventually_atTop] at hband
  choose y0 hy0 using hband
  rw [eventually_atTop]
  refine Exists.intro (max (k ^ k) (y0 ^ k)) ?_
  intro X hX
  have hkX : k ^ k <= X := le_trans (le_max_left _ _) hX
  have hyX : y0 ^ k <= X := le_trans (le_max_right _ _) hX
  have hkRoot : k <= Nat.nthRoot k X :=
    (Nat.le_nthRoot_iff hk.ne').mpr hkX
  have hyRoot : y0 <= Nat.nthRoot k X :=
    (Nat.le_nthRoot_iff hk.ne').mpr hyX
  have hPX := hy0 (Nat.nthRoot k X) hyRoot
  cases hPX with
  | intro P hP =>
      have hXRoot : X < (Nat.nthRoot k X + 1) ^ k :=
        Nat.lt_pow_nthRoot_add_one hk.ne' X
      have hgeom : X <= (Nat.nthRoot k X + 1) ^ (k + 1) := by
        exact le_trans (Nat.le_of_lt hXRoot)
          (Nat.pow_le_pow_right (by omega) (by omega))
      have hrec := vinogradovMeanValue_le_primeBand_uniform
        P k r X (Nat.nthRoot k X) (2 * Nat.nthRoot k X)
          (vinogradovMeanValue k (k * (r - 1))
            (1 + X / (Nat.nthRoot k X + 1)))
          hk hr hm
          (fun p hpP => (hP.2 p hpP).1)
          (fun p hpP => (hP.2 p hpP).2.1)
          (by omega) hgeom
          (fun p hpP => lt_of_le_of_lt hkRoot (hP.2 p hpP).2.1)
          (fun p hpP => lt_of_lt_of_le hXRoot
            (Nat.pow_le_pow_left
              (Nat.succ_le_of_lt (hP.2 p hpP).2.1) k))
          (fun p hpP => (hP.2 p hpP).2.2)
          (by
            intro p hpP
            apply vinogradovMeanValue_mono
            apply Nat.add_le_add_left
            exact Nat.div_le_div_left
              (Nat.succ_le_of_lt (hP.2 p hpP).2.1) (by omega))
      rw [hP.1] at hrec
      exact hrec

end Finset
