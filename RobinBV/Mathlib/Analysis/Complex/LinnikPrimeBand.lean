/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Nat.Dist
import Mathlib.NumberTheory.Bertrand
import RobinBV.Mathlib.Analysis.Complex.LinnikDistinctCover
import RobinBV.Mathlib.NumberTheory.PrimeSieve.InclusionExclusion

/-!
# Prime-band separation for Linnik's distinct branch

This module supplies the arithmetic part of the prime-band cover.  A finite
set of distinct primes above a cutoff has a rapidly growing product.  If all
of those primes divide one nonzero difference, the product-divisibility bound
therefore limits the number of such primes.  This is the per-pair estimate
used to construct a modulus that separates every coordinate of a distinct
prefix tuple.
-/

set_option autoImplicit false

namespace Finset

/-- Equality of Linnik residue indices forces the modulus to divide the
ordinary distance between the represented interval values. -/
theorem dvd_dist_of_linnikResidueIndex_eq
    (p X : Nat) (hp : 0 < p) (x y : Fin X)
    (hxy : linnikResidueIndex p X hp x =
      linnikResidueIndex p X hp y) :
    Dvd.dvd p (Nat.dist x.val y.val) := by
  have hmod : Nat.ModEq p (x.val + 1) (y.val + 1) :=
    congrArg Fin.val hxy
  cases le_total (x.val + 1) (y.val + 1) with
  | inl hle =>
      have hdvd := (Nat.modEq_iff_dvd' hle).mp hmod
      rw [<- Nat.dist_eq_sub_of_le hle, Nat.dist_add_add_right] at hdvd
      exact hdvd
  | inr hle =>
      have hdvd := (Nat.modEq_iff_dvd' hle).mp hmod.symm
      rw [<- Nat.dist_eq_sub_of_le hle, Nat.dist_add_add_right] at hdvd
      simpa [Nat.dist_comm] using hdvd

/-- At most `K` primes larger than `y` can divide a positive integer smaller
than `(y+1)^(K+1)`. -/
theorem card_positive_primes_dvd_le_of_lt_pow
    (Q : Finset {p : Nat // 0 < p}) (y K d : Nat)
    (hprime : forall q, Membership.mem Q q -> q.val.Prime)
    (hy : forall q, Membership.mem Q q -> y < q.val)
    (hdiv : forall q, Membership.mem Q q -> Dvd.dvd q.val d)
    (hd : 0 < d) (hdlt : d < (y + 1) ^ (K + 1)) :
    Q.card <= K := by
  classical
  let QN : Finset Nat := Q.image Subtype.val
  have hprimeN : forall q, Membership.mem QN q -> q.Prime := by
    intro q hq
    cases Finset.mem_image.mp hq with
    | intro a ha =>
        cases ha with
        | intro haQ haeq =>
            subst q
            exact hprime a haQ
  have hdivN : forall q, Membership.mem QN q -> Dvd.dvd q d := by
    intro q hq
    cases Finset.mem_image.mp hq with
    | intro a ha =>
        cases ha with
        | intro haQ haeq =>
            subst q
            exact hdiv a haQ
  have hprodDvd : Dvd.dvd (QN.prod fun q => q) d :=
    (Nat.PrimeSieve.prod_primes_dvd_iff hprimeN d).mpr hdivN
  have hprodEq : (QN.prod fun q => q) = Q.prod (fun q => q.val) := by
    unfold QN
    rw [Finset.prod_image]
    exact Set.injOn_of_injective Subtype.val_injective
  have hlower : (y + 1) ^ Q.card <= Q.prod (fun q => q.val) := by
    calc
      (y + 1) ^ Q.card = Q.prod (fun _q => y + 1) := by simp
      _ <= Q.prod (fun q => q.val) := by
        apply Finset.prod_le_prod
        next =>
          intro q hq
          omega
        next =>
          intro q hq
          exact Nat.succ_le_of_lt (hy q hq)
  have hprodLe : Q.prod (fun q => q.val) <= d := by
    rw [<- hprodEq]
    exact Nat.le_of_dvd hd hprodDvd
  by_contra hcard
  have hK : K + 1 <= Q.card := by omega
  have hpow : (y + 1) ^ (K + 1) <= (y + 1) ^ Q.card :=
    Nat.pow_le_pow_right (by omega) hK
  omega

/-- Iterating Bertrand's postulate produces exactly `M` distinct primes above
`y`, all bounded by the fixed dyadic multiple `2^M*y`. -/
theorem exists_linnikPrimeBand
    (y M : Nat) (hy : 0 < y) :
    exists P : Finset {p : Nat // 0 < p},
      P.card = M /\
        (forall p, Membership.mem P p ->
          p.val.Prime /\ y < p.val /\ p.val <= 2 ^ M * y) := by
  induction M with
  | zero =>
      refine Exists.intro
        (EmptyCollection.emptyCollection : Finset {p : Nat // 0 < p}) ?_
      constructor
      next => rfl
      next =>
        intro p hp
        simp at hp
  | succ M ih =>
      cases ih with
      | intro P hP =>
          let N := 2 ^ M * y
          have hN : 0 < N := by
            unfold N
            positivity
          cases Nat.bertrand N hN.ne' with
          | intro q hq =>
              let qpos : {p : Nat // 0 < p} := Subtype.mk q hq.1.pos
              have hqNotMem : Not (Membership.mem P qpos) := by
                intro hqP
                have hqUpper := (hP.2 qpos hqP).2.2
                exact (not_lt_of_ge hqUpper) hq.2.1
              refine Exists.intro (Insert.insert qpos P) ?_
              constructor
              next =>
                simp [hqNotMem, hP.1]
              next =>
                intro p hp
                have hpCases := Finset.mem_insert.mp hp
                cases hpCases with
                | inl hpq =>
                    subst p
                    refine And.intro hq.1 (And.intro ?_ ?_)
                    next =>
                      have hyN : y <= N := by
                        unfold N
                        exact Nat.le_mul_of_pos_left y (pow_pos (by decide) M)
                      exact lt_of_le_of_lt hyN hq.2.1
                    next =>
                      unfold N at hq
                      simpa [Nat.pow_succ, mul_assoc, mul_left_comm,
                        mul_comm] using hq.2.2
                | inr hpP =>
                    have hpOld := hP.2 p hpP
                    refine And.intro hpOld.1 (And.intro hpOld.2.1 ?_)
                    calc
                      p.val <= 2 ^ M * y := hpOld.2.2
                      _ <= 2 ^ (M + 1) * y := by
                        apply Nat.mul_le_mul_right y
                        exact Nat.pow_le_pow_right (by decide) (by omega)

/-- For `X >= k^k`, a Bertrand band above the integer `k`th root of `X`
has all of the arithmetic properties required by the distinct-branch
consumer. -/
theorem exists_linnikPrimeBand_for_nthRoot
    (k X : Nat) (hk : 0 < k) (hX : 0 < X) (hkX : k ^ k <= X) :
    exists P : Finset {p : Nat // 0 < p},
      P.card = k ^ 3 + 1 /\
        (forall p, Membership.mem P p ->
          p.val.Prime /\
            Nat.nthRoot k X < p.val /\
            p.val <= 2 ^ (k ^ 3 + 1) * Nat.nthRoot k X /\
            k < p.val /\ X < p.val ^ k) := by
  have hy : 0 < Nat.nthRoot k X := by
    have hone : 1 <= Nat.nthRoot k X :=
      (Nat.le_nthRoot_iff hk.ne').mpr (by
        simpa using (show 1 <= X by omega))
    omega
  cases exists_linnikPrimeBand (Nat.nthRoot k X) (k ^ 3 + 1) hy with
  | intro P hP =>
      refine Exists.intro P (And.intro hP.1 ?_)
      intro p hpP
      have hp := hP.2 p hpP
      have hkRoot : k <= Nat.nthRoot k X :=
        (Nat.le_nthRoot_iff hk.ne').mpr hkX
      have hXRoot : X < (Nat.nthRoot k X + 1) ^ k :=
        Nat.lt_pow_nthRoot_add_one hk.ne' X
      refine And.intro hp.1 (And.intro hp.2.1
        (And.intro hp.2.2 (And.intro ?_ ?_)))
      next => exact lt_of_le_of_lt hkRoot hp.2.1
      next =>
        exact lt_of_lt_of_le hXRoot
          (Nat.pow_le_pow_left (Nat.succ_le_of_lt hp.2.1) k)

/-- Moduli in `P` that fail to separate one prefix tuple. -/
noncomputable def linnikBadModuli
    (P : Finset {p : Nat // 0 < p}) (k r X : Nat) (hr : 0 < r)
    (v : Fin (k * r) -> Fin X) : Finset {p : Nat // 0 < p} :=
  P.filter (fun p => Not (Function.Injective (fun i : Fin k =>
    linnikResidueIndex p.val X p.property
      (linnikMomentPrefix k r X hr v i))))

/-- Moduli in `P` dividing the value difference at one ordered pair of
prefix coordinates. -/
noncomputable def linnikPairDivisorModuli
    (P : Finset {p : Nat // 0 < p}) (k r X : Nat) (hr : 0 < r)
    (v : Fin (k * r) -> Fin X) (ij : Prod (Fin k) (Fin k)) :
    Finset {p : Nat // 0 < p} :=
  P.filter (fun p => Dvd.dvd p.val (Nat.dist
    (linnikMomentPrefix k r X hr v ij.fst).val
    (linnikMomentPrefix k r X hr v ij.snd).val))

/-- Every bad modulus divides the coordinate difference of an ordered pair
of distinct prefix indices. -/
theorem linnikBadModuli_subset_pairDivisor_biUnion
    (P : Finset {p : Nat // 0 < p}) (k r X : Nat) (hr : 0 < r)
    (v : Fin (k * r) -> Fin X) :
    linnikBadModuli P k r X hr v <=
      (linnikCollisionIndexPairs k).biUnion
        (linnikPairDivisorModuli P k r X hr v) := by
  classical
  intro p hpbad
  have hpParts := Finset.mem_filter.mp hpbad
  have hex := Function.not_injective_iff.mp hpParts.2
  cases hex with
  | intro i hi =>
      cases hi with
      | intro j hij =>
          apply Finset.mem_biUnion.mpr
          refine Exists.intro (i, j) ?_
          refine And.intro ?_ ?_
          next =>
            apply Finset.mem_filter.mpr
            refine And.intro (Finset.mem_product.mpr
              (And.intro (Finset.mem_univ i) (Finset.mem_univ j))) ?_
            exact hij.2
          next =>
            apply Finset.mem_filter.mpr
            refine And.intro hpParts.1 ?_
            exact dvd_dist_of_linnikResidueIndex_eq
              p.val X p.property
              (linnikMomentPrefix k r X hr v i)
              (linnikMomentPrefix k r X hr v j) hij.1

/-- For a prefix with distinct integer coordinates, at most `k` primes above
`y` divide the difference belonging to one distinct coordinate pair, provided
the interval length is at most `(y+1)^(k+1)`. -/
theorem card_linnikPairDivisorModuli_le
    (P : Finset {p : Nat // 0 < p}) (k r X y : Nat) (hr : 0 < r)
    (hprime : forall p, Membership.mem P p -> p.val.Prime)
    (hy : forall p, Membership.mem P p -> y < p.val)
    (hX : X <= (y + 1) ^ (k + 1))
    (v : Fin (k * r) -> Fin X)
    (hinj : Function.Injective (linnikMomentPrefix k r X hr v))
    (ij : Prod (Fin k) (Fin k))
    (hij : Membership.mem (linnikCollisionIndexPairs k) ij) :
    (linnikPairDivisorModuli P k r X hr v ij).card <= k := by
  classical
  let a := linnikMomentPrefix k r X hr v ij.fst
  let b := linnikMomentPrefix k r X hr v ij.snd
  let d := Nat.dist a.val b.val
  have hijne : Not (ij.fst = ij.snd) := (Finset.mem_filter.mp hij).2
  have hab : Not (a = b) := by
    intro heq
    exact hijne (hinj heq)
  have habVal : Not (a.val = b.val) := by
    intro heq
    exact hab (Fin.ext heq)
  have hd : 0 < d := Nat.dist_pos_of_ne habVal
  have hdX : d < X := by
    unfold d
    cases le_total a.val b.val with
    | inl hle =>
        rw [Nat.dist_eq_sub_of_le hle]
        exact lt_of_le_of_lt (Nat.sub_le _ _) b.isLt
    | inr hle =>
        rw [Nat.dist_eq_sub_of_le_right hle]
        exact lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
  apply card_positive_primes_dvd_le_of_lt_pow
    (linnikPairDivisorModuli P k r X hr v ij) y k d
  next =>
    intro p hp
    exact hprime p (Finset.mem_filter.mp hp).1
  next =>
    intro p hp
    exact hy p (Finset.mem_filter.mp hp).1
  next =>
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  next => exact hd
  next => exact lt_of_lt_of_le hdX hX

/-- The total number of bad moduli is at most `k^3`: there are at most
`k^2` ordered distinct coordinate pairs and at most `k` bad primes per pair. -/
theorem card_linnikBadModuli_le_cube
    (P : Finset {p : Nat // 0 < p}) (k r X y : Nat) (hr : 0 < r)
    (hprime : forall p, Membership.mem P p -> p.val.Prime)
    (hy : forall p, Membership.mem P p -> y < p.val)
    (hX : X <= (y + 1) ^ (k + 1))
    (v : Fin (k * r) -> Fin X)
    (hinj : Function.Injective (linnikMomentPrefix k r X hr v)) :
    (linnikBadModuli P k r X hr v).card <= k ^ 3 := by
  classical
  calc
    (linnikBadModuli P k r X hr v).card <=
        ((linnikCollisionIndexPairs k).biUnion
          (linnikPairDivisorModuli P k r X hr v)).card :=
      Finset.card_le_card
        (linnikBadModuli_subset_pairDivisor_biUnion P k r X hr v)
    _ <= (linnikCollisionIndexPairs k).sum (fun ij =>
        (linnikPairDivisorModuli P k r X hr v ij).card) :=
      Finset.card_biUnion_le
    _ <= (linnikCollisionIndexPairs k).sum (fun _ij => k) := by
      apply Finset.sum_le_sum
      intro ij hij
      exact card_linnikPairDivisorModuli_le
        P k r X y hr hprime hy hX v hinj ij hij
    _ = (linnikCollisionIndexPairs k).card * k := by simp
    _ <= k ^ 2 * k :=
      Nat.mul_le_mul_right k (card_linnikCollisionIndexPairs_le_sq k)
    _ = k ^ 3 := by ring

/-- A prime band of more than `k^3` primes above `y` separates every
integer-distinct prefix and therefore supplies the complete distinct-branch
square-sum estimate. -/
theorem linnikDistinctSquareSum_le_primeBand_equalPairs
    (P : Finset {p : Nat // 0 < p}) (k r X y : Nat) (hr : 0 < r)
    (hprime : forall p, Membership.mem P p -> p.val.Prime)
    (hy : forall p, Membership.mem P p -> y < p.val)
    (hcard : k ^ 3 < P.card)
    (hX : X <= (y + 1) ^ (k + 1)) :
    linnikDistinctSquareSum k r X hr <=
      P.card * P.sum (fun p =>
        (linnikModDistinctEqualPairs p.val k r X p.property hr).card) := by
  apply
    linnikDistinctSquareSum_le_card_mul_sum_equalPairs_of_bad_card_lt
      P k r X hr
  intro h hh v hv
  change (linnikBadModuli P k r X hr v).card < P.card
  exact lt_of_le_of_lt
    (card_linnikBadModuli_le_cube P k r X y hr hprime hy hX v
      (Finset.mem_filter.mp hv).2)
    hcard

/-- The equal-pair cardinality for one prime modulus satisfies the explicit
lower-level Vinogradov mean-value estimate. -/
theorem card_linnikModDistinctEqualPairs_le_vinogradovMeanValue_explicit
    (p k r X : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (hr : 1 < r) (hx : X < p ^ k) :
    (linnikModDistinctEqualPairs p k r X hp.pos
      (lt_trans (by omega) hr)).card <=
      p ^ (2 * (k * (r - 1))) *
        ((X ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) *
          vinogradovMeanValue k (k * (r - 1)) (1 + X / p)) := by
  cases exists_residue_linnikModDistinctPairCount_le_vinogradovMeanValue
      p k r X hp hk hkp hr hx with
  | intro a ha =>
      rw [linnikModDistinctPacketPairCount_eq_card_equalPairs
        p k r X hp.pos (lt_trans (by omega) hr)] at ha
      exact_mod_cast ha

/-- Complete prime-band consumer: the distinct branch is bounded entirely by
explicit arithmetic factors and lower-level Vinogradov mean values. -/
theorem linnikDistinctSquareSum_le_primeBand_vinogradovMeanValue
    (P : Finset {p : Nat // 0 < p}) (k r X y : Nat)
    (hk : 0 < k) (hr : 1 < r)
    (hprime : forall p, Membership.mem P p -> p.val.Prime)
    (hy : forall p, Membership.mem P p -> y < p.val)
    (hcard : k ^ 3 < P.card)
    (hX : X <= (y + 1) ^ (k + 1))
    (hkp : forall p, Membership.mem P p -> k < p.val)
    (hx : forall p, Membership.mem P p -> X < p.val ^ k) :
    linnikDistinctSquareSum k r X (lt_trans (by omega) hr) <=
      P.card * P.sum (fun p =>
        p.val ^ (2 * (k * (r - 1))) *
          ((X ^ k *
              (k.factorial * p.val ^ (k * (k - 1) / 2))) *
            vinogradovMeanValue k (k * (r - 1)) (1 + X / p.val))) := by
  calc
    linnikDistinctSquareSum k r X (lt_trans (by omega) hr) <=
        P.card * P.sum (fun p =>
          (linnikModDistinctEqualPairs p.val k r X p.property
            (lt_trans (by omega) hr)).card) :=
      linnikDistinctSquareSum_le_primeBand_equalPairs
        P k r X y (lt_trans (by omega) hr) hprime hy hcard hX
    _ <= P.card * P.sum (fun p =>
        p.val ^ (2 * (k * (r - 1))) *
          ((X ^ k *
              (k.factorial * p.val ^ (k * (k - 1) / 2))) *
            vinogradovMeanValue k (k * (r - 1)) (1 + X / p.val))) := by
      apply Nat.mul_le_mul_left
      apply Finset.sum_le_sum
      intro p hpP
      exact card_linnikModDistinctEqualPairs_le_vinogradovMeanValue_explicit
        p.val k r X (hprime p hpP) hk (hkp p hpP) hr (hx p hpP)

/-- Uniformizing the finite prime sum replaces every modulus and lower-level
mean value by common upper bounds. -/
theorem linnikDistinctSquareSum_le_primeBand_uniform
    (P : Finset {p : Nat // 0 < p}) (k r X y U M : Nat)
    (hk : 0 < k) (hr : 1 < r)
    (hprime : forall p, Membership.mem P p -> p.val.Prime)
    (hy : forall p, Membership.mem P p -> y < p.val)
    (hcard : k ^ 3 < P.card)
    (hX : X <= (y + 1) ^ (k + 1))
    (hkp : forall p, Membership.mem P p -> k < p.val)
    (hx : forall p, Membership.mem P p -> X < p.val ^ k)
    (hupper : forall p, Membership.mem P p -> p.val <= U)
    (hmean : forall p, Membership.mem P p ->
      vinogradovMeanValue k (k * (r - 1)) (1 + X / p.val) <= M) :
    linnikDistinctSquareSum k r X (lt_trans (by omega) hr) <=
      P.card ^ 2 *
        (U ^ (2 * (k * (r - 1))) *
          ((X ^ k * (k.factorial * U ^ (k * (k - 1) / 2))) * M)) := by
  calc
    linnikDistinctSquareSum k r X (lt_trans (by omega) hr) <=
        P.card * P.sum (fun p =>
          p.val ^ (2 * (k * (r - 1))) *
            ((X ^ k *
                (k.factorial * p.val ^ (k * (k - 1) / 2))) *
              vinogradovMeanValue k (k * (r - 1))
                (1 + X / p.val))) :=
      linnikDistinctSquareSum_le_primeBand_vinogradovMeanValue
        P k r X y hk hr hprime hy hcard hX hkp hx
    _ <= P.card * P.sum (fun _p =>
        U ^ (2 * (k * (r - 1))) *
          ((X ^ k * (k.factorial * U ^ (k * (k - 1) / 2))) * M)) := by
      apply Nat.mul_le_mul_left
      apply Finset.sum_le_sum
      intro p hpP
      gcongr
      next => exact hupper p hpP
      next => exact hupper p hpP
      next => exact hmean p hpP
    _ = P.card ^ 2 *
        (U ^ (2 * (k * (r - 1))) *
          ((X ^ k * (k.factorial * U ^ (k * (k - 1) / 2))) * M)) := by
      simp [Nat.pow_two, mul_assoc]

/-- The uniform prime-band estimate is consumed immediately by the complete
collision-versus-distinct recurrence for the Vinogradov mean value. -/
theorem vinogradovMeanValue_le_primeBand_uniform
    (P : Finset {p : Nat // 0 < p}) (k r X y U M : Nat)
    (hk : 0 < k) (hr : 1 < r) (hm : 2 <= k * r)
    (hprime : forall p, Membership.mem P p -> p.val.Prime)
    (hy : forall p, Membership.mem P p -> y < p.val)
    (hcard : k ^ 3 < P.card)
    (hX : X <= (y + 1) ^ (k + 1))
    (hkp : forall p, Membership.mem P p -> k < p.val)
    (hx : forall p, Membership.mem P p -> X < p.val ^ k)
    (hupper : forall p, Membership.mem P p -> p.val <= U)
    (hmean : forall p, Membership.mem P p ->
      vinogradovMeanValue k (k * (r - 1)) (1 + X / p.val) <= M) :
    vinogradovMeanValue k (k * r) X <=
      max
        (4 * (P.card ^ 2 *
          (U ^ (2 * (k * (r - 1))) *
            ((X ^ k * (k.factorial * U ^ (k * (k - 1) / 2))) * M))))
        (4 ^ (k * r) * k ^ (4 * (k * r))) := by
  apply vinogradovMeanValue_le_max_of_distinctSquareSum_le
    k r X
      (P.card ^ 2 *
        (U ^ (2 * (k * (r - 1))) *
          ((X ^ k * (k.factorial * U ^ (k * (k - 1) / 2))) * M)))
      (lt_trans (by omega) hr) hm
  exact linnikDistinctSquareSum_le_primeBand_uniform
    P k r X y U M hk hr hprime hy hcard hX hkp hx hupper hmean

/-- The root-scale Bertrand construction instantiates every hypothesis of the
complete distinct-branch consumer. -/
theorem exists_linnikDistinctSquareSum_le_nthRoot_primeBand
    (k r X : Nat) (hk : 0 < k) (hr : 1 < r)
    (hX : 0 < X) (hkX : k ^ k <= X) :
    exists P : Finset {p : Nat // 0 < p},
      P.card = k ^ 3 + 1 /\
        (forall p, Membership.mem P p ->
          p.val.Prime /\
            Nat.nthRoot k X < p.val /\
            p.val <= 2 ^ (k ^ 3 + 1) * Nat.nthRoot k X) /\
        linnikDistinctSquareSum k r X (lt_trans (by omega) hr) <=
          P.card * P.sum (fun p =>
            p.val ^ (2 * (k * (r - 1))) *
              ((X ^ k *
                  (k.factorial * p.val ^ (k * (k - 1) / 2))) *
                vinogradovMeanValue k (k * (r - 1))
                  (1 + X / p.val))) := by
  cases exists_linnikPrimeBand_for_nthRoot k X hk hX hkX with
  | intro P hP =>
      have hXRoot : X < (Nat.nthRoot k X + 1) ^ k :=
        Nat.lt_pow_nthRoot_add_one hk.ne' X
      have hgeom : X <= (Nat.nthRoot k X + 1) ^ (k + 1) := by
        exact le_trans (Nat.le_of_lt hXRoot)
          (Nat.pow_le_pow_right (by omega) (by omega))
      refine Exists.intro P (And.intro hP.1 (And.intro ?_ ?_))
      next =>
        intro p hpP
        have hp := hP.2 p hpP
        exact And.intro hp.1 (And.intro hp.2.1 hp.2.2.1)
      next =>
        apply linnikDistinctSquareSum_le_primeBand_vinogradovMeanValue
          P k r X (Nat.nthRoot k X) hk hr
        next =>
          intro p hpP
          exact (hP.2 p hpP).1
        next =>
          intro p hpP
          exact (hP.2 p hpP).2.1
        next => omega
        next => exact hgeom
        next =>
          intro p hpP
          exact (hP.2 p hpP).2.2.2.1
        next =>
          intro p hpP
          exact (hP.2 p hpP).2.2.2.2

/-- Fully instantiated recurrence with no free prime band: Bertrand's
construction and monotonicity reduce the distinct branch to one lower-level
mean value at the root-scale quotient. -/
theorem vinogradovMeanValue_le_nthRoot_recurrence
    (k r X : Nat) (hk : 0 < k) (hr : 1 < r) (hm : 2 <= k * r)
    (hX : 0 < X) (hkX : k ^ k <= X) :
    vinogradovMeanValue k (k * r) X <=
      max
        (4 * ((k ^ 3 + 1) ^ 2 *
          ((2 ^ (k ^ 3 + 1) * Nat.nthRoot k X) ^
              (2 * (k * (r - 1))) *
            ((X ^ k * (k.factorial *
                (2 ^ (k ^ 3 + 1) * Nat.nthRoot k X) ^
                  (k * (k - 1) / 2))) *
              vinogradovMeanValue k (k * (r - 1))
                (1 + X / (Nat.nthRoot k X + 1))))))
        (4 ^ (k * r) * k ^ (4 * (k * r))) := by
  cases exists_linnikPrimeBand_for_nthRoot k X hk hX hkX with
  | intro P hP =>
      have hXRoot : X < (Nat.nthRoot k X + 1) ^ k :=
        Nat.lt_pow_nthRoot_add_one hk.ne' X
      have hgeom : X <= (Nat.nthRoot k X + 1) ^ (k + 1) := by
        exact le_trans (Nat.le_of_lt hXRoot)
          (Nat.pow_le_pow_right (by omega) (by omega))
      have hrec := vinogradovMeanValue_le_primeBand_uniform
        P k r X (Nat.nthRoot k X)
          (2 ^ (k ^ 3 + 1) * Nat.nthRoot k X)
          (vinogradovMeanValue k (k * (r - 1))
            (1 + X / (Nat.nthRoot k X + 1)))
          hk hr hm
          (fun p hpP => (hP.2 p hpP).1)
          (fun p hpP => (hP.2 p hpP).2.1)
          (by omega) hgeom
          (fun p hpP => (hP.2 p hpP).2.2.2.1)
          (fun p hpP => (hP.2 p hpP).2.2.2.2)
          (fun p hpP => (hP.2 p hpP).2.2.1)
          (by
            intro p hpP
            apply vinogradovMeanValue_mono
            apply Nat.add_le_add_left
            exact Nat.div_le_div_left
              (Nat.succ_le_of_lt (hP.2 p hpP).2.1) (by omega))
      rw [hP.1] at hrec
      exact hrec

end Finset
