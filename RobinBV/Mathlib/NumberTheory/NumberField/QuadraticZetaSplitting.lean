/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.GCD.BigOperators
public import RobinBV.Mathlib.NumberTheory.NumberField.Ideal.Factorization
public import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaAtTwo

/-!
# Splitting of rational primes in canonical quadratic fields

This file reconstructs ideals of prime-power norm from exponent vectors
on the primes above a rational prime and proves the exact split, ramified,
and inert classification from the canonical quadratic character.
-/

@[expose] public section

namespace NumberField.OddFundamentalDiscriminant

noncomputable section

open UniqueFactorizationMonoid

noncomputable def idealFromPrimeExponents
    (K : Type*) [Field K] [NumberField K]
    (p : Nat) [Fact (Nat.Prime p)]
    (f : Ideal.primesOver
      (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) -> Nat) :
    Ideal (NumberField.RingOfIntegers K) :=
  letI := Fintype.ofFinite
    (Ideal.primesOver
      (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K))
  Finset.univ.prod (fun P => P.val ^ f P)

theorem idealFromPrimeExponents_ne_zero
    (K : Type*) [Field K] [NumberField K]
    (p : Nat) [Fact (Nat.Prime p)]
    (f : Ideal.primesOver
      (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) -> Nat) :
    Not (idealFromPrimeExponents K p f = 0) := by
  classical
  unfold idealFromPrimeExponents
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  apply pow_ne_zero
  exact Ideal.ne_bot_of_mem_primesOver
    (by simp [NeZero.ne p]) P.property

theorem absNorm_idealFromPrimeExponents
    (K : Type*) [Field K] [NumberField K]
    (p : Nat) [Fact (Nat.Prime p)]
    (f : Ideal.primesOver
      (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) -> Nat) :
    Ideal.absNorm (idealFromPrimeExponents K p f) =
      p ^ (Finset.univ.sum
        (fun P => f P * Ideal.inertiaDeg P.val Int)) := by
  classical
  unfold idealFromPrimeExponents
  rw [map_prod Ideal.absNorm
    (fun P => P.val ^ f P) Finset.univ]
  simp_rw [map_pow, <- Ideal.pow_inertiaDeg p, <- pow_mul]
  simpa only [Nat.mul_comm] using
    (Finset.prod_pow_eq_pow_sum Finset.univ
      (fun P => f P * Ideal.inertiaDeg P.val Int) p)

theorem normalizedFactor_mem_primesOver_of_absNorm_eq_prime_pow
    (K : Type*) [Field K] [NumberField K]
    (p k : Nat) [Fact (Nat.Prime p)]
    (I : Ideal (NumberField.RingOfIntegers K))
    (hNorm : Ideal.absNorm I = p ^ k)
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (normalizedFactors I) P) :
    Membership.mem
      (Ideal.primesOver
        (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K)) P := by
  have hPrime : Prime P := prime_of_normalized_factor P hP
  have hMem : Membership.mem I
      ((p ^ k : Nat) : NumberField.RingOfIntegers K) := by
    rw [<- hNorm]
    exact Ideal.absNorm_mem I
  have hSpanLe :
      Ideal.span
        {((p ^ k : Nat) : NumberField.RingOfIntegers K)} <= I :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hMem)
  have hDvdPower : Dvd.dvd P
      ((Ideal.span
        {(p : NumberField.RingOfIntegers K)}) ^ k) := by
    apply Dvd.dvd.trans (dvd_of_mem_normalizedFactors hP)
    rw [Ideal.span_singleton_pow]
    apply Ideal.dvd_iff_le.mpr
    simpa only [Nat.cast_pow] using hSpanLe
  have hDvdBase : Dvd.dvd P
      (Ideal.span {(p : NumberField.RingOfIntegers K)}) :=
    hPrime.dvd_of_dvd_pow hDvdPower
  have hBaseNe : Not
      (Ideal.span {(p : NumberField.RingOfIntegers K)} = 0) := by
    simp [NeZero.ne p]
  have hBaseFactor : Membership.mem
      (normalizedFactors
        (Ideal.span {(p : NumberField.RingOfIntegers K)})) P :=
    (mem_normalizedFactors_iff hBaseNe).mpr
      (And.intro hPrime hDvdBase)
  apply
    (Ideal.mem_primesOver_iff_mem_normalizedFactors
      (NumberField.RingOfIntegers K)
      (by simp [NeZero.ne p] :
        Not (Ideal.span {(p : Int)} = 0))).mpr
  simpa [Ideal.map_span] using hBaseFactor

noncomputable def primeExponentVector
    (K : Type*) [Field K] [NumberField K]
    (p : Nat) [Fact (Nat.Prime p)]
    (I : Ideal (NumberField.RingOfIntegers K)) :
    Ideal.primesOver
      (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) -> Nat :=
  fun P => Multiset.count P.val (normalizedFactors I)

theorem idealFromPrimeExponents_primeExponentVector
    (K : Type*) [Field K] [NumberField K]
    (p k : Nat) [Fact (Nat.Prime p)]
    (I : Ideal (NumberField.RingOfIntegers K))
    (hNorm : Ideal.absNorm I = p ^ k) :
    idealFromPrimeExponents K p (primeExponentVector K p I) = I := by
  classical
  have hI : Not (I = 0) := by
    intro hzero
    subst I
    have hpow : Not (p ^ k = 0) :=
      pow_ne_zero k (Fact.out : Nat.Prime p).ne_zero
    exact hpow (by simpa using hNorm.symm)
  let s := (normalizedFactors I).toFinset
  let t := Finset.univ.filter
    (fun P : Ideal.primesOver
      (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) =>
        Membership.mem s P.val)
  have hUnivToT :
      (Finset.univ.prod
        (fun P : Ideal.primesOver
          (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) =>
            P.val ^ Multiset.count P.val (normalizedFactors I))) =
      t.prod
        (fun P : Ideal.primesOver
          (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) =>
            P.val ^ Multiset.count P.val (normalizedFactors I)) := by
    symm
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro P hUniv hNotT
    have hNotMem : Not (Membership.mem (normalizedFactors I) P.val) := by
      intro hMem
      apply hNotT
      apply Finset.mem_filter.mpr
      exact And.intro (Finset.mem_univ P)
        (by simpa [s] using hMem)
    have hCount : Multiset.count P.val (normalizedFactors I) = 0 :=
      Multiset.count_eq_zero.mpr hNotMem
    rw [hCount, pow_zero]
  have hTToS :
      t.prod
        (fun P : Ideal.primesOver
          (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) =>
            P.val ^ Multiset.count P.val (normalizedFactors I)) =
      s.prod
        (fun Q => Q ^ Multiset.count Q (normalizedFactors I)) := by
    apply Finset.prod_bij (fun P hP => P.val)
    next =>
      intro P hP
      exact (Finset.mem_filter.mp hP).2
    next =>
      intro P hP Q hQ hEq
      exact Subtype.val_injective hEq
    next =>
      intro Q hQ
      have hQMulti : Membership.mem (normalizedFactors I) Q := by
        simpa [s] using hQ
      let P : Ideal.primesOver
          (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) :=
        Subtype.mk Q
          (normalizedFactor_mem_primesOver_of_absNorm_eq_prime_pow
            K p k I hNorm hQMulti)
      apply Exists.intro P
      apply Exists.intro (by
        apply Finset.mem_filter.mpr
        exact And.intro (Finset.mem_univ P) (by simpa [s] using hQ))
      rfl
    next =>
      intro P hP
      rfl
  unfold idealFromPrimeExponents primeExponentVector
  rw [hUnivToT, hTToS]
  exact (Ideal.eq_prod_primeFactors_pow I hI).symm

noncomputable def primeFactorMultiset
    (K : Type*) [Field K] [NumberField K]
    (p : Nat) [Fact (Nat.Prime p)]
    (f : Ideal.primesOver
      (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) -> Nat) :
    Multiset (Ideal (NumberField.RingOfIntegers K)) :=
  letI := Fintype.ofFinite
    (Ideal.primesOver
      (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K))
  Finset.univ.1.bind
    (fun P => Multiset.replicate (f P) P.val)

theorem primeFactorMultiset_prod
    (K : Type*) [Field K] [NumberField K]
    (p : Nat) [Fact (Nat.Prime p)]
    (f : Ideal.primesOver
      (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) -> Nat) :
    (primeFactorMultiset K p f).prod =
      idealFromPrimeExponents K p f := by
  classical
  simp [primeFactorMultiset, idealFromPrimeExponents,
    Multiset.prod_bind, Multiset.prod_replicate]

theorem normalizedFactors_idealFromPrimeExponents
    (K : Type*) [Field K] [NumberField K]
    (p : Nat) [Fact (Nat.Prime p)]
    (f : Ideal.primesOver
      (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) -> Nat) :
    normalizedFactors (idealFromPrimeExponents K p f) =
      primeFactorMultiset K p f := by
  rw [<- primeFactorMultiset_prod K p f]
  apply normalizedFactors_prod_of_prime
  intro P hP
  rw [primeFactorMultiset, Multiset.mem_bind] at hP
  choose Q hQ using hP
  have hRep := hQ.2
  rw [Multiset.mem_replicate] at hRep
  rw [hRep.2]
  exact Ideal.prime_of_mem_primesOver
    (by simp [NeZero.ne p]) Q.property

theorem primeExponentVector_idealFromPrimeExponents
    (K : Type*) [Field K] [NumberField K]
    (p : Nat) [Fact (Nat.Prime p)]
    (f : Ideal.primesOver
      (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) -> Nat) :
    primeExponentVector K p (idealFromPrimeExponents K p f) = f := by
  funext P
  unfold primeExponentVector
  rw [normalizedFactors_idealFromPrimeExponents]
  classical
  unfold primeFactorMultiset
  rw [Multiset.count_bind]
  change Finset.univ.sum
    (fun Q => Multiset.count P.val
      (Multiset.replicate (f Q) Q.val)) = f P
  rw [Finset.sum_eq_single P]
  next =>
    simp
  next =>
    intro Q hQ hNe
    have hValNe : Not (Q.val = P.val) := by
      intro hVal
      exact hNe (Subtype.ext hVal)
    apply Multiset.count_eq_zero.mpr
    intro hMem
    have hEq := (Multiset.mem_replicate.mp hMem).2
    exact hValNe hEq.symm
  next =>
    simp

noncomputable def idealNormPrimePowEquivExponentVectors
    (K : Type*) [Field K] [NumberField K]
    (p k : Nat) [Fact (Nat.Prime p)] :
    Equiv
      {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = p ^ k}
      {f : Ideal.primesOver
          (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) -> Nat //
        Finset.univ.sum
          (fun P => f P * Ideal.inertiaDeg P.val Int) = k} := by
  let toVector :
      {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = p ^ k} ->
      {f : Ideal.primesOver
          (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) -> Nat //
        Finset.univ.sum
          (fun P => f P * Ideal.inertiaDeg P.val Int) = k} := fun I =>
    Subtype.mk (primeExponentVector K p I.val) (by
      have hNorm :=
        absNorm_idealFromPrimeExponents K p
          (primeExponentVector K p I.val)
      rw [idealFromPrimeExponents_primeExponentVector
        K p k I.val I.property, I.property] at hNorm
      exact Nat.pow_right_injective
        (Fact.out : Nat.Prime p).two_le hNorm.symm)
  let toIdeal :
      {f : Ideal.primesOver
          (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) -> Nat //
        Finset.univ.sum
          (fun P => f P * Ideal.inertiaDeg P.val Int) = k} ->
      {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = p ^ k} := fun f =>
    Subtype.mk (idealFromPrimeExponents K p f.val) (by
      rw [absNorm_idealFromPrimeExponents, f.property])
  exact Equiv.mk toVector toIdeal (by
    intro I
    apply Subtype.ext
    exact idealFromPrimeExponents_primeExponentVector
      K p k I.val I.property) (by
    intro f
    apply Subtype.ext
    exact primeExponentVector_idealFromPrimeExponents K p f.val)

theorem sum_ramification_inertia_quadraticField
    (D : OddFundamentalDiscriminant) (p : Nat) [Fact (Nat.Prime p)] :
    Finset.univ.sum
      (fun P : Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField) =>
          Ideal.ramificationIdx P.val Int *
            Ideal.inertiaDeg P.val Int) = 2 := by
  have hsum :=
    Ideal.sum_ramification_inertia_eq_finrank
      (p := Ideal.span {(p : Int)})
      (S := NumberField.RingOfIntegers D.QuadraticField)
  rw [NumberField.RingOfIntegers.rank,
    D.finrank_quadraticField] at hsum
  exact hsum

theorem card_primesOver_quadraticField_le_two
    (D : OddFundamentalDiscriminant) (p : Nat) [Fact (Nat.Prime p)] :
    Fintype.card
      (Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField)) <= 2 := by
  classical
  calc
    Fintype.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) =
        Finset.univ.sum (fun _ : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) => 1) := by
      simp
    _ <= Finset.univ.sum
        (fun P : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) =>
            Ideal.ramificationIdx P.val Int *
              Ideal.inertiaDeg P.val Int) := by
      apply Finset.sum_le_sum
      intro P hP
      have he := Ideal.ramificationIdx_pos P.val Int
      have hf := Ideal.inertiaDeg_pos P.val Int
      have hef := Nat.mul_pos he hf
      omega
    _ = 2 := D.sum_ramification_inertia_quadraticField p

theorem card_primesOver_quadraticField_pos
    (D : OddFundamentalDiscriminant) (p : Nat) [Fact (Nat.Prime p)] :
    0 < Fintype.card
      (Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField)) := by
  classical
  by_contra hzero
  have hcard :
      Fintype.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 0 := by
    omega
  have hempty :
      IsEmpty
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) :=
    Fintype.card_eq_zero_iff.mp hcard
  letI : IsEmpty
      (Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField)) := hempty
  have hsum := D.sum_ramification_inertia_quadraticField p
  simpa using hsum

theorem card_primesOver_inertiaDeg_one_eq_one_add_character
    (D : OddFundamentalDiscriminant) (p : Nat) (hp : Nat.Prime p) :
    (Nat.card
      {P : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.inertiaDeg P.val Int = 1} : Complex) =
      1 + D.character p := by
  letI : Fact (Nat.Prime p) := Fact.mk hp
  have hcard := Nat.card_congr
    (idealNormPrimeEquivPrimesOverInertiaOne D.QuadraticField p)
  rw [<- D.idealCountAtPrime_eq_one_add_character p hp]
  exact_mod_cast hcard.symm

theorem split_prime_card_and_inertiaDeg
    (D : OddFundamentalDiscriminant) (p : Nat) (hp : Nat.Prime p)
    (hchi : D.character p = 1) :
    And
      (Nat.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 2)
      (forall P : Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField),
          Ideal.inertiaDeg P.val Int = 1) := by
  letI : Fact (Nat.Prime p) := Fact.mk hp
  letI := Fintype.ofFinite
    (Ideal.primesOver
      (Ideal.span {(p : Int)})
      (NumberField.RingOfIntegers D.QuadraticField))
  have hsubComplex :=
    D.card_primesOver_inertiaDeg_one_eq_one_add_character p hp
  rw [hchi] at hsubComplex
  norm_num at hsubComplex
  have hsub :
      Fintype.card
        {P : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.inertiaDeg P.val Int = 1} = 2 := by
    exact_mod_cast hsubComplex
  have htotalLe := D.card_primesOver_quadraticField_le_two p
  have hsubLe :=
    Fintype.card_subtype_le
      (fun P : Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField) =>
          Ideal.inertiaDeg P.val Int = 1)
  have htotal :
      Fintype.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 2 := by
    omega
  have htotalNat :
      Nat.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 2 := by
    simpa only [Nat.card_eq_fintype_card] using htotal
  apply And.intro htotalNat
  intro P
  by_contra hP
  have hlt := Fintype.card_subtype_lt
    (p := fun Q : Ideal.primesOver
      (Ideal.span {(p : Int)})
      (NumberField.RingOfIntegers D.QuadraticField) =>
        Ideal.inertiaDeg Q.val Int = 1)
    (x := P) hP
  omega

theorem ramified_prime_card_and_inertiaDeg
    (D : OddFundamentalDiscriminant) (p : Nat) (hp : Nat.Prime p)
    (hchi : D.character p = 0) :
    And
      (Nat.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 1)
      (forall P : Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField),
          Ideal.inertiaDeg P.val Int = 1) := by
  letI : Fact (Nat.Prime p) := Fact.mk hp
  letI := Fintype.ofFinite
    (Ideal.primesOver
      (Ideal.span {(p : Int)})
      (NumberField.RingOfIntegers D.QuadraticField))
  have hsubComplex :=
    D.card_primesOver_inertiaDeg_one_eq_one_add_character p hp
  rw [hchi] at hsubComplex
  have hsubNat :
      Nat.card
        {P : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.inertiaDeg P.val Int = 1} = 1 := by
    exact_mod_cast hsubComplex
  have hsub :
      Fintype.card
        {P : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.inertiaDeg P.val Int = 1} = 1 := by
    simpa only [Nat.card_eq_fintype_card] using hsubNat
  have hSubNonempty :
      Nonempty
        {P : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.inertiaDeg P.val Int = 1} :=
    Fintype.card_pos_iff.mp (by omega)
  let Pgood := Classical.choice hSubNonempty
  have hAll :
      forall P : Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField),
          Ideal.inertiaDeg P.val Int = 1 := by
    intro P
    by_contra hBad
    have hNe : Not (P = Pgood.val) := by
      intro hEq
      apply hBad
      rw [hEq]
      exact Pgood.property
    let term := fun Q : Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField) =>
      Ideal.ramificationIdx Q.val Int * Ideal.inertiaDeg Q.val Int
    have hTermGood : 1 <= term Pgood.val := by
      have he := Ideal.ramificationIdx_pos Pgood.val.val Int
      dsimp only [term]
      rw [Pgood.property, mul_one]
      exact he
    have hfPos := Ideal.inertiaDeg_pos P.val Int
    have hfTwo : 2 <= Ideal.inertiaDeg P.val Int := by omega
    have hePos := Ideal.ramificationIdx_pos P.val Int
    have hTermBad : 2 <= term P := by
      dsimp only [term]
      calc
        2 = 1 * 2 := by norm_num
        _ <= Ideal.ramificationIdx P.val Int *
            Ideal.inertiaDeg P.val Int :=
          Nat.mul_le_mul (by omega) hfTwo
    have hBadMem :
        Membership.mem (Finset.univ.erase Pgood.val) P := by
      apply Finset.mem_erase.mpr
      exact And.intro hNe (Finset.mem_univ P)
    have hBadLe :
        term P <= (Finset.univ.erase Pgood.val).sum term :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hBadMem
    have hDecomp :=
      Finset.sum_erase_add Finset.univ term
        (Finset.mem_univ Pgood.val)
    have hSum := D.sum_ramification_inertia_quadraticField p
    change Finset.univ.sum term = 2 at hSum
    have hAtLeastThree :
        3 <= (Finset.univ.erase Pgood.val).sum term +
          term Pgood.val := by
      omega
    have hImpossible : 3 <= 2 := by
      rw [<- hSum, <- hDecomp]
      exact hAtLeastThree
    omega
  let eAll :
      Equiv
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField))
        {P : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.inertiaDeg P.val Int = 1} := {
    toFun P := Subtype.mk P (hAll P)
    invFun P := P.val
    left_inv P := rfl
    right_inv P := by apply Subtype.ext; rfl }
  have hTotalFintype := Fintype.card_congr eAll
  have hTotalNat :
      Nat.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 1 := by
    rw [Nat.card_eq_fintype_card, hTotalFintype, hsub]
  exact And.intro hTotalNat hAll

theorem inert_prime_card_and_inertiaDeg
    (D : OddFundamentalDiscriminant) (p : Nat) (hp : Nat.Prime p)
    (hchi : D.character p = -1) :
    And
      (Nat.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 1)
      (forall P : Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField),
          Ideal.inertiaDeg P.val Int = 2) := by
  letI : Fact (Nat.Prime p) := Fact.mk hp
  letI := Fintype.ofFinite
    (Ideal.primesOver
      (Ideal.span {(p : Int)})
      (NumberField.RingOfIntegers D.QuadraticField))
  have hsubComplex :=
    D.card_primesOver_inertiaDeg_one_eq_one_add_character p hp
  rw [hchi] at hsubComplex
  norm_num at hsubComplex
  have hsub :
      Fintype.card
        {P : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.inertiaDeg P.val Int = 1} = 0 := by
    exact_mod_cast hsubComplex
  have hNoOne :
      forall P : Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField),
          Not (Ideal.inertiaDeg P.val Int = 1) := by
    intro P hP
    have hEmpty :
        IsEmpty
          {Q : Ideal.primesOver
              (Ideal.span {(p : Int)})
              (NumberField.RingOfIntegers D.QuadraticField) //
            Ideal.inertiaDeg Q.val Int = 1} :=
      Fintype.card_eq_zero_iff.mp hsub
    exact hEmpty.false (Subtype.mk P hP)
  have hTotalLe := D.card_primesOver_quadraticField_le_two p
  have hTotalPos := D.card_primesOver_quadraticField_pos p
  have hTotalNotTwo :
      Not (Fintype.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 2) := by
    intro hTwo
    let e := Fintype.equivFinOfCardEq hTwo
    let Pzero := e.symm (0 : Fin 2)
    let Pone := e.symm (1 : Fin 2)
    have hNe : Not (Pone = Pzero) := by
      intro hEq
      have := e.symm.injective hEq
      norm_num at this
    let term := fun Q : Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField) =>
      Ideal.ramificationIdx Q.val Int * Ideal.inertiaDeg Q.val Int
    have hTermTwo :
        forall Q : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField),
            2 <= term Q := by
      intro Q
      have hfPos := Ideal.inertiaDeg_pos Q.val Int
      have hfTwo : 2 <= Ideal.inertiaDeg Q.val Int := by
        have hne := hNoOne Q
        omega
      have hePos := Ideal.ramificationIdx_pos Q.val Int
      dsimp only [term]
      calc
        2 = 1 * 2 := by norm_num
        _ <= Ideal.ramificationIdx Q.val Int *
            Ideal.inertiaDeg Q.val Int :=
          Nat.mul_le_mul (by omega) hfTwo
    have hOneMem :
        Membership.mem (Finset.univ.erase Pzero) Pone := by
      apply Finset.mem_erase.mpr
      exact And.intro hNe (Finset.mem_univ Pone)
    have hOneLe :
        term Pone <= (Finset.univ.erase Pzero).sum term :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hOneMem
    have hDecomp :=
      Finset.sum_erase_add Finset.univ term (Finset.mem_univ Pzero)
    have hSum := D.sum_ramification_inertia_quadraticField p
    change Finset.univ.sum term = 2 at hSum
    have hAtLeastFour :
        4 <= (Finset.univ.erase Pzero).sum term + term Pzero := by
      have hz := hTermTwo Pzero
      have ho := hTermTwo Pone
      omega
    have hImpossible : 4 <= 2 := by
      rw [<- hSum, <- hDecomp]
      exact hAtLeastFour
    omega
  have hTotal :
      Fintype.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 1 := by
    omega
  have hAll :
      forall P : Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField),
          Ideal.inertiaDeg P.val Int = 2 := by
    intro P
    let term := fun Q : Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField) =>
      Ideal.ramificationIdx Q.val Int * Ideal.inertiaDeg Q.val Int
    have hTermLe : term P <= Finset.univ.sum term :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ P)
    have hSum := D.sum_ramification_inertia_quadraticField p
    change Finset.univ.sum term = 2 at hSum
    have hePos := Ideal.ramificationIdx_pos P.val Int
    have hfPos := Ideal.inertiaDeg_pos P.val Int
    have hfLeTerm :
        Ideal.inertiaDeg P.val Int <= term P := by
      dsimp only [term]
      calc
        Ideal.inertiaDeg P.val Int =
            1 * Ideal.inertiaDeg P.val Int := by simp
        _ <= Ideal.ramificationIdx P.val Int *
            Ideal.inertiaDeg P.val Int :=
          Nat.mul_le_mul_right _ (by omega)
    have hne := hNoOne P
    omega
  have hTotalNat :
      Nat.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 1 := by
    simpa only [Nat.card_eq_fintype_card] using hTotal
  exact And.intro hTotalNat hAll


end

end NumberField.OddFundamentalDiscriminant
