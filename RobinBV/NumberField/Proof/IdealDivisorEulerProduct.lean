import RobinBV.Mathlib.NumberTheory.NumberField.Ideal.Factorization
import RobinBV.NumberField.Definitions.RobinCriterion

/-!
# Euler product for the ideal-divisor norm sum

The normalized prime-ideal factorization of a nonzero integral ideal gives a
finite family of independent exponent choices. This module proves that these
choices enumerate the ideal divisors exactly and factors their norm sum into
local finite geometric sums.
-/

open UniqueFactorizationMonoid

namespace RobinBV.NumberField

variable {K : Type*} [Field K] [NumberField K]

private abbrev PrimeSupport
    (I : Ideal (_root_.NumberField.RingOfIntegers K)) :=
  {P : Ideal (_root_.NumberField.RingOfIntegers K) //
    Membership.mem (normalizedFactors I).toFinset P}

private abbrev ExponentChoice
    (I : Ideal (_root_.NumberField.RingOfIntegers K)) :=
  (P : PrimeSupport I) ->
    Fin (Multiset.count P.val (normalizedFactors I) + 1)

private abbrev IdealDivisor
    (I : Ideal (_root_.NumberField.RingOfIntegers K)) :=
  {J : Ideal (_root_.NumberField.RingOfIntegers K) // Dvd.dvd J I}

private noncomputable def idealOfExponentChoice
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (e : ExponentChoice I) :
    Ideal (_root_.NumberField.RingOfIntegers K) :=
  ((Finset.univ : Finset (PrimeSupport I)).val.bind
    (fun P => Multiset.replicate (e P).val P.val)).prod

private noncomputable def choiceFactors
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (e : ExponentChoice I) :
    Multiset (Ideal (_root_.NumberField.RingOfIntegers K)) :=
  (Finset.univ : Finset (PrimeSupport I)).val.bind
    (fun P => Multiset.replicate (e P).val P.val)

private theorem choiceFactors_prod
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (e : ExponentChoice I) :
    (choiceFactors I e).prod = idealOfExponentChoice I e := by
  rfl

private theorem idealOfExponentChoice_eq_prod
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (e : ExponentChoice I) :
    idealOfExponentChoice I e =
      Finset.univ.prod (fun P : PrimeSupport I => P.val ^ (e P).val) := by
  rw [idealOfExponentChoice, Multiset.prod_bind]
  simp only [Multiset.prod_replicate]
  exact Finset.prod_map_val (Finset.univ : Finset (PrimeSupport I))
    (fun P => P.val ^ (e P).val)

private theorem count_choiceFactors
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (e : ExponentChoice I) (P : PrimeSupport I) :
    Multiset.count P.val (choiceFactors I e) = (e P).val := by
  classical
  rw [choiceFactors, Multiset.count_bind]
  change (Finset.univ : Finset (PrimeSupport I)).sum
    (fun Q => Multiset.count P.val (Multiset.replicate (e Q).val Q.val)) =
      (e P).val
  calc
    (Finset.univ : Finset (PrimeSupport I)).sum
        (fun Q => Multiset.count P.val
          (Multiset.replicate (e Q).val Q.val)) =
        Multiset.count P.val (Multiset.replicate (e P).val P.val) := by
      apply Finset.sum_eq_single P
      next =>
        intro Q _hQ hQP
        rw [Multiset.count_replicate]
        have hVal : Not (Q.val = P.val) := by
          intro hEq
          exact hQP (Subtype.ext hEq)
        simp [hVal]
      next => simp
    _ = (e P).val := Multiset.count_replicate_self P.val (e P).val

private theorem choiceFactors_prime
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (e : ExponentChoice I) (P : Ideal (_root_.NumberField.RingOfIntegers K))
    (hP : Membership.mem (choiceFactors I e) P) : Prime P := by
  rw [choiceFactors, Multiset.mem_bind] at hP
  choose Q _hQ hPQ using hP
  rw [Multiset.mem_replicate] at hPQ
  exact hPQ.2.symm.subst
    (prime_of_normalized_factor Q.val (Multiset.mem_toFinset.mp Q.property))

private theorem normalizedFactors_idealOfExponentChoice
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (e : ExponentChoice I) :
    normalizedFactors (idealOfExponentChoice I e) = choiceFactors I e := by
  rw [(choiceFactors_prod I e).symm]
  exact normalizedFactors_prod_of_prime (choiceFactors_prime I e)

private theorem absNorm_idealOfExponentChoice
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (e : ExponentChoice I) :
    Ideal.absNorm (idealOfExponentChoice I e) =
      Finset.univ.prod (fun P : PrimeSupport I =>
        Ideal.absNorm P.val ^ (e P).val) := by
  rw [idealOfExponentChoice_eq_prod]
  simp

private theorem idealOfExponentChoice_dvd
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (hI : Not (I = 0)) (e : ExponentChoice I) :
    Dvd.dvd (idealOfExponentChoice I e) I := by
  let Q : Ideal (_root_.NumberField.RingOfIntegers K) :=
    Finset.univ.prod fun P : PrimeSupport I =>
      P.val ^ (Multiset.count P.val (normalizedFactors I) - (e P).val)
  apply Exists.intro Q
  calc
    I = (normalizedFactors I).toFinset.prod
        (fun P => P ^ Multiset.count P (normalizedFactors I)) :=
      Ideal.eq_prod_primeFactors_pow I hI
    _ = Finset.univ.prod (fun P : PrimeSupport I =>
        P.val ^ Multiset.count P.val (normalizedFactors I)) := by
      exact (Finset.prod_coe_sort (normalizedFactors I).toFinset
        (fun P => P ^ Multiset.count P (normalizedFactors I))).symm
    _ = idealOfExponentChoice I e * Q := by
      rw [idealOfExponentChoice_eq_prod]
      dsimp [Q]
      rw [Finset.prod_mul_distrib.symm]
      apply Finset.prod_congr rfl
      intro P _hP
      rw [(pow_add P.val (e P).val
        (Multiset.count P.val (normalizedFactors I) - (e P).val)).symm]
      congr
      exact (Nat.add_sub_of_le (Nat.lt_succ_iff.mp (e P).isLt)).symm

private noncomputable def exponentChoiceOfDivisor
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (hI : Not (I = 0)) (J : IdealDivisor I) : ExponentChoice I := by
  classical
  have hJ0 : Not (J.val = 0) := by
    intro hJ
    have hDvd := J.property
    rw [hJ, zero_dvd_iff] at hDvd
    exact hI hDvd
  have hle : normalizedFactors J.val <= normalizedFactors I :=
    (dvd_iff_normalizedFactors_le_normalizedFactors hJ0 hI).mp J.property
  intro P
  apply Fin.mk (Multiset.count P.val (normalizedFactors J.val))
  exact Nat.lt_succ_of_le ((Multiset.le_iff_count.mp hle) P.val)

private theorem idealOfExponentChoice_exponentChoiceOfDivisor
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (hI : Not (I = 0)) (J : IdealDivisor I) :
    idealOfExponentChoice I (exponentChoiceOfDivisor I hI J) = J.val := by
  classical
  have hJ0 : Not (J.val = 0) := by
    intro hJ
    have hDvd := J.property
    rw [hJ, zero_dvd_iff] at hDvd
    exact hI hDvd
  have hle : normalizedFactors J.val <= normalizedFactors I :=
    (dvd_iff_normalizedFactors_le_normalizedFactors hJ0 hI).mp J.property
  have hsubset :
      (normalizedFactors J.val).toFinset <= (normalizedFactors I).toFinset := by
    intro P hP
    rw [Multiset.mem_toFinset] at hP
    rw [Multiset.mem_toFinset]
    exact Multiset.mem_of_le hle hP
  calc
    idealOfExponentChoice I (exponentChoiceOfDivisor I hI J) =
        Finset.univ.prod (fun P : PrimeSupport I =>
          P.val ^ Multiset.count P.val (normalizedFactors J.val)) := by
      rw [idealOfExponentChoice_eq_prod]
      apply Finset.prod_congr rfl
      intro P _hP
      rfl
    _ =
        (normalizedFactors I).toFinset.prod
          (fun P => P ^ Multiset.count P (normalizedFactors J.val)) := by
      exact (Finset.prod_subtype
        (p := fun P => Membership.mem (normalizedFactors I).toFinset P)
        (normalizedFactors I).toFinset (fun _P => Iff.rfl)
        (fun P => P ^ Multiset.count P (normalizedFactors J.val))).symm
    _ = (normalizedFactors J.val).toFinset.prod
          (fun P => P ^ Multiset.count P (normalizedFactors J.val)) := by
      symm
      apply Finset.prod_subset hsubset
      intro P _hPI hPJ
      rw [pow_eq_one_iff]
      right
      exact Multiset.count_eq_zero_of_notMem
        (fun hMem => hPJ (Multiset.mem_toFinset.mpr hMem))
    _ = J.val := (Ideal.eq_prod_primeFactors_pow J.val hJ0).symm

private theorem exponentChoiceOfDivisor_idealOfExponentChoice
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (hI : Not (I = 0)) (e : ExponentChoice I) :
    exponentChoiceOfDivisor I hI
        (Subtype.mk (idealOfExponentChoice I e)
          (idealOfExponentChoice_dvd I hI e)) = e := by
  funext P
  apply Fin.ext
  change Multiset.count P.val
      (normalizedFactors (idealOfExponentChoice I e)) = (e P).val
  rw [normalizedFactors_idealOfExponentChoice, count_choiceFactors]

private noncomputable def exponentChoiceEquivIdealDivisor
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (hI : Not (I = 0)) : Equiv (ExponentChoice I) (IdealDivisor I) :=
  Equiv.mk
    (fun e => Subtype.mk (idealOfExponentChoice I e)
      (idealOfExponentChoice_dvd I hI e))
    (exponentChoiceOfDivisor I hI)
    (exponentChoiceOfDivisor_idealOfExponentChoice I hI)
    (fun J => Subtype.ext (idealOfExponentChoice_exponentChoiceOfDivisor I hI J))

private noncomputable def idealDivisors
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) :
    Finset (Ideal (_root_.NumberField.RingOfIntegers K)) := by
  classical
  exact
    (idealsUpToNorm K (Ideal.absNorm
      (I : Ideal (_root_.NumberField.RingOfIntegers K)))).filter
        (fun J => Dvd.dvd J (I : Ideal (_root_.NumberField.RingOfIntegers K)))

private theorem mem_idealDivisors_iff
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K)))
    (J : Ideal (_root_.NumberField.RingOfIntegers K)) :
    Membership.mem (idealDivisors I) J <->
      Dvd.dvd J (I : Ideal (_root_.NumberField.RingOfIntegers K)) := by
  classical
  constructor
  next =>
    intro hJ
    exact (Finset.mem_filter.mp hJ).2
  next =>
    intro hJ
    apply Finset.mem_filter.mpr
    apply And.intro
    next =>
      simp only [idealsUpToNorm, Set.Finite.mem_toFinset,
        Set.mem_ofPred_eq]
      apply Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors I)
      exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hJ)
    next => exact hJ

private noncomputable instance idealDivisorFintype
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) :
    Fintype (IdealDivisor (I :
      Ideal (_root_.NumberField.RingOfIntegers K))) :=
  UniqueFactorizationMonoid.fintypeSubtypeDvd
    (I : Ideal (_root_.NumberField.RingOfIntegers K))
    (nonZeroDivisors.coe_ne_zero I)

private theorem idealDivisorSum_eq_sum_divisors
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) :
    idealDivisorSum K I =
      Finset.univ.sum (fun J : IdealDivisor
        (I : Ideal (_root_.NumberField.RingOfIntegers K)) =>
          Ideal.absNorm J.val) := by
  classical
  calc
    idealDivisorSum K I =
        (idealDivisors I).sum Ideal.absNorm := by
      unfold idealDivisorSum idealDivisors
      rw [Finset.sum_filter]
    _ = Finset.univ.sum (fun J : IdealDivisor
        (I : Ideal (_root_.NumberField.RingOfIntegers K)) =>
          Ideal.absNorm J.val) := by
      exact Finset.sum_subtype (idealDivisors I)
        (fun J => mem_idealDivisors_iff I J) Ideal.absNorm

private theorem sum_pi_prod_eq_prod_sum
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (beta : alpha -> Type*) [forall i, Fintype (beta i)]
    (f : (i : alpha) -> beta i -> Nat) :
    Finset.univ.sum (fun x : (i : alpha) -> beta i =>
        Finset.univ.prod (fun i => f i (x i))) =
      Finset.univ.prod (fun i => Finset.univ.sum (fun j => f i j)) := by
  exact (Fintype.prod_sum f).symm

private theorem sum_prod_absNorm_eq_prod_sum
    (I : Ideal (_root_.NumberField.RingOfIntegers K)) :
    Finset.univ.sum (fun e : ExponentChoice I =>
        Finset.univ.prod (fun P : PrimeSupport I =>
          Ideal.absNorm P.val ^ (e P).val)) =
      Finset.univ.prod (fun P : PrimeSupport I =>
        Finset.univ.sum (fun j : Fin
            (Multiset.count P.val (normalizedFactors I) + 1) =>
          Ideal.absNorm P.val ^ j.val)) := by
  exact sum_pi_prod_eq_prod_sum
    (fun P : PrimeSupport I =>
      Fin (Multiset.count P.val (normalizedFactors I) + 1))
    (fun P j => Ideal.absNorm P.val ^ j.val)

theorem idealDivisorSum_eq_prod_geometric
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) :
    idealDivisorSum K I =
      Finset.univ.prod
        (fun P : {P : Ideal (_root_.NumberField.RingOfIntegers K) //
            Membership.mem
              (normalizedFactors
                (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset P} =>
          Finset.univ.sum
            (fun j : Fin (Multiset.count P.val
                (normalizedFactors
                  (I : Ideal (_root_.NumberField.RingOfIntegers K))) + 1) =>
              Ideal.absNorm P.val ^ j.val)) := by
  classical
  let rawI : Ideal (_root_.NumberField.RingOfIntegers K) := I
  have hI : Not (rawI = 0) := nonZeroDivisors.coe_ne_zero I
  calc
    idealDivisorSum K I =
        Finset.univ.sum (fun J : IdealDivisor rawI =>
          Ideal.absNorm J.val) := idealDivisorSum_eq_sum_divisors I
    _ = Finset.univ.sum (fun e : ExponentChoice rawI =>
          Ideal.absNorm (idealOfExponentChoice rawI e)) := by
      exact ((exponentChoiceEquivIdealDivisor rawI hI).sum_comp
        (fun J => Ideal.absNorm J.val)).symm
    _ = Finset.univ.sum (fun e : ExponentChoice rawI =>
          Finset.univ.prod (fun P : PrimeSupport rawI =>
            Ideal.absNorm P.val ^ (e P).val)) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact absNorm_idealOfExponentChoice rawI e
    _ = Finset.univ.prod (fun P : PrimeSupport rawI =>
          Finset.univ.sum (fun j : Fin
              (Multiset.count P.val (normalizedFactors rawI) + 1) =>
            Ideal.absNorm P.val ^ j.val)) := by
      exact sum_prod_absNorm_eq_prod_sum rawI

end RobinBV.NumberField
