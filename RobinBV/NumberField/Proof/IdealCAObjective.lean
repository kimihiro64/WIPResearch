import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import RobinBV.NumberField.Definitions.IdealCA
import RobinBV.NumberField.Proof.IdealAbundancyEulerProduct

/-!
# Local factorization of the ideal CA objective

The CA objective of a nonzero integral ideal is exactly the product of its
norm-local factors. Consequently, pointwise comparison of local exponent
choices gives comparison of the full fixed-support profiles.
-/

open UniqueFactorizationMonoid

namespace RobinBV.NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem idealCALocalFactor_nonneg
    (epsilon : Real) (q e : Nat) :
    0 <= idealCALocalFactor epsilon q e := by
  unfold idealCALocalFactor
  positivity

@[simp] theorem idealCALocalFactor_zero
    (epsilon : Real) (q : Nat) :
    idealCALocalFactor epsilon q 0 = 1 := by
  simp [idealCALocalFactor]

theorem idealCAProfileObjective_nonneg
    (epsilon : Real)
    (S : Finset (Ideal (_root_.NumberField.RingOfIntegers K)))
    (exponent : Ideal (_root_.NumberField.RingOfIntegers K) -> Nat) :
    0 <= idealCAProfileObjective K epsilon S exponent := by
  unfold idealCAProfileObjective
  exact Finset.prod_nonneg fun P _ =>
    idealCALocalFactor_nonneg epsilon (Ideal.absNorm P) (exponent P)

/-- Pointwise domination of every local factor implies domination of the full
fixed-support exponent profile. -/
theorem idealCAProfileObjective_le_of_pointwise
    (epsilon : Real)
    (S : Finset (Ideal (_root_.NumberField.RingOfIntegers K)))
    {exponent maximizer :
      Ideal (_root_.NumberField.RingOfIntegers K) -> Nat}
    (hlocal : forall P, Membership.mem S P ->
      idealCALocalFactor epsilon (Ideal.absNorm P) (exponent P) <=
        idealCALocalFactor epsilon (Ideal.absNorm P) (maximizer P)) :
    idealCAProfileObjective K epsilon S exponent <=
      idealCAProfileObjective K epsilon S maximizer := by
  unfold idealCAProfileObjective
  exact Finset.prod_le_prod
    (fun P _ =>
      idealCALocalFactor_nonneg epsilon (Ideal.absNorm P) (exponent P))
    hlocal

private theorem idealCAProfileObjective_eq_prod_subtype
    (epsilon : Real)
    (S : Finset (Ideal (_root_.NumberField.RingOfIntegers K)))
    (exponent : Ideal (_root_.NumberField.RingOfIntegers K) -> Nat) :
    idealCAProfileObjective K epsilon S exponent =
      Finset.univ.prod
        (fun P : {P : Ideal (_root_.NumberField.RingOfIntegers K) //
            Membership.mem S P} =>
          idealCALocalFactor epsilon (Ideal.absNorm P.val) (exponent P.val)) := by
  unfold idealCAProfileObjective
  exact Finset.prod_subtype
    (p := fun P => Membership.mem S P)
    S
    (fun _P => Iff.rfl)
    (fun P => idealCALocalFactor epsilon (Ideal.absNorm P) (exponent P))

/-- Enlarging a profile support by positions with exponent zero leaves its
objective unchanged. -/
theorem idealCAProfileObjective_eq_of_subset
    (epsilon : Real)
    (S T : Finset (Ideal (_root_.NumberField.RingOfIntegers K)))
    (exponent : Ideal (_root_.NumberField.RingOfIntegers K) -> Nat)
    (hST : S <= T)
    (hzero : forall P, Membership.mem T P -> Not (Membership.mem S P) ->
      exponent P = 0) :
    idealCAProfileObjective K epsilon S exponent =
      idealCAProfileObjective K epsilon T exponent := by
  unfold idealCAProfileObjective
  apply Finset.prod_subset hST
  intro P hPT hPS
  rw [hzero P hPT hPS, idealCALocalFactor_zero]

private theorem absNorm_rpow_eq_prod_local
    (epsilon : Real)
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) :
    (Ideal.absNorm
        (I : Ideal (_root_.NumberField.RingOfIntegers K)) : Real) ^ epsilon =
      Finset.univ.prod
        (fun P : {P : Ideal (_root_.NumberField.RingOfIntegers K) //
            Membership.mem
              (normalizedFactors
                (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset P} =>
          (((Ideal.absNorm P.val : Real) ^
            Multiset.count P.val
              (normalizedFactors
                (I : Ideal (_root_.NumberField.RingOfIntegers K))))) ^ epsilon) := by
  rw [cast_absNorm_eq_prod_primeFactors_pow]
  symm
  exact Real.finsetProd_rpow Finset.univ _ (by
    intro P _hP
    positivity) epsilon

/-- The abundancy-based definition is exactly the ideal-divisor sum divided
by absolute norm to the `1 + epsilon` power. -/
theorem idealCAObjective_eq_divisorSum_div_rpow
    (epsilon : Real)
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) :
    idealCAObjective K epsilon I =
      (idealDivisorSum K I : Real) /
        ((Ideal.absNorm
          (I : Ideal (_root_.NumberField.RingOfIntegers K)) : Real) ^
            (1 + epsilon)) := by
  unfold idealCAObjective idealAbundancy
  have hnorm : 0 <
      (Ideal.absNorm
        (I : Ideal (_root_.NumberField.RingOfIntegers K)) : Real) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
  rw [Real.rpow_add hnorm, Real.rpow_one, div_div]

/-- The ideal CA objective factors over the canonical prime-ideal exponent
profile. -/
theorem idealCAObjective_eq_profileObjective
    (epsilon : Real)
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) :
    idealCAObjective K epsilon I =
      idealCAProfileObjective K epsilon
        (normalizedFactors
          (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset
        (fun P => Multiset.count P
          (normalizedFactors
            (I : Ideal (_root_.NumberField.RingOfIntegers K)))) := by
  rw [idealCAProfileObjective_eq_prod_subtype]
  rw [idealCAObjective, idealAbundancy_eq_prod_local,
    absNorm_rpow_eq_prod_local]
  simp only [idealCALocalFactor, Finset.prod_div_distrib]

/-- The canonical exponent profile of an ideal may be evaluated on any finite
support containing its canonical prime-ideal support. -/
theorem idealCAObjective_eq_profileObjective_of_subset
    (epsilon : Real)
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K)))
    (S : Finset (Ideal (_root_.NumberField.RingOfIntegers K)))
    (hsupport :
      (normalizedFactors
        (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset <= S) :
    idealCAObjective K epsilon I =
      idealCAProfileObjective K epsilon S
        (fun P => Multiset.count P
          (normalizedFactors
            (I : Ideal (_root_.NumberField.RingOfIntegers K)))) := by
  calc
    idealCAObjective K epsilon I =
        idealCAProfileObjective K epsilon
          (normalizedFactors
            (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset
          (fun P => Multiset.count P
            (normalizedFactors
              (I : Ideal (_root_.NumberField.RingOfIntegers K)))) :=
      idealCAObjective_eq_profileObjective epsilon I
    _ = idealCAProfileObjective K epsilon S
          (fun P => Multiset.count P
            (normalizedFactors
              (I : Ideal (_root_.NumberField.RingOfIntegers K)))) := by
      apply idealCAProfileObjective_eq_of_subset epsilon _ S _ hsupport
      intro P _hPS hP
      apply Multiset.count_eq_zero_of_notMem
      simpa using hP

/-- Comparing local factors on the union of two canonical supports compares
the full CA objectives of the two ideals. -/
theorem idealCAObjective_le_of_localFactors
    (epsilon : Real)
    (I J : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K)))
    (hlocal : forall P, Membership.mem
        (Max.max
          (normalizedFactors
            (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset
          (normalizedFactors
            (J : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset) P ->
      idealCALocalFactor epsilon (Ideal.absNorm P)
          (Multiset.count P
            (normalizedFactors
              (J : Ideal (_root_.NumberField.RingOfIntegers K)))) <=
        idealCALocalFactor epsilon (Ideal.absNorm P)
          (Multiset.count P
            (normalizedFactors
              (I : Ideal (_root_.NumberField.RingOfIntegers K))))) :
    idealCAObjective K epsilon J <= idealCAObjective K epsilon I := by
  let S := Max.max
    (normalizedFactors
      (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset
    (normalizedFactors
      (J : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset
  rw [idealCAObjective_eq_profileObjective_of_subset epsilon J S
      Finset.subset_union_right,
    idealCAObjective_eq_profileObjective_of_subset epsilon I S
      Finset.subset_union_left]
  exact idealCAProfileObjective_le_of_pointwise epsilon S hlocal

/-- Prime-by-prime global maximality of the local exponent choices is
sufficient for an ideal to be globally colossally abundant. -/
theorem isColossallyAbundantIdeal_of_prime_localMax
    (epsilon : Real)
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K)))
    (hmax : forall P : Ideal (_root_.NumberField.RingOfIntegers K),
      P.IsPrime -> forall e : Nat,
        idealCALocalFactor epsilon (Ideal.absNorm P) e <=
          idealCALocalFactor epsilon (Ideal.absNorm P)
            (Multiset.count P
              (normalizedFactors
                (I : Ideal (_root_.NumberField.RingOfIntegers K))))) :
    IsColossallyAbundantIdeal K epsilon I := by
  intro J
  apply idealCAObjective_le_of_localFactors epsilon I J
  intro P hP
  apply hmax P
  next =>
    have hor := Finset.mem_union.mp hP
    cases hor with
    | inl hPI =>
        have h := (Ideal.mem_normalizedFactors_iff
          (nonZeroDivisors.coe_ne_zero I)).mp (by simpa using hPI)
        exact h.1
    | inr hPJ =>
        have h := (Ideal.mem_normalizedFactors_iff
          (nonZeroDivisors.coe_ne_zero J)).mp (by simpa using hPJ)
        exact h.1

end RobinBV.NumberField
