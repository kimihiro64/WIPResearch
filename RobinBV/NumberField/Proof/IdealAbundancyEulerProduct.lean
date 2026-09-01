import RobinBV.NumberField.Proof.IdealDivisorEulerProduct

/-!
# Local product formula for ideal abundancy

The ideal-divisor Euler product and canonical absolute-norm product combine,
after casting to the reals, to express ideal abundancy as a product of local
prime-ideal factors.
-/

open UniqueFactorizationMonoid

namespace RobinBV.NumberField

variable {K : Type*} [Field K] [NumberField K]

private theorem cast_idealDivisorSum_eq_prod_geometric
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) :
    (idealDivisorSum K I : Real) =
      Finset.univ.prod
        (fun P : {P : Ideal (_root_.NumberField.RingOfIntegers K) //
            Membership.mem
              (normalizedFactors
                (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset P} =>
          Finset.univ.sum
            (fun j : Fin (Multiset.count P.val
                (normalizedFactors
                  (I : Ideal (_root_.NumberField.RingOfIntegers K))) + 1) =>
              (Ideal.absNorm P.val : Real) ^ j.val)) := by
  norm_cast
  exact idealDivisorSum_eq_prod_geometric I

theorem cast_absNorm_eq_prod_primeFactors_pow
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) :
    (Ideal.absNorm
        (I : Ideal (_root_.NumberField.RingOfIntegers K)) : Real) =
      Finset.univ.prod
        (fun P : {P : Ideal (_root_.NumberField.RingOfIntegers K) //
            Membership.mem
              (normalizedFactors
                (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset P} =>
          (Ideal.absNorm P.val : Real) ^
            Multiset.count P.val
              (normalizedFactors
                (I : Ideal (_root_.NumberField.RingOfIntegers K)))) := by
  classical
  calc
    (Ideal.absNorm
        (I : Ideal (_root_.NumberField.RingOfIntegers K)) : Real) =
        (((normalizedFactors
            (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset.prod
          (fun P => Ideal.absNorm P ^ Multiset.count P
            (normalizedFactors
              (I : Ideal (_root_.NumberField.RingOfIntegers K))))) : Nat) := by
      norm_cast
      exact Ideal.absNorm_eq_prod_primeFactors_pow
        (I : Ideal (_root_.NumberField.RingOfIntegers K))
        (nonZeroDivisors.coe_ne_zero I)
    _ = (normalizedFactors
            (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset.prod
          (fun P => (Ideal.absNorm P : Real) ^ Multiset.count P
            (normalizedFactors
              (I : Ideal (_root_.NumberField.RingOfIntegers K)))) := by
      simp
    _ = Finset.univ.prod
        (fun P : {P : Ideal (_root_.NumberField.RingOfIntegers K) //
            Membership.mem
              (normalizedFactors
                (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset P} =>
          (Ideal.absNorm P.val : Real) ^
            Multiset.count P.val
              (normalizedFactors
                (I : Ideal (_root_.NumberField.RingOfIntegers K)))) := by
      exact Finset.prod_subtype
        (p := fun P => Membership.mem
          (normalizedFactors
            (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset P)
        (normalizedFactors
          (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset
        (fun _P => Iff.rfl)
        (fun P => (Ideal.absNorm P : Real) ^ Multiset.count P
          (normalizedFactors
            (I : Ideal (_root_.NumberField.RingOfIntegers K))))

theorem idealAbundancy_eq_prod_local
    (I : nonZeroDivisors
      (Ideal (_root_.NumberField.RingOfIntegers K))) :
    idealAbundancy K I =
      Finset.univ.prod
        (fun P : {P : Ideal (_root_.NumberField.RingOfIntegers K) //
            Membership.mem
              (normalizedFactors
                (I : Ideal (_root_.NumberField.RingOfIntegers K))).toFinset P} =>
          (Finset.univ.sum
            (fun j : Fin (Multiset.count P.val
                (normalizedFactors
                  (I : Ideal (_root_.NumberField.RingOfIntegers K))) + 1) =>
              (Ideal.absNorm P.val : Real) ^ j.val)) /
            ((Ideal.absNorm P.val : Real) ^
              Multiset.count P.val
                (normalizedFactors
                  (I : Ideal (_root_.NumberField.RingOfIntegers K))))) := by
  rw [idealAbundancy, cast_idealDivisorSum_eq_prod_geometric,
    cast_absNorm_eq_prod_primeFactors_pow, Finset.prod_div_distrib]

end RobinBV.NumberField
