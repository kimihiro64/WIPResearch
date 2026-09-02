import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaSplitting

/-!
# Quadratic prime-ideal norm multiplicity

Every equal-norm fiber of prime ideals in the canonical quadratic field has
cardinality at most two. A nonempty fiber is injected into the prime ideals
above the rational prime recovered from any one of its members.
-/

namespace RobinBV.NumberField

open UniqueFactorizationMonoid

noncomputable section

/-- Prime ideals in the canonical quadratic field with absolute norm `n`. -/
def quadraticPrimeIdealNormFiber
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) :=
  {P : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
    And (Prime P) (Ideal.absNorm P = n)}

/-- At most two prime ideals in a quadratic field have any prescribed
absolute norm. -/
theorem quadraticPrimeIdealNormFiber_card_le_two
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) :
    Nat.card (quadraticPrimeIdealNormFiber D n) <= 2 := by
  classical
  rcases isEmpty_or_nonempty (quadraticPrimeIdealNormFiber D n) with
      hEmpty | hNonempty
  next =>
    letI : IsEmpty (quadraticPrimeIdealNormFiber D n) := hEmpty
    simp
  next =>
    let P := Classical.choice hNonempty
    have hPrimeP : Prime P.val := P.property.1
    let _ : P.val.IsMaximal :=
      (Ideal.isPrime_of_prime hPrimeP).isMaximal hPrimeP.ne_zero
    choose p k _hkPos _hpMem hp hNormP using
      Ideal.exists_prime_and_absNorm_eq_pow P.val
    letI : Fact (Nat.Prime p) := Fact.mk hp
    let toPrime : quadraticPrimeIdealNormFiber D n ->
        Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) := fun Q =>
      Subtype.mk Q.val (by
        have hPrimeQ : Prime Q.val := Q.property.1
        have hNormQ : Ideal.absNorm Q.val = p ^ k :=
          Q.property.2.trans (P.property.2.symm.trans hNormP)
        have hFactor : Membership.mem (normalizedFactors Q.val) Q.val := by
          apply (Ideal.mem_normalizedFactors_iff hPrimeQ.ne_zero).mpr
          exact And.intro (Ideal.isPrime_of_prime hPrimeQ) le_rfl
        exact
          NumberField.OddFundamentalDiscriminant.normalizedFactor_mem_primesOver_of_absNorm_eq_prime_pow
            D.QuadraticField p k Q.val hNormQ hFactor)
    have hInjective : Function.Injective toPrime := by
      intro Q R hQR
      have hVal : (toPrime Q).val = (toPrime R).val :=
        congrArg
          (fun Z : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) => Z.val)
          hQR
      apply Subtype.ext
      exact hVal
    calc
      Nat.card (quadraticPrimeIdealNormFiber D n) <=
          Nat.card
            (Ideal.primesOver
              (Ideal.span {(p : Int)})
              (NumberField.RingOfIntegers D.QuadraticField)) :=
        Nat.card_le_card_of_injective toPrime hInjective
      _ = Fintype.card
            (Ideal.primesOver
              (Ideal.span {(p : Int)})
              (NumberField.RingOfIntegers D.QuadraticField)) :=
        Nat.card_eq_fintype_card
      _ <= 2 := D.card_primesOver_quadraticField_le_two p

end

end RobinBV.NumberField
