import RobinBV.NumberField.Proof.ImprimitiveEndpointAsymptotic
import RobinBV.NumberField.Proof.RiemannCriticalBound

/-!
# Actual centered principal-character endpoint integrals

The principal Chebyshev function is centered before integration. Its complete
difference from zeta is integrable unconditionally and has an explicit
inverse-cutoff term. No divergent uncentered integral is split.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set

noncomputable section

/-- The primitive component of a principal character has exactly the ordinary
Chebyshev sum, including cutoff zero. -/
theorem characterChebyshevSum_primitive_principal_eq_psi
    {N : Nat} [NeZero N] (t : Real) :
    characterChebyshevSum (Nat.floor t)
      (1 : DirichletCharacter Complex N).primitiveCharacter = (Chebyshev.psi t : Complex) := by
  unfold characterChebyshevSum BombieriVinogradov.VaughanMeanValue.psiCharacterSum
  rw [Chebyshev.psi_eq_sum_Icc]
  push_cast
  calc
    _ = Finset.sum (Finset.Icc 1 (Nat.floor t))
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hValue : (1 : DirichletCharacter Complex N).primitiveCharacter n = 1 := by
        rw [DirichletCharacter.primitiveCharacter_one]
        apply MulChar.one_apply
        have hConductor : (1 : DirichletCharacter Complex N).conductor = 1 :=
          DirichletCharacter.conductor_one
        rw [hConductor]
        exact isUnit_of_subsingleton _
      rw [hValue, mul_one]
    _ = _ := by
      apply Finset.sum_subset
      next =>
        intro n hn
        simp only [Finset.mem_Icc] at hn
        exact Finset.mem_Icc.mpr (And.intro (Nat.zero_le n) hn.2)
      next =>
        intro n hn hnNot
        have hZero : n = 0 := by
          simp only [Finset.mem_Icc] at hn hnNot
          omega
        simp [hZero]

/-- Every excluded prime is resonant for a principal character. The exact
step-error constant is the sum of the logarithms of all distinct prime
divisors; no prime is omitted. -/
theorem principalImprimitiveConstants
    {N : Nat} [NeZero N] :
    And
      (imprimitiveResonanceCount (1 : DirichletCharacter Complex N) = N.primeFactors.card)
      (imprimitiveStepErrorBound (1 : DirichletCharacter Complex N) =
        Finset.sum N.primeFactors (fun p => Real.log p)) := by
  have hValue : forall p : Nat,
      (1 : DirichletCharacter Complex N).primitiveCharacter p = 1 := by
    intro p
    rw [DirichletCharacter.primitiveCharacter_one]
    apply MulChar.one_apply
    have hConductor : (1 : DirichletCharacter Complex N).conductor = 1 :=
      DirichletCharacter.conductor_one
    rw [hConductor]
    exact isUnit_of_subsingleton _
  constructor
  next =>
    simp [imprimitiveResonanceCount, DirichletCharacter.primePowerResonance, hValue]
  next =>
    unfold imprimitiveStepErrorBound
    apply Finset.sum_congr rfl
    intro p hp
    unfold DirichletCharacter.primePowerStepErrorBound
    rw [if_pos (hValue p)]

/-- The actual principal-character tail, centered by its pole contribution
before integration. -/
def principalCenteredWeightedIntegral (N : Nat) [NeZero N] (x : Real) : Complex :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    (characterChebyshevSum (Nat.floor t) (1 : DirichletCharacter Complex N) - (t : Complex)) *
      (Robin1984.robinRealWeight 1 t : Complex))

/-- Absolute integrability of the actual centered principal endpoint follows
from the rational centered tail and the full finite conductor correction. -/
theorem integrableOn_principalCenteredWeightedError
    {N : Nat} [NeZero N] {x : Real} (hx : 3 <= x) :
    IntegrableOn (fun t : Real =>
      (characterChebyshevSum (Nat.floor t) (1 : DirichletCharacter Complex N) - (t : Complex)) *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
  have hDifference := integrableOn_imprimitiveChebyshevStep_mul_weight
    (1 : DirichletCharacter Complex N) hx
  have hRational : IntegrableOn (fun t : Real =>
      (((Chebyshev.psi t - t) * Robin1984.robinRealWeight 1 t : Real) : Complex)) (Ioi x) :=
    (integrableOn_quadraticRationalWeightedError_one (x := x) (by linarith : 2 <= x)).ofReal
  apply (hDifference.add hRational).congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only [Pi.add_apply]
  rw [characterChebyshevSum_primitive_principal_eq_psi]
  push_cast
  ring

/-- Exact complete correction between the centered principal endpoint and
Nicolas's actual zeta tail. -/
theorem principalCenteredWeightedIntegral_sub_zeta_eq
    {N : Nat} [NeZero N] {x : Real} (hx : 3 <= x) :
    principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex) =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (characterChebyshevSum (Nat.floor t) (1 : DirichletCharacter Complex N) -
          characterChebyshevSum (Nat.floor t)
            (1 : DirichletCharacter Complex N).primitiveCharacter) *
              (Robin1984.robinRealWeight 1 t : Complex)) := by
  have hDifference := integrableOn_imprimitiveChebyshevStep_mul_weight
    (1 : DirichletCharacter Complex N) hx
  have hRational : IntegrableOn (fun t : Real =>
      (((Chebyshev.psi t - t) * Robin1984.robinRealWeight 1 t : Real) : Complex)) (Ioi x) :=
    (integrableOn_quadraticRationalWeightedError_one (x := x) (by linarith : 2 <= x)).ofReal
  have hRationalIntegral : integral (volume.restrict (Ioi x)) (fun t : Real =>
      (((Chebyshev.psi t - t) * Robin1984.robinRealWeight 1 t : Real) : Complex)) =
        (Robin1984.nicolasJ x : Complex) := by
    rw [integral_complex_ofReal]
    congr 1
    exact riemannWeightedErrorIntegral_eq_nicolasJ (by linarith : 1 <= x)
  have hSum : principalCenteredWeightedIntegral N x =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (characterChebyshevSum (Nat.floor t) (1 : DirichletCharacter Complex N) -
          characterChebyshevSum (Nat.floor t)
            (1 : DirichletCharacter Complex N).primitiveCharacter) *
              (Robin1984.robinRealWeight 1 t : Complex)) + (Robin1984.nicolasJ x : Complex) := by
    unfold principalCenteredWeightedIntegral
    rw [<- hRationalIntegral, <- integral_add hDifference hRational]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [characterChebyshevSum_primitive_principal_eq_psi]
    push_cast
    ring
  rw [hSum]
  ring

/-- Exact finite logarithmic-floor expression for the full principal
Chebyshev correction. All admitted powers of every excluded prime remain. -/
theorem principalChebyshevStep_sub_primitive_eq_logFloorSum
    {N : Nat} [NeZero N] (t : Real) :
    characterChebyshevSum (Nat.floor t) (1 : DirichletCharacter Complex N) -
      characterChebyshevSum (Nat.floor t) (1 : DirichletCharacter Complex N).primitiveCharacter =
      -((Finset.sum N.primeFactors (fun p =>
        Real.log p * (Nat.log p (Nat.floor t) : Real)) : Real) : Complex) := by
  rw [characterChebyshevSum_sub_primitive_eq_sum_primePowers]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hValue : (1 : DirichletCharacter Complex N).primitiveCharacter p = 1 := by
    rw [DirichletCharacter.primitiveCharacter_one]
    apply MulChar.one_apply
    have hConductor : (1 : DirichletCharacter Complex N).conductor = 1 :=
      DirichletCharacter.conductor_one
    rw [hConductor]
    exact isUnit_of_subsingleton _
  simp [hValue, Nat.card_Icc]

/-- The complete principal endpoint correction is the negative real integral
of its full finite logarithmic-floor sum. -/
theorem principalCenteredWeightedIntegral_sub_zeta_eq_logFloorIntegral
    {N : Nat} [NeZero N] {x : Real} (hx : 3 <= x) :
    principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex) =
      -((integral (volume.restrict (Ioi x)) (fun t : Real =>
        Finset.sum N.primeFactors (fun p => Real.log p * (Nat.log p (Nat.floor t) : Real)) *
          Robin1984.robinRealWeight 1 t) : Real) : Complex) := by
  rw [principalCenteredWeightedIntegral_sub_zeta_eq hx]
  simp_rw [principalChebyshevStep_sub_primitive_eq_logFloorSum, neg_mul, <- Complex.ofReal_mul]
  rw [integral_neg, integral_complex_ofReal]

/-- Explicit unconditional secondary term of the actual centered principal
tail. The coefficient is the number of distinct prime divisors of the
ambient modulus; the entire error constant is displayed. -/
theorem principalCenteredWeightedIntegral_sub_zeta_asymptotic
    {N : Nat} [NeZero N] {x : Real} (hx : 3 <= x) :
    norm (principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex) +
      (N.primeFactors.card : Complex) / (x : Complex)) <=
        (Finset.sum N.primeFactors (fun p => Real.log p) + (N.primeFactors.card : Real)) /
          (x * Real.log x) := by
  have hConstants := principalImprimitiveConstants (N := N)
  rw [principalCenteredWeightedIntegral_sub_zeta_eq hx, <- hConstants.1, <- hConstants.2]
  exact norm_integral_imprimitiveChebyshevStep_add_resonance_div_le
    (1 : DirichletCharacter Complex N) hx

end

end RobinBV.NumberField
