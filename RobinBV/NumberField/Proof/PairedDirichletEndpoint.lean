import RobinBV.NumberField.Proof.DirichletCharacterWeightedArithmetic
import RobinBV.NumberField.Proof.PairedDirichletEndpointZeros

/-!
# Exponent-one explicit formula for a paired Dirichlet character

The formula combines the actual weighted arithmetic integral, the full
multiplicity-counted zero sum, and the canonical parity-dependent correction.
Siegel-Walfisz supplies endpoint integrability unconditionally. ERH is used
only for the zero-kernel estimates and the explicit-formula zero mass.

The correction is retained as an exact endpoint reweighting of its completely
specified exponent-two expression; no lower-order estimate is assumed here.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

/-- Weighted arithmetic integral for a character and its dual. -/
def pairedDirichletWeightedIntegral
    {N : Nat} (chi : DirichletCharacter Complex N) (n : Nat) (x : Real) : Complex :=
  dirichletCharacterWeightedIntegral chi n x +
    dirichletCharacterWeightedIntegral (Inv.inv chi) n x

/-- Exact even-parity correction for the dual pair, with single-character
inverse-square zero mass Z. -/
def pairedDirichletEvenWeightedRemainder
    (N : Nat) (Z : Real) (n : Nat) (x : Real) : Complex :=
  ((Real.log N + Z - Real.eulerMascheroniConstant - Real.log Real.pi : Real) : Complex) *
      Robin1984.robinCutoffMellinTest n x 1 +
    2 * tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n (-(2 * ((k : Complex) + 1))) x /
        (2 * ((k : Complex) + 1))) -
    2 * quadraticCharacterEvenOriginCorrection n x

/-- Exact odd-parity correction for the dual pair. -/
def pairedDirichletOddWeightedRemainder
    (N : Nat) (Z : Real) (n : Nat) (x : Real) : Complex :=
  ((Real.log N + Z - Real.eulerMascheroniConstant - Real.log Real.pi : Real) : Complex) *
      Robin1984.robinCutoffMellinTest n x 1 +
    2 * quadraticOddGammaConstant * Robin1984.robinCutoffMellinTest n x 1 +
    2 * tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1))

/-- Complete endpoint transfer of an explicitly given exponent-two correction. -/
def dirichletEndpointCorrection (R : Real -> Complex) (x : Real) : Complex :=
  (Robin1984.robinEndpointReweight x : Complex) * R x +
    integral (volume.restrict (Ioi x)) (fun t : Real =>
      (Robin1984.robinEndpointReweightDerivative t : Complex) * R t)

/-- The paired cutoff series agrees with the paired arithmetic integral. -/
theorem pairedDirichletPrimePowerSum_eq_weightedIntegral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    pairedDirichletPrimePowerSum chi n x = pairedDirichletWeightedIntegral chi n x := by
  rw [pairedDirichletPrimePowerSum, pairedDirichletWeightedIntegral,
    primitiveCharacterPrimePowerSum_eq_weightedIntegral chi hn hx,
    primitiveCharacterPrimePowerSum_eq_weightedIntegral (Inv.inv chi) hn hx]

/-- The full paired arithmetic integral satisfies the exact endpoint transfer. -/
theorem pairedDirichletWeightedIntegral_one_reweight
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) {x : Real} (hx : 3 <= x) :
    And
      (IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          pairedDirichletWeightedIntegral chi 2 t) (Ioi x))
      (pairedDirichletWeightedIntegral chi 1 x =
        (Robin1984.robinEndpointReweight x : Complex) *
          pairedDirichletWeightedIntegral chi 2 x +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Robin1984.robinEndpointReweightDerivative t : Complex) *
            pairedDirichletWeightedIntegral chi 2 t)) := by
  have hi := BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hLeft := dirichletCharacterWeightedIntegral_one_reweight chi hchi hx
  have hRight := dirichletCharacterWeightedIntegral_one_reweight (Inv.inv chi) hi hx
  have hInt : IntegrableOn (fun t : Real =>
      (Robin1984.robinEndpointReweightDerivative t : Complex) *
        pairedDirichletWeightedIntegral chi 2 t) (Ioi x) := by
    simpa only [pairedDirichletWeightedIntegral, mul_add, Pi.add_apply] using!
      hLeft.1.add hRight.1
  refine And.intro hInt ?_
  rw [pairedDirichletWeightedIntegral, hLeft.2, hRight.2]
  simp only [pairedDirichletWeightedIntegral, mul_add]
  rw [integral_add hLeft.1 hRight.1]
  ring

/-- Reweight an established exponent-two formula. This transfer lemma also
proves integrability of the complete correction instead of assuming it. -/
theorem pairedDirichletWeightedIntegral_one_eq_zero_sum_of_two_formula
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) (R : Real -> Complex)
    (hFormula : forall t : Real, 3 <= t ->
      pairedDirichletWeightedIntegral chi 2 t =
        -tsum (fun p : PairedDirichletZeroIndex chi =>
          Robin1984.robinZeroKernel 2 (pairedDirichletZeroValue p) t /
            pairedDirichletZeroValue p) + R t)
    {x : Real} (hx : 3 <= x) :
    And
      (IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) * R t) (Ioi x))
      (pairedDirichletWeightedIntegral chi 1 x =
        -tsum (fun p : PairedDirichletZeroIndex chi =>
          Robin1984.robinZeroKernel 1 (pairedDirichletZeroValue p) x /
            pairedDirichletZeroValue p) + dirichletEndpointCorrection R x) := by
  have hArithmetic := pairedDirichletWeightedIntegral_one_reweight hchi hx
  have hZeros := pairedDirichlet_complete_zero_sum_one_reweight
    hchi hPrimitive hERH (by linarith : 1 < x)
  have hCorrection : IntegrableOn (fun t : Real =>
      (Robin1984.robinEndpointReweightDerivative t : Complex) * R t) (Ioi x) := by
    apply (hArithmetic.1.add hZeros.1).congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.add_apply]
    rw [hFormula t (hx.trans ht.le)]
    ring
  have hIntegral :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) * R t) =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          pairedDirichletWeightedIntegral chi 2 t) +
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          tsum (fun p : PairedDirichletZeroIndex chi =>
            Robin1984.robinZeroKernel 2 (pairedDirichletZeroValue p) t /
              pairedDirichletZeroValue p)) := by
    rw [<- integral_add hArithmetic.1 hZeros.1]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [Pi.add_apply]
    rw [hFormula t (hx.trans ht.le)]
    ring
  refine And.intro hCorrection ?_
  rw [dirichletEndpointCorrection, hIntegral, hArithmetic.2, hZeros.2, hFormula x hx]
  ring

/-- Full exponent-one paired formula for an even primitive character.
All conductor, zero-mass, trivial-zero, and origin terms are retained. -/
theorem pairedDirichletWeightedIntegral_one_eq_even_explicit
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hEven : DirichletCharacter.Even chi) (hERH : DirichletERH chi)
    {x : Real} (hx : 3 <= x) :
    And
      (IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          pairedDirichletEvenWeightedRemainder N (quadraticLZeroMass chi) 2 t) (Ioi x))
      (pairedDirichletWeightedIntegral chi 1 x =
        -tsum (fun p : PairedDirichletZeroIndex chi =>
          Robin1984.robinZeroKernel 1 (pairedDirichletZeroValue p) x /
            pairedDirichletZeroValue p) +
          dirichletEndpointCorrection
            (pairedDirichletEvenWeightedRemainder N (quadraticLZeroMass chi) 2) x) := by
  apply pairedDirichletWeightedIntegral_one_eq_zero_sum_of_two_formula
    hchi hPrimitive hERH _ _ hx
  intro t ht
  rw [<- pairedDirichletPrimePowerSum_eq_weightedIntegral chi
    (by norm_num : 2 <= 2) (by linarith : 1 < t)]
  have hFormula := pairedDirichletPrimePowerSum_eq_even_explicit hchi hPrimitive hEven hERH
    (n := 2) (by norm_num) (x := t) (by linarith)
  simpa only [pairedDirichletEvenWeightedRemainder, sub_eq_add_neg, add_assoc] using hFormula

/-- Full exponent-one paired formula for an odd primitive character,
including its different archimedean constant and odd trivial-zero sequence. -/
theorem pairedDirichletWeightedIntegral_one_eq_odd_explicit
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hOdd : DirichletCharacter.Odd chi) (hERH : DirichletERH chi)
    {x : Real} (hx : 3 <= x) :
    And
      (IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          pairedDirichletOddWeightedRemainder N (quadraticLZeroMass chi) 2 t) (Ioi x))
      (pairedDirichletWeightedIntegral chi 1 x =
        -tsum (fun p : PairedDirichletZeroIndex chi =>
          Robin1984.robinZeroKernel 1 (pairedDirichletZeroValue p) x /
            pairedDirichletZeroValue p) +
          dirichletEndpointCorrection
            (pairedDirichletOddWeightedRemainder N (quadraticLZeroMass chi) 2) x) := by
  apply pairedDirichletWeightedIntegral_one_eq_zero_sum_of_two_formula
    hchi hPrimitive hERH _ _ hx
  intro t ht
  rw [<- pairedDirichletPrimePowerSum_eq_weightedIntegral chi
    (by norm_num : 2 <= 2) (by linarith : 1 < t)]
  have hFormula := pairedDirichletPrimePowerSum_eq_odd_explicit hchi hPrimitive hOdd hERH
    (n := 2) (by norm_num) (x := t) (by linarith)
  simpa only [pairedDirichletOddWeightedRemainder, add_assoc] using hFormula

end

end RobinBV.NumberField
