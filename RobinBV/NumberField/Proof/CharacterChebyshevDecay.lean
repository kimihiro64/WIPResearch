import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.PrimitiveAtLeastTwo
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.FaithfulChoice
import RobinBV.NumberField.Proof.CharacterZeroSumDecay

/-!
# Primitive character sums with explicit zero-free damping

One positive zero-free constant and one positive remainder constant work
for every primitive nonprincipal character. The finite inverse-square mass
may depend on the character. The exceptional contribution is kept visible;
its eventual absorption and the logarithmic height choice are separate steps.

The primitive explicit formula is reused from BV commit
310dcff4efc8109814e6cbeab093465262d5d1c5 (Apache-2.0).
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_characterChebyshevSum_zeroFree_bound :
    exists c : Real, And (0 < c) (exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        3 <= N -> Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
        exists e : Option Complex, And (IsExceptionalZeroChoice c chi e)
          (forall {x : Nat}, 2 <= x -> forall {T : Real}, 2 <= T -> T <= x ->
            norm (characterChebyshevSum x chi) <=
              (x : Real) ^ (1 - c / (Real.log N + Real.log (T + 2))) *
                ((T + 1) * tsum (fun p : SymmetricCompletedZeroIndex chi =>
                  (1 / norm (symmetricCompletedZeroValue p)) ^ 2)) +
              norm (exceptionalZeroContribution x e) +
              C * explicitFormulaRemainderMajorant N x T))) := by
  have hWitness := exists_primitiveExplicitFormula_at_least_two
  let c := hWitness.choose
  have hc : 0 < c := hWitness.choose_spec.1
  have hData : forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
      3 <= N -> Ne chi 1 -> ExplicitFormulaZeroFreeData c chi :=
    hWitness.choose_spec.2.1
  choose C hC hFormula using hWitness.choose_spec.2.2
  refine Exists.intro c (And.intro hc (Exists.intro C (And.intro hC ?_)))
  intro N inst chi hN hchi hPrimitive
  have hChoiceExists := exists_faithfulExceptionalChoice c chi
  let e := hChoiceExists.choose
  have hChoice : IsExceptionalZeroChoice c chi e := hChoiceExists.choose_spec
  refine Exists.intro e (And.intro hChoice ?_)
  intro x hx T hT hTx
  have hError := hFormula hN hchi hPrimitive hx hT hTx e hChoice
  have hZeros := norm_truncatedCriticalZeroSum_le_zeroFree_mass
    hN hchi hPrimitive hc (hData chi hN hchi) hChoice
    (show 1 <= x by omega) (show 0 <= T by linarith)
  have hTriangle : norm (characterChebyshevSum x chi) <=
      norm (characterChebyshevSum x chi + truncatedCriticalZeroSum chi x T e +
        exceptionalZeroContribution x e) + norm (truncatedCriticalZeroSum chi x T e) +
        norm (exceptionalZeroContribution x e) := by
    let a := characterChebyshevSum x chi
    let b := truncatedCriticalZeroSum chi x T e
    let d := exceptionalZeroContribution x e
    change norm a <= norm (a + b + d) + norm b + norm d
    calc
      norm a = norm ((a + b + d) - b - d) := by congr 1; ring
      _ <= norm ((a + b + d) - b) + norm d := norm_sub_le _ _
      _ <= (norm (a + b + d) + norm b) + norm d := by
        linarith only [norm_sub_le (a + b + d) b]
  linarith

end RobinBV.NumberField
