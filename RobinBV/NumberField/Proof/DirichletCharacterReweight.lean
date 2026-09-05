import Robin1984.NicolasLandau.WeightedEndpoint
import RobinBV.NumberField.Proof.QuadraticCharacterEndpoint

/-!
# Endpoint reweighting for complex Dirichlet characters

The exponent-one input is supplied unconditionally by Siegel-Walfisz.
The exponent-two input is dominated by the ordinary weighted Chebyshev
integral. Robin's exact reweighting therefore applies to every nonprincipal
complex character, not just real or quadratic characters.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set

noncomputable section

/-- The complete weighted complex character Chebyshev integral. -/
def dirichletCharacterWeightedIntegral
    {N : Nat} (chi : DirichletCharacter Complex N) (n : Nat) (x : Real) : Complex :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    characterChebyshevSum (Nat.floor t) chi * (Robin1984.robinRealWeight n t : Complex))

/-- Absolute domination proves integrability for every exponent at least two,
including principal and imprimitive characters. -/
theorem integrableOn_characterChebyshevStep_mul_weight
    {N : Nat} (chi : DirichletCharacter Complex N)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real =>
      characterChebyshevSum (Nat.floor t) chi *
        (Robin1984.robinRealWeight n t : Complex)) (Ioi x) := by
  have hBase : IntegrableOn (fun t : Real =>
      Chebyshev.psi t * Robin1984.robinRealWeight n t) (Ioi x) := by
    have hComplex := Robin1984.integrableOn_complex_psi_robinRealWeight hn hx
    have hReal := hComplex.re
    change IntegrableOn (fun t : Real =>
      ((Chebyshev.psi t * Robin1984.robinRealWeight n t : Real) : Complex).re)
        (Ioi x) at hReal
    simpa only [Complex.ofReal_re] using hReal
  have hStepMeasurable : Measurable
      (fun t : Real => characterChebyshevSum (Nat.floor t) chi) :=
    (measurable_of_countable (fun k : Nat => characterChebyshevSum k chi)).comp
      Nat.measurable_floor
  have hWeightMeasurable : Measurable (fun t : Real =>
      (Robin1984.robinRealWeight n t : Complex)) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  apply hBase.mono' (hStepMeasurable.mul hWeightMeasurable).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hWeightNonneg := Robin1984.robinRealWeight_nonneg (n := n) (lt_trans hx ht)
  dsimp only [Pi.mul_apply]
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hWeightNonneg]
  apply mul_le_mul_of_nonneg_right _ hWeightNonneg
  calc
    norm (characterChebyshevSum (Nat.floor t) chi) <=
        Chebyshev.psi (Nat.floor t) := norm_characterChebyshevSum_le_psi chi _
    _ = Chebyshev.psi t := (Chebyshev.psi_eq_psi_coe_floor t).symm

/-- Exact transfer from exponent two to exponent one, with integrability of
the entire reweighting term proved rather than assumed. -/
theorem dirichletCharacterWeightedIntegral_one_reweight
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hchi : Ne chi 1)
    {x : Real} (hx : 3 <= x) :
    And
      (IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          dirichletCharacterWeightedIntegral chi 2 t) (Ioi x))
      (dirichletCharacterWeightedIntegral chi 1 x =
        (Robin1984.robinEndpointReweight x : Complex) *
          dirichletCharacterWeightedIntegral chi 2 x +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Robin1984.robinEndpointReweightDerivative t : Complex) *
            dirichletCharacterWeightedIntegral chi 2 t)) := by
  have hxOne : 1 < x := by linarith
  have hOne := (integrableOn_characterChebyshevStep_mul_weight_one chi hchi).mono_set
    (Ioi_subset_Ioi hx)
  have hTwo := integrableOn_characterChebyshevStep_mul_weight chi (by norm_num : 2 <= 2) hxOne
  have hStepMeasurable : Measurable
      (fun t : Real => characterChebyshevSum (Nat.floor t) chi) :=
    (measurable_of_countable (fun k : Nat => characterChebyshevSum k chi)).comp
      Nat.measurable_floor
  exact Robin1984.robin_weighted_integral_reweight hxOne hStepMeasurable hOne hTwo

end

end RobinBV.NumberField
