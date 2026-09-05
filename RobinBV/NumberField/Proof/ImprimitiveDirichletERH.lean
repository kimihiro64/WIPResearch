import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorRegularity
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionEulerProduct
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionNonvanishing
import RobinBV.NumberField.Definitions.QuadraticLZeros

/-!
# Conductor invariance of the Dirichlet critical-line assertion

Every finite level-correction Euler factor is nonzero in the positive
half-plane. The completed critical-strip zero predicate is consequently
unchanged on passing to the inducing primitive character. No ERH assumption
is used to establish this exact equivalence.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex

noncomputable section

/-- The complete critical-strip zero predicate is invariant under induction
from the conductor, not just the location of some selected zeros. -/
theorem isNontrivialCompletedLZero_iff_primitive
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Not (chi = 1)) (rho : Complex) :
    IsNontrivialCompletedLZero chi rho <->
      IsNontrivialCompletedLZero chi.primitiveCharacter rho := by
  by_cases hStrip : And (0 < rho.re) (rho.re < 1)
  case neg =>
    simp only [IsNontrivialCompletedLZero, hStrip, and_false]
  case pos =>
    have hRho : Not (rho = 0) := by
      intro hEq
      have hPos := hStrip.1
      rw [hEq] at hPos
      norm_num at hPos
    have hGamma := BombieriVinogradov.SiegelWalfisz.DirichletCharacter.gammaFactor_ne_zero_of_re_pos
      chi hStrip.1
    have hPrimitiveGamma :=
      BombieriVinogradov.SiegelWalfisz.DirichletCharacter.gammaFactor_ne_zero_of_re_pos
        chi.primitiveCharacter hStrip.1
    have hLevel := BombieriVinogradov.SiegelWalfisz.levelCorrection_ne_zero_of_re_pos
      chi hStrip.1
    have hOrdinary : chi.LFunction rho = 0 <->
        chi.primitiveCharacter.LFunction rho = 0 := by
      rw [BombieriVinogradov.SiegelWalfisz.LFunction_eq_primitive_mul_levelCorrection
        chi hchi rho, mul_eq_zero]
      simp only [hLevel, or_false]
    have hCompleted : chi.completedLFunction rho = 0 <->
        chi.primitiveCharacter.completedLFunction rho = 0 := by
      simpa only [chi.LFunction_eq_completed_div_gammaFactor rho (Or.inl hRho),
        chi.primitiveCharacter.LFunction_eq_completed_div_gammaFactor rho (Or.inl hRho),
        div_eq_zero_iff, hGamma, hPrimitiveGamma, or_false] using hOrdinary
    exact and_congr hCompleted Iff.rfl

/-- Imprimitive characters introduce no additional ERH obligation: the
finite Euler correction has no zero in the open critical strip. -/
theorem dirichletERH_iff_primitive
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Not (chi = 1)) :
    DirichletERH chi <-> DirichletERH chi.primitiveCharacter := by
  constructor
  next =>
    intro hERH rho hZero
    exact hERH rho ((isNontrivialCompletedLZero_iff_primitive chi hchi rho).2 hZero)
  next =>
    intro hERH rho hZero
    exact hERH rho ((isNontrivialCompletedLZero_iff_primitive chi hchi rho).1 hZero)

end

end RobinBV.NumberField
