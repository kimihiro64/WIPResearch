import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorRegularity
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionFactorNonvanishing
import Robin1984.NicolasLandau.NicolasLandau
import RobinBV.NumberField.Definitions.QuadraticLZeros

/-!
# Principal characters and the Riemann hypothesis

The finite Euler factors removed from zeta are nonzero throughout the open
critical strip. This identifies every completed principal-character strip
zero with an actual zeta zero and proves the principal ERH assertion equivalent
to Mathlib's full Riemann hypothesis, including its nontrivial-zero convention.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex

noncomputable section

/-- At every positive modulus, the completed principal-character strip zeros
are exactly the zeta zeros in that strip. -/
theorem isNontrivialCompletedLZero_principal_iff
    {N : Nat} [NeZero N] (rho : Complex) :
    IsNontrivialCompletedLZero (1 : DirichletCharacter Complex N) rho <->
      And (riemannZeta rho = 0) (And (0 < rho.re) (rho.re < 1)) := by
  by_cases hStrip : And (0 < rho.re) (rho.re < 1)
  case neg =>
    simp only [IsNontrivialCompletedLZero, hStrip, and_false]
  case pos =>
    have hRhoZero : Not (rho = 0) := by
      intro hEq
      have hPos := hStrip.1
      rw [hEq] at hPos
      norm_num at hPos
    have hRhoOne : Not (rho = 1) := by
      intro hEq
      have hLt := hStrip.2
      rw [hEq] at hLt
      norm_num at hLt
    have hProduct : Not ((Finset.prod N.primeFactors
        (fun p => (1 : Complex) - (p : Complex) ^ (-rho))) = 0) := by
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      have hNorm := BombieriVinogradov.SiegelWalfisz.norm_prime_cpow_lt_one_of_re_pos
        (Nat.prime_of_mem_primeFactors hp) hStrip.1
      apply sub_ne_zero.mpr
      intro hEq
      rw [<- hEq] at hNorm
      norm_num at hNorm
    have hOrdinary : (1 : DirichletCharacter Complex N).LFunction rho = 0 <->
        riemannZeta rho = 0 := by
      have hFactor : (1 : DirichletCharacter Complex N).LFunction rho =
          (Finset.prod N.primeFactors (fun p => (1 : Complex) - (p : Complex) ^ (-rho))) *
            riemannZeta rho :=
        DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := N) hRhoOne
      rw [hFactor, mul_eq_zero]
      simp only [hProduct, false_or]
    have hGamma := BombieriVinogradov.SiegelWalfisz.DirichletCharacter.gammaFactor_ne_zero_of_re_pos
      (1 : DirichletCharacter Complex N) hStrip.1
    have hCompleted : (1 : DirichletCharacter Complex N).completedLFunction rho = 0 <->
        riemannZeta rho = 0 := by
      simpa only [DirichletCharacter.LFunction_eq_completed_div_gammaFactor
        (1 : DirichletCharacter Complex N) rho (Or.inl hRhoZero),
        div_eq_zero_iff, hGamma, or_false] using hOrdinary
    exact and_congr hCompleted Iff.rfl

/-- The principal-character critical-line assertion at any positive modulus
is exactly the full Riemann hypothesis. -/
theorem dirichletERH_principal_iff_riemannHypothesis
    {N : Nat} [NeZero N] :
    DirichletERH (1 : DirichletCharacter Complex N) <-> RiemannHypothesis := by
  constructor
  next =>
    intro hERH
    by_contra hNotRH
    choose rho hZero hHalf hOne using
      Robin1984.exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
    have hPos : 0 < rho.re := by linarith
    have hCompleted := (isNontrivialCompletedLZero_principal_iff (N := N) rho).2
      (And.intro hZero (And.intro hPos hOne))
    have hLine := hERH rho hCompleted
    linarith
  next =>
    intro hRH rho hCompleted
    have hData := (isNontrivialCompletedLZero_principal_iff (N := N) rho).1 hCompleted
    have hNontrivial : Not (Exists fun n : Nat => rho = -2 * (n + 1)) := by
      intro hExists
      choose n hn using hExists
      have hRe := congrArg Complex.re hn
      norm_num at hRe
      have hnNonneg : 0 <= (n : Real) := Nat.cast_nonneg n
      linarith [hData.2.1]
    have hRhoOne : Not (rho = 1) := by
      intro hEq
      have hLt := hData.2.2
      rw [hEq] at hLt
      norm_num at hLt
    exact hRH rho hData.1 hNontrivial hRhoOne

end

end RobinBV.NumberField
