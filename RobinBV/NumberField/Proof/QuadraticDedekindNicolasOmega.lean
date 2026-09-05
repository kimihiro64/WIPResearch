import RobinBV.NumberField.Proof.QuadraticDedekindNicolasRealOmega

/-!
# Quadratic Dedekind Nicolas Omega-minus theorem

Focused infrastructure for the quadratic Dedekind Nicolas-Landau Omega theorem.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section
theorem exists_quadraticDedekindNicolasJ_omegaMinus_of_not_ERH
    (D : NumberField.OddFundamentalDiscriminant)
    (hNotERH : Not (QuadraticDedekindZetaERH D)) :
    Exists fun b : Real => And (0 < b) (And (b < 1 / 2)
      (Robin1984.AtTopOmegaMinus (quadraticDedekindNicolasJ D)
        (fun x : Real => x ^ (-b)))) := by
  by_cases hReal : Exists fun beta : Real =>
      And ((1 / 2 : Real) < beta) (And (beta < 1)
        (quadraticDedekindZetaContinuation D (beta : Complex) = 0))
  next =>
    choose beta hBetaHalf hBetaOne hZero using hReal
    choose rho hRhoZero hRhoHalf hRhoOne hRhoIm hRay using
      exists_rightmost_horizontal_quadraticDedekindZeta_zero
        D hZero hBetaHalf hBetaOne
    have hRhoReal : rho = (rho.re : Complex) := by
      apply Complex.ext
      next => simp
      next => simpa using hRhoIm
    have hZeroReal :
        quadraticDedekindZetaContinuation D (rho.re : Complex) = 0 := by
      rw [<- hRhoReal]
      exact hRhoZero
    have hRayReal : forall v : Real, 0 < v ->
        Not (quadraticDedekindZetaContinuation D
          ((rho.re : Complex) + (v : Complex)) = 0) := by
      intro v hv
      rw [<- hRhoReal]
      exact hRay v hv
    exact
      exists_quadraticDedekindNicolasJ_omegaMinus_of_real_rightmost_zero
        D hZeroReal hRhoHalf hRhoOne hRayReal
  next =>
    have hNoReal : QuadraticDedekindNoRealOffCriticalZero D := by
      intro beta hBetaHalf hBetaOne hZero
      apply hReal
      exact Exists.intro beta
        (And.intro hBetaHalf (And.intro hBetaOne hZero))
    exact
      exists_quadraticDedekindNicolasJ_omegaMinus_of_not_ERH_of_noReal
        D hNoReal hNotERH

end

end RobinBV.NumberField
