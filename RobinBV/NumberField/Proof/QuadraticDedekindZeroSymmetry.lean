import RobinBV.NumberField.Proof.QuadraticDedekindERH
import RobinBV.NumberField.Proof.QuadraticLZeroSymmetry

/-!
# Off-critical zeros of quadratic Dedekind zeta

Failure of the Riemann hypothesis supplies a right-half-strip Riemann-zeta
zero by reflection. Failure of the quadratic Dirichlet ERH supplies a
right-half-strip completed L-zero by quadratic symmetry. The canonical
Dedekind-zeta factorization combines these alternatives into an actual zero
of the continued quadratic Dedekind zeta strictly right of the critical line.
-/

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex

noncomputable section

theorem exists_quadraticDedekindZeta_zero_re_gt_half_of_not_RH
    (D : NumberField.OddFundamentalDiscriminant)
    (hNotRH : Not RiemannHypothesis) :
    Exists fun rho : Complex =>
      And (quadraticDedekindZetaContinuation D rho = 0)
        (And (1 / 2 < rho.re) (rho.re < 1)) := by
  unfold RiemannHypothesis at hNotRH
  push Not at hNotRH
  choose rho hZeta hNontrivial hOne hOffLine using hNotRH
  have hLt : rho.re < 1 := by
    by_contra hNotLt
    exact riemannZeta_ne_zero_of_one_le_re
      (le_of_not_gt hNotLt) hZeta
  have hMirrorZero : riemannZeta (1 - rho) = 0 :=
    riemannZeta_one_sub_eq_zero_of_nontrivial_zero
      hZeta (by
        intro hExists
        choose n hn using hExists
        exact hNontrivial n hn) hOne
  have hPos : 0 < rho.re := by
    by_contra hNotPos
    have hMirrorRe : 1 <= (1 - rho).re := by
      change 1 <= 1 - rho.re
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hMirrorRe hMirrorZero
  by_cases hRight : 1 / 2 < rho.re
  next =>
    apply Exists.intro rho
    apply And.intro
    next =>
      unfold quadraticDedekindZetaContinuation
      rw [hZeta, zero_mul]
    next => exact And.intro hRight hLt
  next =>
    have hLeft : rho.re < 1 / 2 :=
      lt_of_le_of_ne (le_of_not_gt hRight) hOffLine
    apply Exists.intro (1 - rho)
    apply And.intro
    next =>
      unfold quadraticDedekindZetaContinuation
      rw [hMirrorZero, zero_mul]
    next =>
      apply And.intro
      next =>
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      next =>
        simp only [Complex.sub_re, Complex.one_re]
        linarith

theorem exists_quadraticDedekindZeta_zero_re_gt_half_of_not_ERH
    (D : NumberField.OddFundamentalDiscriminant)
    (hNotERH : Not (QuadraticDedekindZetaERH D)) :
    Exists fun rho : Complex =>
      And (quadraticDedekindZetaContinuation D rho = 0)
        (And (1 / 2 < rho.re) (rho.re < 1)) := by
  have hNotFactors :
      Not (And RiemannHypothesis (DirichletERH D.character)) := by
    intro hFactors
    exact hNotERH ((quadraticDedekindZetaERH_iff D).2 hFactors)
  by_cases hRH : RiemannHypothesis
  next =>
    have hNotL : Not (DirichletERH D.character) := by
      intro hL
      exact hNotFactors (And.intro hRH hL)
    choose rho hZero hRight using
      exists_nontrivialCompletedLZero_re_gt_half_of_not_dirichletERH
        D.character_isPrimitive D.character_isQuadratic hNotL
    have hSymmetric :
        symmetricCompletedLFunction D.character rho = 0 := by
      rw [symmetricCompletedLFunction, hZero.1, mul_zero]
    have hCarrier : quadraticDedekindZeroCarrier D rho = 0 :=
      (quadraticDedekindZeroCarrier_eq_zero_iff D rho).2
        (Or.inr hSymmetric)
    have hContinuation : quadraticDedekindZetaContinuation D rho = 0 :=
      (quadraticDedekindZeroCarrier_eq_zero_iff_continuation_eq_zero
        D hZero.2.1 hZero.2.2).1 hCarrier
    exact Exists.intro rho
      (And.intro hContinuation (And.intro hRight hZero.2.2))
  next =>
    exact exists_quadraticDedekindZeta_zero_re_gt_half_of_not_RH D hRH

theorem not_quadraticDedekindZetaERH_iff_exists_zero_re_gt_half
    (D : NumberField.OddFundamentalDiscriminant) :
    Not (QuadraticDedekindZetaERH D) <->
      Exists fun rho : Complex =>
        And (quadraticDedekindZetaContinuation D rho = 0)
          (And (1 / 2 < rho.re) (rho.re < 1)) := by
  constructor
  next =>
    exact exists_quadraticDedekindZeta_zero_re_gt_half_of_not_ERH D
  next =>
    intro hExists hERH
    choose rho hZero hRight hLt using hExists
    have hPos : 0 < rho.re := by linarith
    have hCritical := hERH rho hZero hPos hLt
    linarith

end

end RobinBV.NumberField
