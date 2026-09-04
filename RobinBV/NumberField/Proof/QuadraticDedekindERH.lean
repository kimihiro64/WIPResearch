import RobinBV.NumberField.Definitions.QuadraticLZeros
import RobinBV.NumberField.Proof.QuadraticDedekindZetaZeros

/-!
# Quadratic Dedekind ERH and its two factors

This module identifies ERH for the canonical quadratic Dedekind continuation
with RH for zeta and ERH for the primitive quadratic Dirichlet L-function.
-/

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex
open DirichletCharacter

noncomputable section

/-- Extended RH for the entire quadratic Dedekind zero carrier. -/
def QuadraticDedekindERH
    (D : NumberField.OddFundamentalDiscriminant) : Prop :=
  forall rho : Complex,
    quadraticDedekindZeroCarrier D rho = 0 ->
      0 < rho.re -> rho.re < 1 -> rho.re = 1 / 2

/-- Extended RH stated directly for the canonical continued quadratic
Dedekind zeta. -/
def QuadraticDedekindZetaERH
    (D : NumberField.OddFundamentalDiscriminant) : Prop :=
  forall rho : Complex,
    quadraticDedekindZetaContinuation D rho = 0 ->
      0 < rho.re -> rho.re < 1 -> rho.re = 1 / 2

theorem quadraticDedekindZetaERH_iff_carrierERH
    (D : NumberField.OddFundamentalDiscriminant) :
    QuadraticDedekindZetaERH D <-> QuadraticDedekindERH D := by
  constructor
  next =>
    intro hZeta rho hCarrier hPos hLt
    have hContinuation :=
      (quadraticDedekindZeroCarrier_eq_zero_iff_continuation_eq_zero
        D hPos hLt).1 hCarrier
    exact hZeta rho hContinuation hPos hLt
  next =>
    intro hCarrier rho hContinuation hPos hLt
    have hCarrierZero :=
      (quadraticDedekindZeroCarrier_eq_zero_iff_continuation_eq_zero
        D hPos hLt).2 hContinuation
    exact hCarrier rho hCarrierZero hPos hLt

theorem riemannZeta_one_sub_eq_zero_of_nontrivial_zero
    {s : Complex} (hZeta : riemannZeta s = 0)
    (hNontrivial : Not (Exists fun n : Nat => s = -2 * (n + 1)))
    (hOne : Not (s = 1)) :
    riemannZeta (1 - s) = 0 := by
  have hZero : Not (s = 0) := by
    intro hEq
    subst s
    norm_num [riemannZeta_zero] at hZeta
  have hCompleted : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hZero] at hZeta
    have hCases := div_eq_zero_iff.mp hZeta
    cases hCases with
    | inl hCompleted => exact hCompleted
    | inr hGammaFactor =>
      change
        (Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2) = 0
          at hGammaFactor
      have hProductCases := mul_eq_zero.mp hGammaFactor
      cases hProductCases with
      | inl hPiPower =>
        have hPi : Not ((Real.pi : Complex) = 0) :=
          Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact
          (Complex.cpow_ne_zero_iff.mpr (Or.inl hPi) hPiPower).elim
      | inr hGamma =>
        choose m hm using (Complex.Gamma_eq_zero_iff (s / 2)).mp hGamma
        have hsEq : s = -2 * (m : Complex) := by
          calc
            s = 2 * (s / 2) := by ring
            _ = 2 * (-(m : Complex)) := by rw [hm]
            _ = -2 * (m : Complex) := by ring
        cases m with
        | zero => exact (hZero (by simpa using hsEq)).elim
        | succ n =>
          exact (hNontrivial (Exists.intro n (by
            simpa [Nat.cast_add, Nat.cast_one] using hsEq))).elim
  have hMirrorCompleted : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hCompleted
  have hMirrorNonzero : Not (1 - s = 0) :=
    sub_ne_zero.mpr (Ne.symm hOne)
  rw [riemannZeta_def_of_ne_zero hMirrorNonzero,
    hMirrorCompleted, zero_div]

theorem quadraticDedekindERH_iff
    (D : NumberField.OddFundamentalDiscriminant) :
    QuadraticDedekindERH D <->
      And RiemannHypothesis (DirichletERH D.character) := by
  constructor
  next =>
    intro hField
    apply And.intro
    next =>
      intro rho hZeta hNontrivial hOne
      have hLt : rho.re < 1 := by
        by_contra hNotLt
        exact riemannZeta_ne_zero_of_one_le_re
          (le_of_not_gt hNotLt) hZeta
      have hMirrorZero : riemannZeta (1 - rho) = 0 :=
        riemannZeta_one_sub_eq_zero_of_nontrivial_zero
          hZeta hNontrivial hOne
      have hPos : 0 < rho.re := by
        by_contra hNotPos
        have hMirrorRe : 1 <= (1 - rho).re := by
          change 1 <= 1 - rho.re
          linarith
        exact riemannZeta_ne_zero_of_one_le_re hMirrorRe hMirrorZero
      have hContinuation : quadraticDedekindZetaContinuation D rho = 0 := by
        unfold quadraticDedekindZetaContinuation
        rw [hZeta, zero_mul]
      have hCarrier : quadraticDedekindZeroCarrier D rho = 0 :=
        (quadraticDedekindZeroCarrier_eq_zero_iff_continuation_eq_zero
          D hPos hLt).2 hContinuation
      exact hField rho hCarrier hPos hLt
    next =>
      intro rho hZero
      have hSymmetric :
          symmetricCompletedLFunction D.character rho = 0 := by
        rw [symmetricCompletedLFunction, hZero.1, mul_zero]
      have hCarrier : quadraticDedekindZeroCarrier D rho = 0 :=
        (quadraticDedekindZeroCarrier_eq_zero_iff D rho).2
          (Or.inr hSymmetric)
      exact hField rho hCarrier hZero.2.1 hZero.2.2
  next =>
    intro hFactors rho hCarrier hPos hLt
    have hZeroFactors :=
      (quadraticDedekindZeroCarrier_eq_zero_iff D rho).1 hCarrier
    cases hZeroFactors with
    | inl hXi =>
      have hZeta : riemannZeta rho = 0 :=
        (riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
          hPos hLt).1 hXi
      have hNontrivial :
          Not (Exists fun n : Nat => rho = -2 * (n + 1)) := by
        intro hTrivial
        choose n hn using hTrivial
        rw [hn] at hPos
        norm_num at hPos
        have hFactorNonneg :
            (0 : Real) <= 2 * ((n : Real) + 1) := by
          positivity
        exact (not_lt_of_ge hFactorNonneg) hPos
      have hOne : Not (rho = 1) := by
        intro hEq
        rw [hEq] at hLt
        norm_num at hLt
      exact hFactors.1 rho hZeta hNontrivial hOne
    | inr hSymmetric =>
      have hN : Not ((D.modulus : Complex) = 0) := by
        exact_mod_cast NeZero.ne D.modulus
      have hPower :
          Not ((D.modulus : Complex) ^ (rho / 2) = 0) :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hN)
      rw [symmetricCompletedLFunction] at hSymmetric
      have hCompleted : completedLFunction D.character rho = 0 :=
        (mul_eq_zero.mp hSymmetric).resolve_left hPower
      exact hFactors.2 rho
        (And.intro hCompleted (And.intro hPos hLt))

theorem quadraticDedekindZetaERH_iff
    (D : NumberField.OddFundamentalDiscriminant) :
    QuadraticDedekindZetaERH D <->
      And RiemannHypothesis (DirichletERH D.character) := by
  exact (quadraticDedekindZetaERH_iff_carrierERH D).trans
    (quadraticDedekindERH_iff D)

end

end RobinBV.NumberField
