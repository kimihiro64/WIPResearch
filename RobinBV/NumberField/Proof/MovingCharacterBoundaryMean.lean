import RobinBV.Mathlib.Analysis.SpecificLimits.IntervalMean
import RobinBV.NumberField.Proof.MovingCharacterBoundaryZeros
import RobinBV.NumberField.Proof.ZeroSeriesLogarithmicMean

/-!
# Logarithmic mean of the actual doubled-boundary arithmetic residual

Keep every exact finite prime moment and principal-power model integral.
The arithmetic-to-zero error is averaged from its proved convergence,
without imposing a rate or replacing the actual integrals by a model.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set

noncomputable section

/-- Fully normalized actual centered boundary residual, with its finite
prime-moment prefix and all earlier principal models retained exactly. -/
def centeredCharacterBoundaryResidual {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (m P : Nat) : Complex := by
  classical
  exact ((((P : Real) ^ ((m : Real) * (((2 * (m + 1) : Nat) : Real) - 1) /
      ((2 * (m + 1) : Nat) : Real)) * Real.log P : Real) : Complex) *
      (centeredCharacterWeightedIntegral
        (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) ((P : Real) ^ m) -
          centeredCharacterWeightedIntegral chi ((P : Real) ^ m) +
        Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
          Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
            ((((P : Real) ^ m : Real) : Complex) * (m : Complex) * (Real.log P : Complex)) +
        Finset.sum (Finset.Ico (m + 1) (2 * (m + 1))) (fun j =>
          (if chi ^ j = 1 then (1 : Complex) else 0) *
            ((integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
              t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex))))

/-- The complete actual arithmetic-to-zero error has vanishing logarithmic
mean. Convergence supplies its boundedness; no uniform error rate is assumed. -/
theorem centeredCharacterBoundaryResidual_zeroSeries_mean_error_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t)) -
        boundaryCharacterZeroSeries chi m (Nat.floor (Real.exp t)))) atTop (nhds (0 : Complex)) := by
  apply Complex.tendsto_intervalMean_nat_floor_exp
    (fun P : Nat => centeredCharacterBoundaryResidual chi m P-boundaryCharacterZeroSeries chi m P)
  simpa only [centeredCharacterBoundaryResidual] using
    centeredCharacter_boundary_zero_expansion_of_ERH chi m hm hPowersERH

/-- Exact mean of the canonical boundary zero series. Only ERH of its
selected first character power is needed for this spectral statement. -/
theorem boundaryCharacterZeroSeries_logMean_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hFirstERH : DirichletERH (chi^(m+1))) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      boundaryCharacterZeroSeries chi m (Nat.floor (Real.exp t)))) atTop
      (nhds ((2*((m+1 : Nat) : Complex)/
        ((m : Complex)*(((m+1 : Nat) : Complex)-1/2)))*
          (rootCharacterCentralMultiplicity (chi^(m+1)) : Complex))) := by
  have h := (rootCharacterZeroSeries_power_logFloorMean_tendsto
    (chi^(m+1)) hFirstERH (by omega : 2 <= m+1) m hm).div_const (m : Complex)
  have hConstant :
      ((2*((m+1 : Nat) : Complex)/(((m+1 : Nat) : Complex)-1/2))*
        (rootCharacterCentralMultiplicity (chi^(m+1)) : Complex))/(m : Complex) =
      (2*((m+1 : Nat) : Complex)/((m : Complex)*(((m+1 : Nat) : Complex)-1/2)))*
        (rootCharacterCentralMultiplicity (chi^(m+1)) : Complex) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hConstant] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro T
  have hFunction : (fun t : Real => boundaryCharacterZeroSeries chi m (Nat.floor (Real.exp t))) =
      (fun t : Real => rootCharacterZeroSeries (chi^(m+1)) (m+1)
        ((Nat.floor (Real.exp t) : Real)^m)/(m : Complex)) := by
    funext t
    exact (rootCharacterZeroSeries_power_cutoff_div_eq chi m (Nat.floor (Real.exp t))).symm
  dsimp only
  unfold Complex.intervalMean
  rw [hFunction, intervalIntegral.integral_div]
  ring

/-- The actual fully centered arithmetic boundary residual has logarithmic
mean 2(m+1)/(m(m+1/2)) times the canonical central multiplicity of chi^(m+1).
All finite prime moments, principal models and arithmetic corrections remain. -/
theorem centeredCharacter_boundary_logMean_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t)))) atTop
      (nhds ((2*((m+1 : Nat) : Complex)/
        ((m : Complex)*(((m+1 : Nat) : Complex)-1/2)))*
          (rootCharacterCentralMultiplicity (chi^(m+1)) : Complex))) := by
  have hError := centeredCharacterBoundaryResidual_zeroSeries_mean_error_tendsto chi m hm hPowersERH
  have hSeries := boundaryCharacterZeroSeries_logMean_tendsto chi m hm
    (hPowersERH (m+1) le_rfl (by omega))
  have h := hError.add hSeries
  simp only [zero_add] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro T
  dsimp only
  rw [Complex.intervalMean_nat_floor_exp_sub]
  ring

end

end RobinBV.NumberField
