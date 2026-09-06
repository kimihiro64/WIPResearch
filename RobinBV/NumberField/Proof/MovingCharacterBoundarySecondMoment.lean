import RobinBV.NumberField.Proof.MovingCharacterBoundaryMean
import RobinBV.NumberField.Proof.ZeroSeriesMomentMass

/-!
# Exact second moment of the actual arithmetic boundary residual

The complete equal-zero pair mass is divided by m squared. Arithmetic
error and boundedness are derived from the actual ERH providers.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory

noncomputable section

/-- Actual boundary zero-series boundedness, derived from the complete root
series rather than added as an arithmetic hypothesis. -/
theorem exists_boundaryCharacterZeroSeries_norm_bound
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hFirstERH : DirichletERH (chi^(m+1))) :
    exists C : Real, Filter.Eventually (fun P : Nat => norm (boundaryCharacterZeroSeries chi m P) <= C) atTop := by
  choose C hC using exists_rootCharacterZeroSeries_norm_bound (chi^(m+1)) hFirstERH
    (by omega : 2 <= m+1)
  refine Exists.intro (C/(m : Real)) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with P hP
  have hPR : (0 : Real) < P := by exact_mod_cast (by omega : 0 < P)
  rw [<- rootCharacterZeroSeries_power_cutoff_div_eq chi m P, norm_div, norm_natCast]
  exact div_le_div_of_nonneg_right (hC.2 ((P : Real)^m) (pow_pos hPR m)) (Nat.cast_nonneg m)

/-- Exact full second moment of the canonical boundary zero series.
Every repeated-zero cross term remains in the root mass. -/
theorem boundaryCharacterZeroSeries_secondMoment_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hFirstERH : DirichletERH (chi^(m+1))) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      boundaryCharacterZeroSeries chi m (Nat.floor (Real.exp t)) *
        star (boundaryCharacterZeroSeries chi m (Nat.floor (Real.exp t)))))
      atTop (nhds (rootCharacterZeroSecondMoment (chi^(m+1)) (m+1)/(m : Complex)^2)) := by
  have h := (rootCharacterZeroSeries_power_secondMoment_tendsto
    (chi^(m+1)) hFirstERH (by omega : 2 <= m+1) m hm).div_const ((m : Complex)^2)
  have hScale (z : Complex) : (z/(m : Complex))*star (z/(m : Complex)) =
      (z*star z)/(m : Complex)^2 := by
    simp [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro T
  have hFunction : (fun t : Real =>
      boundaryCharacterZeroSeries chi m (Nat.floor (Real.exp t)) *
        star (boundaryCharacterZeroSeries chi m (Nat.floor (Real.exp t)))) =
      (fun t : Real => (rootCharacterZeroSeries (chi^(m+1)) (m+1) ((Nat.floor (Real.exp t) : Real)^m) *
        star (rootCharacterZeroSeries (chi^(m+1)) (m+1) ((Nat.floor (Real.exp t) : Real)^m))) /
          (m : Complex)^2) := by
    funext t
    rw [<- rootCharacterZeroSeries_power_cutoff_div_eq chi m (Nat.floor (Real.exp t)), hScale]
  dsimp only
  unfold Complex.intervalMean
  rw [hFunction, intervalIntegral.integral_div]
  ring

/-- The squared arithmetic-to-zero error tends to zero, using the actual
complete-series bound and the already proved additive error expansion. -/
theorem centeredCharacterBoundaryResidual_secondMoment_error_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    Tendsto (fun P : Nat =>
      centeredCharacterBoundaryResidual chi m P * star (centeredCharacterBoundaryResidual chi m P) -
        boundaryCharacterZeroSeries chi m P * star (boundaryCharacterZeroSeries chi m P))
      atTop (nhds (0 : Complex)) := by
  have hError : Tendsto (fun P : Nat => centeredCharacterBoundaryResidual chi m P -
      boundaryCharacterZeroSeries chi m P) atTop (nhds (0 : Complex)) := by
    simpa only [centeredCharacterBoundaryResidual] using
      centeredCharacter_boundary_zero_expansion_of_ERH chi m hm hPowersERH
  choose C hC using exists_boundaryCharacterZeroSeries_norm_bound chi m hm
    (hPowersERH (m+1) le_rfl (by omega))
  exact Complex.tendsto_mul_star_self_sub_of_tendsto_sub
    (centeredCharacterBoundaryResidual chi m) (boundaryCharacterZeroSeries chi m) hError hC

/-- The exact mean-square identity for the actual fully centered arithmetic
boundary residual, retaining its finite prime moments and principal models. -/
theorem centeredCharacter_boundary_secondMoment_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t)) *
        star (centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t)))))
      atTop (nhds (rootCharacterZeroSecondMoment (chi^(m+1)) (m+1)/(m : Complex)^2)) := by
  have hError := Complex.tendsto_intervalMean_nat_floor_exp
    (fun P : Nat => centeredCharacterBoundaryResidual chi m P * star (centeredCharacterBoundaryResidual chi m P) -
      boundaryCharacterZeroSeries chi m P * star (boundaryCharacterZeroSeries chi m P))
    (centeredCharacterBoundaryResidual_secondMoment_error_tendsto chi m hm hPowersERH)
  have hSeries := boundaryCharacterZeroSeries_secondMoment_tendsto chi m hm
    (hPowersERH (m+1) le_rfl (by omega))
  have h := hError.add hSeries
  simp only [zero_add] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro T
  dsimp only
  rw [Complex.intervalMean_nat_floor_exp_sub
    (fun P : Nat => centeredCharacterBoundaryResidual chi m P * star (centeredCharacterBoundaryResidual chi m P))
    (fun P : Nat => boundaryCharacterZeroSeries chi m P * star (boundaryCharacterZeroSeries chi m P))]
  ring

/-- Exact canonical central contribution to the arithmetic boundary mean. -/
def boundaryCharacterCentralMean {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (m : Nat) : Complex :=
  (2*((m+1 : Nat) : Complex)/((m : Complex)*(((m+1 : Nat) : Complex)-1/2))) *
    (rootCharacterCentralMultiplicity (chi^(m+1)) : Complex)

/-- Actual logarithmic variance after removing precisely the canonical
central mean, including any central-zero multiplicity. -/
theorem centeredCharacter_boundary_variance_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      (centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t))-boundaryCharacterCentralMean chi m) *
        star (centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t))-boundaryCharacterCentralMean chi m)))
      atTop (nhds (rootCharacterZeroSecondMoment (chi^(m+1)) (m+1)/(m : Complex)^2 -
        boundaryCharacterCentralMean chi m * star (boundaryCharacterCentralMean chi m))) := by
  have hMean : Tendsto (Complex.intervalMean (fun t : Real =>
      centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t)))) atTop
      (nhds (boundaryCharacterCentralMean chi m)) :=
    centeredCharacter_boundary_logMean_tendsto chi m hm hPowersERH
  exact Complex.tendsto_intervalMean_nat_floor_exp_variance
    (centeredCharacterBoundaryResidual chi m) (boundaryCharacterCentralMean chi m)
    (rootCharacterZeroSecondMoment (chi^(m+1)) (m+1)/(m : Complex)^2) hMean
    (centeredCharacter_boundary_secondMoment_tendsto chi m hm hPowersERH)

/-- Fully evaluated actual variance: completed logarithmic derivatives,
the full repeated-zero mass, and the squared central contribution. -/
theorem centeredCharacter_boundary_variance_logDeriv_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      (centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t))-boundaryCharacterCentralMean chi m) *
        star (centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t))-boundaryCharacterCentralMean chi m)))
      atTop (nhds (
        ((((m+1 : Nat) : Real)/(((m+1 : Nat) : Real)-1) *
          (-2*(rootCharacterCompletedLogDeriv (chi^(m+1)) 0).re -
            (rootCharacterCompletedLogDeriv (chi^(m+1)) ((m+1 : Nat) : Complex)).re /
              (((m+1 : Nat) : Real)-1/2)) +
          rootCharacterZeroRepeatMass (chi^(m+1)) (m+1) : Real) : Complex)/(m : Complex)^2 -
        boundaryCharacterCentralMean chi m * star (boundaryCharacterCentralMean chi m))) := by
  have h := centeredCharacter_boundary_variance_tendsto chi m hm hPowersERH
  rw [rootCharacterZeroSecondMoment_eq_logDeriv_add_repeat (chi^(m+1))
    (hPowersERH (m+1) le_rfl (by omega)) (by omega : 2 <= m+1)] at h
  exact h

/-- The actual centered variance constant is nonnegative; no sign of the
uncentered arithmetic residual is asserted. -/
theorem centeredCharacter_boundary_variance_re_nonneg
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    0 <= (rootCharacterZeroSecondMoment (chi^(m+1)) (m+1)/(m : Complex)^2 -
      boundaryCharacterCentralMean chi m * star (boundaryCharacterCentralMean chi m)).re := by
  exact Complex.re_nonneg_of_tendsto_intervalMean_mul_star_self
    (fun t : Real => centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t)) -
      boundaryCharacterCentralMean chi m)
    (centeredCharacter_boundary_variance_tendsto chi m hm hPowersERH)

end

end RobinBV.NumberField
