import RobinBV.NumberField.Proof.CharacterBoundaryOscillation
import RobinBV.NumberField.Proof.ZeroSeriesCovariance

/-!
# Complete cross-character and cross-layer arithmetic covariance

All canonical scaled-frequency collisions remain explicit. Arithmetic
errors are transferred bilinearly using the proved full comparison bounds.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory

noncomputable section

/-- The full canonical covariance on the two actual boundary scales. -/
def boundaryCharacterZeroCovariance {N M : Nat} [NeZero N] [NeZero M]
    (chi : DirichletCharacter Complex N) (eta : DirichletCharacter Complex M)
    (m n : Nat) : Complex :=
  rootCharacterZeroCovariance (chi^(m+1)) (eta^(n+1)) (m+1) (n+1) m n /
    ((m : Complex)*(n : Complex))

/-- Exact complete covariance of the two canonical boundary zero series. -/
theorem boundaryCharacterZeroSeries_covariance_tendsto
    {N M : Nat} [NeZero N] [NeZero M]
    (chi : DirichletCharacter Complex N) (eta : DirichletCharacter Complex M)
    (m n : Nat) (hm : 1 <= m) (hn : 1 <= n)
    (hChiERH : DirichletERH (chi^(m+1))) (hEtaERH : DirichletERH (eta^(n+1))) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      boundaryCharacterZeroSeries chi m (Nat.floor (Real.exp t)) *
        star (boundaryCharacterZeroSeries eta n (Nat.floor (Real.exp t)))))
      atTop (nhds (boundaryCharacterZeroCovariance chi eta m n)) := by
  have h := (rootCharacterZeroSeries_power_covariance_tendsto
    (chi^(m+1)) (eta^(n+1)) hChiERH hEtaERH (by omega : 2 <= m+1)
    (by omega : 2 <= n+1) m n).div_const ((m : Complex)*(n : Complex))
  have hScale (z w : Complex) : (z/(m : Complex))*star (w/(n : Complex)) =
      (z*star w)/((m : Complex)*(n : Complex)) := by
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro T
  have hFunction : (fun t : Real =>
      boundaryCharacterZeroSeries chi m (Nat.floor (Real.exp t)) *
        star (boundaryCharacterZeroSeries eta n (Nat.floor (Real.exp t)))) =
      (fun t : Real => (rootCharacterZeroSeries (chi^(m+1)) (m+1) ((Nat.floor (Real.exp t) : Real)^m) *
        star (rootCharacterZeroSeries (eta^(n+1)) (n+1) ((Nat.floor (Real.exp t) : Real)^n))) /
          ((m : Complex)*(n : Complex))) := by
    funext t
    rw [<- rootCharacterZeroSeries_power_cutoff_div_eq chi m (Nat.floor (Real.exp t)),
      <- rootCharacterZeroSeries_power_cutoff_div_eq eta n (Nat.floor (Real.exp t)), hScale]
  dsimp only
  unfold Complex.intervalMean
  rw [hFunction, intervalIntegral.integral_div]
  ring

/-- The complete conjugate-product arithmetic error tends to zero;
both linear errors and their product are controlled by actual providers. -/
theorem centeredCharacterBoundaryResidual_covariance_error_tendsto
    {N M : Nat} [NeZero N] [NeZero M]
    (chi : DirichletCharacter Complex N) (eta : DirichletCharacter Complex M)
    (m n : Nat) (hm : 1 <= m) (hn : 1 <= n)
    (hChiPowers : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j))
    (hEtaPowers : forall j : Nat, n+1 <= j -> j < 2*(n+1) -> DirichletERH (eta^j)) :
    Tendsto (fun P : Nat =>
      centeredCharacterBoundaryResidual chi m P * star (centeredCharacterBoundaryResidual eta n P) -
        boundaryCharacterZeroSeries chi m P * star (boundaryCharacterZeroSeries eta n P))
      atTop (nhds (0 : Complex)) := by
  have hChiError : Tendsto (fun P : Nat => centeredCharacterBoundaryResidual chi m P -
      boundaryCharacterZeroSeries chi m P) atTop (nhds (0 : Complex)) := by
    simpa only [centeredCharacterBoundaryResidual] using
      centeredCharacter_boundary_zero_expansion_of_ERH chi m hm hChiPowers
  have hEtaError : Tendsto (fun P : Nat => centeredCharacterBoundaryResidual eta n P -
      boundaryCharacterZeroSeries eta n P) atTop (nhds (0 : Complex)) := by
    simpa only [centeredCharacterBoundaryResidual] using
      centeredCharacter_boundary_zero_expansion_of_ERH eta n hn hEtaPowers
  choose C hC using exists_boundaryCharacterZeroSeries_norm_bound chi m hm
    (hChiPowers (m+1) le_rfl (by omega))
  choose D hD using exists_boundaryCharacterZeroSeries_norm_bound eta n hn
    (hEtaPowers (n+1) le_rfl (by omega))
  exact Complex.tendsto_mul_star_sub_of_tendsto_sub
    (centeredCharacterBoundaryResidual chi m) (centeredCharacterBoundaryResidual eta n)
    (boundaryCharacterZeroSeries chi m) (boundaryCharacterZeroSeries eta n)
    hChiError hEtaError hC hD

/-- Exact full covariance of actual normalized arithmetic boundaries for
arbitrary complex characters, positive moduli and two fixed positive layers. -/
theorem centeredCharacter_boundary_covariance_tendsto
    {N M : Nat} [NeZero N] [NeZero M]
    (chi : DirichletCharacter Complex N) (eta : DirichletCharacter Complex M)
    (m n : Nat) (hm : 1 <= m) (hn : 1 <= n)
    (hChiPowers : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j))
    (hEtaPowers : forall j : Nat, n+1 <= j -> j < 2*(n+1) -> DirichletERH (eta^j)) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t)) *
        star (centeredCharacterBoundaryResidual eta n (Nat.floor (Real.exp t)))))
      atTop (nhds (boundaryCharacterZeroCovariance chi eta m n)) := by
  have hZero := boundaryCharacterZeroSeries_covariance_tendsto chi eta m n hm hn
    (hChiPowers (m+1) le_rfl (by omega)) (hEtaPowers (n+1) le_rfl (by omega))
  have hError := centeredCharacterBoundaryResidual_covariance_error_tendsto
    chi eta m n hm hn hChiPowers hEtaPowers
  have hErrorMean := Complex.tendsto_intervalMean_nat_floor_exp
    (fun P : Nat =>
      centeredCharacterBoundaryResidual chi m P*star (centeredCharacterBoundaryResidual eta n P) -
        boundaryCharacterZeroSeries chi m P*star (boundaryCharacterZeroSeries eta n P)) hError
  have h := hZero.add hErrorMean
  simp only [add_zero] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro T
  dsimp only
  rw [Complex.intervalMean_nat_floor_exp_sub
    (fun P => centeredCharacterBoundaryResidual chi m P*star (centeredCharacterBoundaryResidual eta n P))
    (fun P => boundaryCharacterZeroSeries chi m P*star (boundaryCharacterZeroSeries eta n P))]
  ring

/-- Exact centered covariance of the actual arithmetic residuals. The
two canonical central-multiplicity means are subtracted, not assumed zero. -/
theorem centeredCharacter_boundary_centered_covariance_tendsto
    {N M : Nat} [NeZero N] [NeZero M]
    (chi : DirichletCharacter Complex N) (eta : DirichletCharacter Complex M)
    (m n : Nat) (hm : 1 <= m) (hn : 1 <= n)
    (hChiPowers : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j))
    (hEtaPowers : forall j : Nat, n+1 <= j -> j < 2*(n+1) -> DirichletERH (eta^j)) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      (centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t)) -
        boundaryCharacterCentralMean chi m) *
      star (centeredCharacterBoundaryResidual eta n (Nat.floor (Real.exp t)) -
        boundaryCharacterCentralMean eta n)))
      atTop (nhds (boundaryCharacterZeroCovariance chi eta m n -
        boundaryCharacterCentralMean chi m * star (boundaryCharacterCentralMean eta n))) := by
  have hMeanChi : Tendsto (Complex.intervalMean (fun t : Real =>
      centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t))))
      atTop (nhds (boundaryCharacterCentralMean chi m)) := by
    simpa only [boundaryCharacterCentralMean] using
      centeredCharacter_boundary_logMean_tendsto chi m hm hChiPowers
  have hMeanEta : Tendsto (Complex.intervalMean (fun t : Real =>
      centeredCharacterBoundaryResidual eta n (Nat.floor (Real.exp t))))
      atTop (nhds (boundaryCharacterCentralMean eta n)) := by
    simpa only [boundaryCharacterCentralMean] using
      centeredCharacter_boundary_logMean_tendsto eta n hn hEtaPowers
  exact Complex.tendsto_intervalMean_nat_floor_exp_centered_product
    (centeredCharacterBoundaryResidual chi m) (centeredCharacterBoundaryResidual eta n)
    (boundaryCharacterCentralMean chi m) (boundaryCharacterCentralMean eta n)
    (boundaryCharacterZeroCovariance chi eta m n) hMeanChi hMeanEta
    (centeredCharacter_boundary_covariance_tendsto chi eta m n hm hn hChiPowers hEtaPowers)

end

end RobinBV.NumberField
