import RobinBV.NumberField.Proof.MovingCharacterBoundary
import RobinBV.NumberField.Proof.RootCharacterZeroExpansion

/-!
# Complete zero-series secondary term at the doubled moving boundary

The doubled arithmetic layer cancels, leaving the actual complete
first-root zero series. Exact earlier finite moments and principal
models remain, with the positive (m+1)/m spectral coefficient.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- Fully expanded canonical boundary zero series at the prime cutoff.
The actual first character power chooses zeta or its primitive L-divisor;
central zeros and every multiplicity remain in the complete sum. -/
def boundaryCharacterZeroSeries
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m P : Nat) : Complex :=
  let psi := chi ^ (m + 1)
  letI : NeZero psi.conductor := NeZero.mk psi.conductor_ne_zero
  (((m + 1 : Nat) : Complex) / (m : Complex)) *
    (if psi = 1 then
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        (P : Complex) ^ ((m : Complex) * (riemannXiDivisorZeroValue p - 1 / 2) / ((m + 1 : Nat) : Complex)) /
          (riemannXiDivisorZeroValue p * (((m + 1 : Nat) : Complex) - riemannXiDivisorZeroValue p)))
    else
      tsum (fun p : QuadraticLZeroIndex psi.primitiveCharacter =>
        (P : Complex) ^ ((m : Complex) * (quadraticLZeroValue p - 1 / 2) / ((m + 1 : Nat) : Complex)) /
          (quadraticLZeroValue p * (((m + 1 : Nat) : Complex) - quadraticLZeroValue p))))

/-- Exact expanded prime-cutoff phase and coefficient, including the
root-substitution and logarithmic normalization factors. -/
theorem rootCharacterZeroSeries_power_cutoff_div_eq
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m P : Nat) :
    rootCharacterZeroSeries (chi ^ (m + 1)) (m + 1) ((P : Real) ^ m) / (m : Complex) =
      boundaryCharacterZeroSeries chi m P := by
  have hPhase (rho : Complex) :
      ((((P : Real) ^ m : Real) : Complex)) ^ ((rho - 1 / 2) / ((m + 1 : Nat) : Complex)) =
        (P : Complex) ^ ((m : Complex) * (rho - 1 / 2) / ((m + 1 : Nat) : Complex)) := by
    rw [<- Real.rpow_natCast, <- Complex.cpow_mul_ofReal_nonneg (Nat.cast_nonneg P)]
    congr 1
    simp only [Complex.ofReal_natCast]
    ring
  dsimp only [rootCharacterZeroSeries, boundaryCharacterZeroSeries]
  split_ifs
  all_goals
    rw [div_eq_mul_inv, <- tsum_mul_right, <- tsum_mul_left]
    apply tsum_congr
    intro p
    rw [hPhase]
    ring

/-- The exact earlier-model-centered residual at the doubled boundary
has the canonical complete zero series as its leading term. ERH is
assumed precisely for the powers m+1 through 2(m+1)-1. -/
theorem movingCharacter_boundary_zero_rootScale_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hPowersERH : forall j : Nat, m + 1 <= j -> j < 2 * (m + 1) -> DirichletERH (chi ^ j)) :
    Tendsto (fun P : Nat =>
      (((((P : Real) ^ m) ^ (1 - Inv.inv ((2 * (m + 1) : Nat) : Real)) *
        Real.log ((P : Real) ^ m) : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (Real.log ((P : Real) ^ m) : Complex)) +
          Finset.sum (Finset.Ico (m + 1) (2 * (m + 1))) (fun j =>
            (if chi ^ j = 1 then (1 : Complex) else 0) *
              ((integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
                t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex))) -
        rootCharacterZeroSeries (chi ^ (m + 1)) (m + 1) ((P : Real) ^ m)))
      atTop (nhds (0 : Complex)) := by
  have hX : Tendsto (fun P : Nat => (P : Real) ^ m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < m by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  have hBoundary := movingCharacter_doubled_boundary_rootScale_tendsto chi m hm
    (fun j hj hLt => hPowersERH j (by omega) hLt)
  have hZeros := (rootCharacterChebyshevTail_centered_add_zeroSeries_tendsto (chi ^ (m + 1))
    (hPowersERH (m + 1) le_rfl (by omega)) (by omega : 2 <= m + 1)).comp hX
  have h := hBoundary.sub hZeros
  simp only [sub_zero] at h
  have hSet : Finset.Ico (m + 1) (2 * (m + 1)) =
      Insert.insert (m + 1) (Finset.Ico (m + 2) (2 * (m + 1))) := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  have hNot : Not (Membership.mem (Finset.Ico (m + 2) (2 * (m + 1))) (m + 1)) := by
    simp only [Finset.mem_Ico]
    omega
  apply h.congr'
  filter_upwards [] with P
  dsimp only [Function.comp_def]
  rw [hSet, Finset.sum_insert hNot]
  simp only [Complex.ofReal_mul]
  ring

/-- Explicit prime-cutoff zero expansion of the complete moving
residual, with all earlier finite moments and principal models exact. -/
theorem movingCharacter_boundary_zero_expansion_of_ERH
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hPowersERH : forall j : Nat, m + 1 <= j -> j < 2 * (m + 1) -> DirichletERH (chi ^ j)) :
    Tendsto (fun P : Nat =>
      ((((P : Real) ^ ((m : Real) * (((2 * (m + 1) : Nat) : Real) - 1) /
        ((2 * (m + 1) : Nat) : Real)) * Real.log P : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (m : Complex) * (Real.log P : Complex)) +
          Finset.sum (Finset.Ico (m + 1) (2 * (m + 1))) (fun j =>
            (if chi ^ j = 1 then (1 : Complex) else 0) *
              ((integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
                t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex))) -
        boundaryCharacterZeroSeries chi m P)) atTop (nhds (0 : Complex)) := by
  have hM : Not ((m : Complex) = 0) := by exact_mod_cast (show Not (m = 0) by omega)
  have hLR : Not (((2 * (m + 1) : Nat) : Real) = 0) := by
    exact_mod_cast (show Not (2 * (m + 1) = 0) by omega)
  have h := (movingCharacter_boundary_zero_rootScale_tendsto chi m hm hPowersERH).div_const (m : Complex)
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with P hP
  have hPPos : 0 < (P : Real) := by exact_mod_cast (show 0 < P by omega)
  have hExponent : (m : Real) * (1 - Inv.inv ((2 * (m + 1) : Nat) : Real)) =
      (m : Real) * (((2 * (m + 1) : Nat) : Real) - 1) / ((2 * (m + 1) : Nat) : Real) := by
    field_simp [hLR]
  have hScale : ((P : Real) ^ m) ^ (1 - Inv.inv ((2 * (m + 1) : Nat) : Real)) * Real.log ((P : Real) ^ m) =
      (m : Real) * ((P : Real) ^ ((m : Real) * (((2 * (m + 1) : Nat) : Real) - 1) /
        ((2 * (m + 1) : Nat) : Real)) * Real.log P) := by
    rw [Real.log_pow, <- Real.rpow_natCast, <- Real.rpow_mul hPPos.le, hExponent]
    ring
  rw [hScale, Real.log_pow, <- rootCharacterZeroSeries_power_cutoff_div_eq chi m P]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp [hM]

/-- Full zero-series secondary expansion for the actual centered
integrals at the original and primorial-enlarged lcm levels. It does
not assert a limit as P tends to infinity or a sign for the leading series. -/
theorem centeredCharacter_boundary_zero_expansion_of_ERH
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hPowersERH : forall j : Nat, m + 1 <= j -> j < 2 * (m + 1) -> DirichletERH (chi ^ j)) :
    Tendsto (fun P : Nat =>
      ((((P : Real) ^ ((m : Real) * (((2 * (m + 1) : Nat) : Real) - 1) /
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
                t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex))) -
        boundaryCharacterZeroSeries chi m P)) atTop (nhds (0 : Complex)) := by
  have hX : Tendsto (fun P : Nat => (P : Real) ^ m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < m by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  apply (movingCharacter_boundary_zero_expansion_of_ERH chi m hm hPowersERH).congr'
  filter_upwards [hX.eventually (Filter.eventually_ge_atTop (3 : Real))] with P hx
  rw [centeredCharacterWeightedIntegral_changeLevel_primorial_sub chi P hx]

end

end RobinBV.NumberField
