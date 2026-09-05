import RobinBV.NumberField.Proof.CharacterRootPrimeCenteredERH
import RobinBV.NumberField.Proof.MovingCharacterLayerCap
import RobinBV.NumberField.Proof.MovingCharacterLayerHierarchy
import RobinBV.NumberField.Proof.RootPrimeSquareRemainder

/-!
# Doubled-layer boundary with the complete first-root term retained

Uncapped prime layers approximate the complete moving correction with
an explicit power-saving residual. At the doubled-layer boundary, the
first Chebyshev root contains the doubled prime layer exactly; its full
contribution must be retained instead of asserting a constant-only limit.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- Any fixed finite interval of complete uncapped root-prime layers
approximates the exact-prefix moving correction at its last root scale.
This transfer is unconditional and has no strict upper bound on L. -/
theorem movingCharacter_uncapped_layers_error_tendsto
    {N : Nat} (chi : DirichletCharacter Complex N) (m L : Nat)
    (hm : 1 <= m) (hML : m + 1 <= L) :
    Tendsto (fun P : Nat =>
      (((((P : Real) ^ m) ^ (1 - Inv.inv (L : Real)) * Real.log ((P : Real) ^ m) : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (Real.log ((P : Real) ^ m) : Complex)) +
          Finset.sum (Finset.Icc (m + 1) L) (fun j =>
            rootPrimeCharacterTail (chi ^ j) (Inv.inv (j : Real)) ((P : Real) ^ m)))))
      atTop (nhds (0 : Complex)) := by
  have hL : 2 <= L := by omega
  have hLPos : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
  have hX : Tendsto (fun P : Nat => (P : Real) ^ m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < m by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  have hEach : forall j : Nat, Membership.mem (Finset.Icc (m + 1) L) j ->
      Tendsto (fun P : Nat =>
        (((((P : Real) ^ m) ^ (1 - Inv.inv (L : Real)) * Real.log ((P : Real) ^ m) : Real) : Complex) *
          (rootPrimeCharacterTail (chi ^ j) (Inv.inv (j : Real)) ((P : Real) ^ m) -
            cappedRootPrimeCharacterTail (chi ^ j) P (Inv.inv (j : Real)) ((P : Real) ^ m))))
        atTop (nhds (0 : Complex)) := by
    intro j hj
    exact rootPrimeCharacterTail_hierarchy_cap_error_tendsto (chi ^ j) m L j hm hL (Finset.mem_Icc.mp hj).1
  have hSum := tendsto_finsetSum (Finset.Icc (m + 1) L) hEach
  simp only [Finset.sum_const_zero] at hSum
  have hHigher : Tendsto (fun P : Nat =>
      (((((P : Real) ^ m) ^ (1 - Inv.inv (L : Real)) * Real.log ((P : Real) ^ m) : Real) : Complex) *
        integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
          Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p L t) *
            (Robin1984.robinRealWeight 1 t : Complex)))) atTop (nhds (0 : Complex)) := by
    apply Metric.tendsto_nhds.mpr
    intro epsilon hEpsilon
    have hExponent : Inv.inv ((L + 1 : Nat) : Real) < Inv.inv (L : Real) := by
      simpa only [one_div] using one_div_lt_one_div_of_lt hLPos
        (show (L : Real) < ((L + 1 : Nat) : Real) by exact_mod_cast Nat.lt_succ_self L)
    have hSmall := higherCharacterPrimePower_uniform_scaled_small L (by omega)
      (s := Inv.inv (L : Real)) hExponent hEpsilon
    filter_upwards [hX.eventually hSmall] with P hSmallP
    simpa only [dist_zero_right] using hSmallP N chi P
  have h := hSum.sub hHigher
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [hX.eventually (Filter.eventually_ge_atTop (3 : Real))] with P hx
  rw [movingCharacterCorrection_prefix_eq_higher_integral chi P m hm hx
    (by simp only [Nat.cast_pow]; exact le_rfl),
    higherCharacterPrimePower_integral_eq_layers_add chi P m L hm (by omega) (by linarith)]
  simp only [mul_add, mul_neg, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- At the doubled-layer boundary the entire first-root Chebyshev term
replaces both its first and doubled prime layers. Only strictly later
intermediate powers need ERH; the first-root term is not dropped. -/
theorem movingCharacter_doubled_boundary_rootScale_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hIntervening : forall j : Nat, m + 2 <= j -> j < 2 * (m + 1) -> DirichletERH (chi ^ j)) :
    Tendsto (fun P : Nat =>
      (((((P : Real) ^ m) ^ (1 - Inv.inv ((2 * (m + 1) : Nat) : Real)) *
        Real.log ((P : Real) ^ m) : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (Real.log ((P : Real) ^ m) : Complex)) +
          rootCharacterChebyshevTail (chi ^ (m + 1)) (m + 1) ((P : Real) ^ m) +
          Finset.sum (Finset.Ico (m + 2) (2 * (m + 1))) (fun j =>
            (if chi ^ j = 1 then (1 : Complex) else 0) *
              ((integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
                t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex)))))
      atTop (nhds (0 : Complex)) := by
  have hLPos : (0 : Real) < ((2 * (m + 1) : Nat) : Real) := by
    exact_mod_cast (show 0 < 2 * (m + 1) by omega)
  have hrPos : 0 < Inv.inv ((2 * (m + 1) : Nat) : Real) := inv_pos.mpr hLPos
  have hX : Tendsto (fun P : Nat => (P : Real) ^ m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < m by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  have hBase := movingCharacter_uncapped_layers_error_tendsto chi m (2 * (m + 1)) hm (by omega)
  have hRootExponent : Inv.inv ((3 * (m + 1) : Nat) : Real) <
      Inv.inv ((2 * (m + 1) : Nat) : Real) := by
    simpa only [one_div] using one_div_lt_one_div_of_lt hLPos
      (show ((2 * (m + 1) : Nat) : Real) < ((3 * (m + 1) : Nat) : Real) by
        exact_mod_cast (show 2 * (m + 1) < 3 * (m + 1) by omega))
  have hRoot := (rootChebyshevTail_sub_prime_sub_square_scaled_tendsto
    (chi ^ (m + 1)) (m + 1) (by omega) hRootExponent).comp hX
  have hPower : (chi ^ (m + 1)) ^ 2 = chi ^ (2 * (m + 1)) := by
    rw [<- pow_mul, Nat.mul_comm (m + 1) 2]
  rw [hPower] at hRoot
  have hEach : forall j : Nat, Membership.mem (Finset.Ico (m + 2) (2 * (m + 1))) j ->
      Tendsto (fun P : Nat =>
        (((((P : Real) ^ m) ^ (1 - Inv.inv ((2 * (m + 1) : Nat) : Real)) *
          Real.log ((P : Real) ^ m) : Real) : Complex) *
          (rootPrimeCharacterTail (chi ^ j) (Inv.inv (j : Real)) ((P : Real) ^ m) -
            (if chi ^ j = 1 then (1 : Complex) else 0) *
              ((integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
                t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex))))
        atTop (nhds (0 : Complex)) := by
    intro j hj
    have hjLow := (Finset.mem_Ico.mp hj).1
    have hjHigh := (Finset.mem_Ico.mp hj).2
    have hExponent : (1 / 2 : Real) < (j : Real) * Inv.inv ((2 * (m + 1) : Nat) : Real) := by
      have hIndex : ((2 * (m + 1) : Nat) : Real) < 2 * (j : Real) := by
        exact_mod_cast (show 2 * (m + 1) < 2 * j by omega)
      have hScaled := mul_lt_mul_of_pos_right hIndex hrPos
      have hCancel : ((2 * (m + 1) : Nat) : Real) * Inv.inv ((2 * (m + 1) : Nat) : Real) = 1 := by
        field_simp
      rw [hCancel] at hScaled
      linarith
    exact (rootPrimeCharacterTail_centered_scaled_tendsto_of_ERH (chi ^ j)
      (hIntervening j hjLow hjHigh) (k := j) (by omega) hExponent).comp hX
  have hSum := tendsto_finsetSum (Finset.Ico (m + 2) (2 * (m + 1))) hEach
  simp only [Finset.sum_const_zero] at hSum
  have h := (hBase.add hRoot).sub hSum
  simp only [add_zero, sub_zero] at h
  have hSet : Finset.Icc (m + 1) (2 * (m + 1)) =
      Insert.insert (m + 1) (Insert.insert (2 * (m + 1)) (Finset.Ico (m + 2) (2 * (m + 1)))) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hFirstNot : Not (Membership.mem
      (Insert.insert (2 * (m + 1)) (Finset.Ico (m + 2) (2 * (m + 1)))) (m + 1)) := by
    simp only [Finset.mem_insert, Finset.mem_Ico]
    omega
  have hLastNot : Not (Membership.mem (Finset.Ico (m + 2) (2 * (m + 1))) (2 * (m + 1))) := by
    simp only [Finset.mem_Ico, lt_self_iff_false, and_false, not_false_eq_true]
  apply h.congr'
  filter_upwards [] with P
  dsimp only [Function.comp_def]
  rw [hSet, Finset.sum_insert hFirstNot, Finset.sum_insert hLastNot]
  simp only [Complex.ofReal_mul, mul_add, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- Explicit prime-cutoff normalization of the equality-boundary
transfer, retaining the whole first-root Chebyshev contribution. -/
theorem movingCharacter_doubled_layer_boundary_of_ERH
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hIntervening : forall j : Nat, m + 2 <= j -> j < 2 * (m + 1) -> DirichletERH (chi ^ j)) :
    Tendsto (fun P : Nat =>
      ((((P : Real) ^ ((m : Real) * (((2 * (m + 1) : Nat) : Real) - 1) /
        ((2 * (m + 1) : Nat) : Real)) * Real.log P : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (m : Complex) * (Real.log P : Complex)) +
          rootCharacterChebyshevTail (chi ^ (m + 1)) (m + 1) ((P : Real) ^ m) +
          Finset.sum (Finset.Ico (m + 2) (2 * (m + 1))) (fun j =>
            (if chi ^ j = 1 then (1 : Complex) else 0) *
              ((integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
                t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex)))))
      atTop (nhds (0 : Complex)) := by
  have hM : Not ((m : Complex) = 0) := by exact_mod_cast (show Not (m = 0) by omega)
  have hLR : Not (((2 * (m + 1) : Nat) : Real) = 0) := by
    exact_mod_cast (show Not (2 * (m + 1) = 0) by omega)
  have h := (movingCharacter_doubled_boundary_rootScale_tendsto chi m hm hIntervening).div_const (m : Complex)
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
  rw [hScale, Real.log_pow]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp [hM]

/-- The boundary cancellation theorem belongs to the actual centered
integrals at the original and primorial-enlarged lcm levels. The full
first-root Chebyshev tail is retained, without any assumption on its ERH. -/
theorem centeredCharacter_doubled_layer_boundary_of_ERH
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hIntervening : forall j : Nat, m + 2 <= j -> j < 2 * (m + 1) -> DirichletERH (chi ^ j)) :
    Tendsto (fun P : Nat =>
      ((((P : Real) ^ ((m : Real) * (((2 * (m + 1) : Nat) : Real) - 1) /
        ((2 * (m + 1) : Nat) : Real)) * Real.log P : Real) : Complex) *
        (centeredCharacterWeightedIntegral
          (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) ((P : Real) ^ m) -
            centeredCharacterWeightedIntegral chi ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (m : Complex) * (Real.log P : Complex)) +
          rootCharacterChebyshevTail (chi ^ (m + 1)) (m + 1) ((P : Real) ^ m) +
          Finset.sum (Finset.Ico (m + 2) (2 * (m + 1))) (fun j =>
            (if chi ^ j = 1 then (1 : Complex) else 0) *
              ((integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
                t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex)))))
      atTop (nhds (0 : Complex)) := by
  have hX : Tendsto (fun P : Nat => (P : Real) ^ m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < m by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  apply (movingCharacter_doubled_layer_boundary_of_ERH chi m hm hIntervening).congr'
  filter_upwards [hX.eventually (Filter.eventually_ge_atTop (3 : Real))] with P hx
  rw [centeredCharacterWeightedIntegral_changeLevel_primorial_sub chi P hx]

end

end RobinBV.NumberField
