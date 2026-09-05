import RobinBV.NumberField.Proof.CharacterRootPrimeCenteredERH
import RobinBV.NumberField.Proof.MovingCharacterLayerCap
import RobinBV.NumberField.Proof.MovingCharacterLayerHierarchy

/-!
# Higher-layer resonance with exact principal intermediate models

The complete model integral of every earlier principal power is retained.
Actual ERH then suffices for all intervening powers, with no nonprincipal
restriction. Exact finite moments, all cap errors and the full higher tail
remain in the argument at their correct secondary scales.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- Complete root-scale hierarchy after exact earlier principal models
are added. ERH is required only for intervening powers, principal or not. -/
theorem movingCharacter_higher_model_rootScale_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (m L : Nat) (hm : 1 <= m) (hML : m + 1 <= L) (hStrict : L < 2 * (m + 1))
    (hIntervening : forall j : Nat, m + 1 <= j -> j < L -> DirichletERH (chi ^ j)) :
    Tendsto (fun P : Nat =>
      (((((P : Real) ^ m) ^ (1 - Inv.inv (L : Real)) * Real.log ((P : Real) ^ m) : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (Real.log ((P : Real) ^ m) : Complex)) +
          Finset.sum (Finset.Ico (m + 1) L) (fun j =>
            (if chi ^ j = 1 then (1 : Complex) else 0) *
              ((integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
                t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex)))))
      atTop (nhds (-((if chi ^ L = 1 then (1 : Complex) else 0) /
        ((1 - Inv.inv (L : Real) : Real) : Complex)))) := by
  have hL : 2 <= L := by omega
  have hLPos : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
  have hr0 : 0 < Inv.inv (L : Real) := inv_pos.mpr hLPos
  have hr1 : Inv.inv (L : Real) < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le
      (n := 1) (k := L) (by norm_num) hL
  have hX : Tendsto (fun P : Nat => (P : Real) ^ m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < (m : Real) by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  have hEach : forall j : Nat, Membership.mem (Finset.Ico (m + 1) L) j ->
      Tendsto (fun P : Nat =>
        (((((P : Real) ^ m) ^ (1 - Inv.inv (L : Real)) * Real.log ((P : Real) ^ m) : Real) : Complex) *
          (cappedRootPrimeCharacterTail (chi ^ j) P (Inv.inv (j : Real)) ((P : Real) ^ m) -
            (if chi ^ j = 1 then (1 : Complex) else 0) *
              ((integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
                t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex))))
        atTop (nhds (0 : Complex)) := by
    intro j hj
    have hjLow := (Finset.mem_Ico.mp hj).1
    have hjHigh := (Finset.mem_Ico.mp hj).2
    have hRootExponent : (1 / 2 : Real) < (j : Real) * Inv.inv (L : Real) := by
      have hIndex : (L : Real) < 2 * (j : Real) := by exact_mod_cast (show L < 2 * j by omega)
      have hScaled := mul_lt_mul_of_pos_right hIndex hr0
      have hCancel : (L : Real) * Inv.inv (L : Real) = 1 := by field_simp
      rw [hCancel] at hScaled
      linarith
    have hRoot := (rootPrimeCharacterTail_centered_scaled_tendsto_of_ERH (chi ^ j)
      (hIntervening j hjLow hjHigh) (k := j) (by omega)
        (s := Inv.inv (L : Real)) hRootExponent).comp hX
    have hCap := rootPrimeCharacterTail_hierarchy_cap_error_tendsto (chi ^ j) m L j hm hL hjLow
    have h := hRoot.sub hCap
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [] with P
    dsimp only [Function.comp_def]
    simp only [Complex.ofReal_mul]
    ring
  have hInter := tendsto_finsetSum (Finset.Ico (m + 1) L) hEach
  simp only [Finset.sum_const_zero] at hInter
  have hSelected := (rootPrimeCharacterTail_normalized_tendsto (chi ^ L) hr0 hr1).comp hX
  have hSelectedCap := rootPrimeCharacterTail_hierarchy_cap_error_tendsto (chi ^ L) m L L hm hL hML
  have hSelectedCapped : Tendsto (fun P : Nat =>
      (((((P : Real) ^ m) ^ (1 - Inv.inv (L : Real)) * Real.log ((P : Real) ^ m) : Real) : Complex) *
        cappedRootPrimeCharacterTail (chi ^ L) P (Inv.inv (L : Real)) ((P : Real) ^ m)))
      atTop (nhds ((if chi ^ L = 1 then (1 : Complex) else 0) /
        ((1 - Inv.inv (L : Real) : Real) : Complex))) := by
    have h := hSelected.sub hSelectedCap
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [] with P
    dsimp only [Function.comp_def]
    simp only [Complex.ofReal_mul]
    ring
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
  have h := (hInter.neg.sub hSelectedCapped).sub hHigher
  simp only [neg_zero, zero_sub, sub_zero] at h
  apply h.congr'
  filter_upwards [hX.eventually (Filter.eventually_ge_atTop (3 : Real))] with P hx
  rw [movingCharacterCorrection_layer_identity chi P m L hm hML hx
    (by simp only [Nat.cast_pow]; exact le_rfl)]
  simp only [mul_sub, mul_neg, mul_add, Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- Explicit sharp higher resonance with all earlier principal models
retained exactly and no nonprincipal restriction on the intervening powers. -/
theorem movingCharacter_higher_model_resonance_of_ERH
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (m L : Nat) (hm : 1 <= m) (hML : m + 1 <= L) (hStrict : L < 2 * (m + 1))
    (hIntervening : forall j : Nat, m + 1 <= j -> j < L -> DirichletERH (chi ^ j)) :
    Tendsto (fun P : Nat =>
      ((((P : Real) ^ ((m : Real) * ((L : Real) - 1) / (L : Real)) * Real.log P : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (m : Complex) * (Real.log P : Complex)) +
          Finset.sum (Finset.Ico (m + 1) L) (fun j =>
            (if chi ^ j = 1 then (1 : Complex) else 0) *
              ((integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
                t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex)))))
      atTop (nhds (-(L : Complex) / ((m : Complex) * ((L : Complex) - 1)) *
        (if chi ^ L = 1 then (1 : Complex) else 0))) := by
  have hM : Not ((m : Complex) = 0) := by exact_mod_cast (show Not (m = 0) by omega)
  have hL : Not ((L : Complex) = 0) := by exact_mod_cast (show Not (L = 0) by omega)
  have hLR : Not ((L : Real) = 0) := by exact_mod_cast (show Not (L = 0) by omega)
  have hL1 : Not ((L : Complex) - 1 = 0) := by
    intro h
    have : (L : Complex) = 1 := by linear_combination h
    have : L = 1 := by exact_mod_cast this
    omega
  have h := (movingCharacter_higher_model_rootScale_tendsto chi m L hm hML hStrict hIntervening).div_const
    (m : Complex)
  have hLimit : -((if chi ^ L = 1 then (1 : Complex) else 0) /
      ((1 - Inv.inv (L : Real) : Real) : Complex)) / (m : Complex) =
        -(L : Complex) / ((m : Complex) * ((L : Complex) - 1)) *
          (if chi ^ L = 1 then (1 : Complex) else 0) := by
    push_cast
    field_simp [hM, hL, hL1]
  rw [hLimit] at h
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with P hP
  have hPPos : 0 < (P : Real) := by exact_mod_cast (show 0 < P by omega)
  have hExponent : (m : Real) * (1 - Inv.inv (L : Real)) =
      (m : Real) * ((L : Real) - 1) / (L : Real) := by field_simp [hLR]
  have hScale : ((P : Real) ^ m) ^ (1 - Inv.inv (L : Real)) * Real.log ((P : Real) ^ m) =
      (m : Real) * ((P : Real) ^ ((m : Real) * ((L : Real) - 1) / (L : Real)) * Real.log P) := by
    rw [Real.log_pow, <- Real.rpow_natCast, <- Real.rpow_mul hPPos.le, hExponent]
    ring
  rw [hScale, Real.log_pow]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp [hM]

/-- The full exact-model hierarchy applies to the actual centered
integral difference at the original and primorial-enlarged lcm levels. -/
theorem centeredCharacter_higher_model_resonance_of_ERH
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (m L : Nat) (hm : 1 <= m) (hML : m + 1 <= L) (hStrict : L < 2 * (m + 1))
    (hIntervening : forall j : Nat, m + 1 <= j -> j < L -> DirichletERH (chi ^ j)) :
    Tendsto (fun P : Nat =>
      ((((P : Real) ^ ((m : Real) * ((L : Real) - 1) / (L : Real)) * Real.log P : Real) : Complex) *
        (centeredCharacterWeightedIntegral
          (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) ((P : Real) ^ m) -
            centeredCharacterWeightedIntegral chi ((P : Real) ^ m) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
              ((((P : Real) ^ m : Real) : Complex) * (m : Complex) * (Real.log P : Complex)) +
          Finset.sum (Finset.Ico (m + 1) L) (fun j =>
            (if chi ^ j = 1 then (1 : Complex) else 0) *
              ((integral (volume.restrict (Ioi ((P : Real) ^ m))) (fun t : Real =>
                t ^ (Inv.inv (j : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex)))))
      atTop (nhds (-(L : Complex) / ((m : Complex) * ((L : Complex) - 1)) *
        (if chi ^ L = 1 then (1 : Complex) else 0))) := by
  have hX : Tendsto (fun P : Nat => (P : Real) ^ m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < m by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  apply (movingCharacter_higher_model_resonance_of_ERH chi m L hm hML hStrict hIntervening).congr'
  filter_upwards [hX.eventually (Filter.eventually_ge_atTop (3 : Real))] with P hx
  rw [centeredCharacterWeightedIntegral_changeLevel_primorial_sub chi P hx]

end

end RobinBV.NumberField
