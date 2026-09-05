import RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimePowerRemainder
import RobinBV.NumberField.Proof.PowerTailAsymptotic

/-!
# Complete integrated bounds for all higher character prime powers

The elementary root-log bound is integrated over the entire infinite tail.
The resulting power saving is uniform in the character and prime cap, and
requires no cancellation or RH assumption.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set

noncomputable section

private theorem log_mul_power_mul_robinWeight
    (a : Real) {t : Real} (ht : 1 < t) :
    (t ^ a * Real.log t) * Robin1984.robinRealWeight 1 t =
      t ^ (a - 2) * (1 + 1 / Real.log t) := by
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  have hLog := (Real.log_pos ht).ne'
  have hPower : t ^ a * t ^ (-2 : Real) = t ^ (a - 2) := by
    rw [<- Real.rpow_add htPos]
    congr 1
  unfold Robin1984.robinRealWeight
  norm_num only [Nat.cast_one, one_mul]
  calc
    _ = (t ^ a * t ^ (-2 : Real)) * ((Real.log t + 1) / Real.log t) := by
      field_simp [hLog]
    _ = _ := by
      rw [hPower]
      field_simp [hLog]

/-- Absolute integrability and a complete power-saving bound for every
higher layer together. Both estimates are uniform in cap and character. -/
theorem higherCharacterPrimePower_integral_data
    {N : Nat} (chi : DirichletCharacter Complex N) (P k : Nat) (hk : 1 <= k)
    {x : Real} (hx : 1 < x) :
    And
      (IntegrableOn (fun t : Real =>
        Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p k t) *
          (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x))
      (norm (integral (volume.restrict (Ioi x)) (fun t : Real =>
        Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p k t) *
          (Robin1984.robinRealWeight 1 t : Complex))) <=
        (1 + 1 / Real.log x) / (1 - Inv.inv ((k + 1 : Nat) : Real)) *
          x ^ (Inv.inv ((k + 1 : Nat) : Real) - 1)) := by
  let a : Real := Inv.inv ((k + 1 : Nat) : Real)
  let C : Real := 1 + 1 / Real.log x
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLogPos := Real.log_pos hx
  have ha : a < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le (n := 1) (k := k + 1)
      (by norm_num) (by omega)
  have hExponent : a - 2 < -1 := by linarith
  have hMajor : IntegrableOn (fun t : Real => C * t ^ (a - 2)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt hExponent hxPos).const_mul C
  have hStepMeas : Measurable (fun t : Real =>
      Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p k t)) := by
    let f : Nat -> Complex := fun n => Finset.sum (Nat.primesLE P) (fun p =>
      (Real.log p : Complex) * Finset.sum (Finset.Icc (k + 1) (Nat.log p n))
        (fun j => chi (p : ZMod N) ^ j))
    change Measurable (fun t : Real => f (Nat.floor t))
    exact (measurable_of_countable f).comp Nat.measurable_floor
  have hWeightMeas : Measurable (fun t : Real => (Robin1984.robinRealWeight 1 t : Complex)) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  have hBoundAE : Filter.Eventually (fun t : Real =>
      norm (Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p k t) *
        (Robin1984.robinRealWeight 1 t : Complex)) <= C * t ^ (a - 2))
      (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t := hx.trans ht
    have htPos : 0 < t := lt_trans Real.zero_lt_one htOne
    have hWeight := Robin1984.robinRealWeight_nonneg (n := 1) htOne
    have hInv : 1 / Real.log t <= 1 / Real.log x :=
      one_div_le_one_div_of_le hLogPos (Real.log_le_log hxPos ht.le)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeight]
    calc
      _ <= (t ^ a * Real.log t) * Robin1984.robinRealWeight 1 t :=
        mul_le_mul_of_nonneg_right (chi.norm_sum_primePowerHigherStep_le_root_log P k htOne.le) hWeight
      _ = t ^ (a - 2) * (1 + 1 / Real.log t) := log_mul_power_mul_robinWeight a htOne
      _ <= t ^ (a - 2) * C := mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hInv) (Real.rpow_nonneg htPos.le _)
      _ = _ := mul_comm _ _
  have hInt : IntegrableOn (fun t : Real =>
      Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p k t) *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) :=
    hMajor.mono' (hStepMeas.mul hWeightMeas).aestronglyMeasurable hBoundAE
  have hNorm := norm_integral_le_of_norm_le hMajor hBoundAE
  have hIntegral : integral (volume.restrict (Ioi x)) (fun t : Real => C * t ^ (a - 2)) =
      C / (1 - a) * x ^ (a - 1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hExponent hxPos]
    rw [show a - 2 + 1 = a - 1 by ring]
    field_simp [show Not (a - 1 = 0) by linarith, show Not (1 - a = 0) by linarith]
    ring
  exact And.intro hInt (hNorm.trans_eq hIntegral)

/-- At any scale strictly above the higher-layer root exponent, the
complete normalized higher-power integral vanishes uniformly in every
character, modulus and prime cap. -/
theorem higherCharacterPrimePower_uniform_scaled_small
    (k : Nat) (hk : 1 <= k) {s : Real} (hs : Inv.inv ((k + 1 : Nat) : Real) < s)
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real => forall N : Nat,
      forall chi : DirichletCharacter Complex N, forall P : Nat,
        norm (((x ^ (1 - s) * Real.log x : Real) : Complex) *
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p k t) *
              (Robin1984.robinRealWeight 1 t : Complex))) < epsilon) atTop := by
  let a : Real := Inv.inv ((k + 1 : Nat) : Real)
  have hLogPower : Tendsto (fun x : Real => Real.log x / x ^ (s - a)) atTop (nhds (0 : Real)) :=
    (isLittleO_log_rpow_atTop (show 0 < s - a from sub_pos.mpr hs)).tendsto_div_nhds_zero
  have hSmall : Tendsto (fun x : Real => x ^ (a - s) * Real.log x) atTop (nhds (0 : Real)) := by
    apply hLogPower.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    rw [show a - s = -(s - a) by ring, Real.rpow_neg hx.le]
    ring
  have hInvLog : Tendsto (fun x : Real => 1 / Real.log x) atTop (nhds (0 : Real)) :=
    Real.tendsto_log_atTop.const_div_atTop 1
  have hCoefficient : Tendsto (fun x : Real => (1 + 1 / Real.log x) / (1 - a))
      atTop (nhds (1 / (1 - a))) := by
    simpa only [add_zero] using (hInvLog.const_add 1).div_const (1 - a)
  have hUpper : Tendsto (fun x : Real => ((1 + 1 / Real.log x) / (1 - a)) *
      (x ^ (a - s) * Real.log x)) atTop (nhds (0 : Real)) := by
    simpa only [mul_zero] using hCoefficient.mul hSmall
  have hLate := hUpper.eventually (eventually_lt_nhds hEpsilon)
  filter_upwards [Filter.eventually_gt_atTop (1 : Real), hLate] with x hx hLateX
  intro N chi P
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hScale : 0 <= x ^ (1 - s) * Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_pos hx).le
  have hBound := (higherCharacterPrimePower_integral_data chi P k hk hx).2
  have hPowers : x ^ (1 - s) * x ^ (a - 1) = x ^ (a - s) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  have hNormalize : (x ^ (1 - s) * Real.log x) *
      (((1 + 1 / Real.log x) / (1 - a)) * x ^ (a - 1)) =
        ((1 + 1 / Real.log x) / (1 - a)) * (x ^ (a - s) * Real.log x) := by
    calc
      _ = ((1 + 1 / Real.log x) / (1 - a)) *
          (x ^ (1 - s) * x ^ (a - 1)) * Real.log x := by ring
      _ = _ := by rw [hPowers]; ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale]
  exact ((mul_le_mul_of_nonneg_left hBound hScale).trans_eq hNormalize).trans_lt hLateX

end

end RobinBV.NumberField
