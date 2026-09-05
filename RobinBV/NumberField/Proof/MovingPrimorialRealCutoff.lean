import RobinBV.NumberField.Proof.MovingPrimorialAsymptotic

/-!
# Complete principal correction at every real square-root cutoff

The modulus cutoff is floor(sqrt(x)) and x ranges through all sufficiently
large real values. The joint finite sandwich, not a square subsequence or
a fixed-modulus eventual estimate, supplies the full critical-scale limit.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter Asymptotics

noncomputable section

/-- The complete square-root moving correction is squeezed at every real
endpoint, with theta kept exactly at the square-root prime cutoff. -/
theorem movingPrimorial_real_critical_sandwich
    {x : Real} (hx : 3 <= x) :
    And
      (2 * Chebyshev.theta (Real.sqrt x) / Real.sqrt x <=
        (Real.sqrt x * Real.log x) *
          -(movingPrimorialCorrection (Nat.floor (Real.sqrt x)) x).re)
      ((Real.sqrt x * Real.log x) *
          -(movingPrimorialCorrection (Nat.floor (Real.sqrt x)) x).re <=
        ((Nat.primeCounting (Nat.floor (Real.sqrt x)) : Real) * Real.log x / Real.sqrt x) *
          (1 + 1 / Real.log x)) := by
  have hxPos : 0 < x := by linarith
  have hLogPos : 0 < Real.log x := Real.log_pos (by linarith)
  have hSqrtPos := Real.sqrt_pos_of_pos hxPos
  have hSq := Real.sq_sqrt hxPos.le
  have hFloor := Nat.floor_le (Real.sqrt_nonneg x)
  have hPNonneg : (0 : Real) <= (Nat.floor (Real.sqrt x) : Real) := Nat.cast_nonneg _
  have hPowers : (((Nat.floor (Real.sqrt x)) ^ 2 : Nat) : Real) <= x := by
    push_cast
    nlinarith
  have h := movingPrimorialCorrection_sandwich (Nat.floor (Real.sqrt x)) 2 hx hPowers
  rw [<- Chebyshev.theta_eq_theta_coe_floor] at h
  norm_num only [Nat.cast_ofNat] at h
  have hScale : 0 <= Real.sqrt x * Real.log x := mul_nonneg hSqrtPos.le hLogPos.le
  have hLower := mul_le_mul_of_nonneg_left h.1 hScale
  have hUpper := mul_le_mul_of_nonneg_left h.2 hScale
  have hRatio : Real.sqrt x / x = 1 / Real.sqrt x := by
    field_simp [hxPos.ne', hSqrtPos.ne']
    nlinarith
  have hCancel : (Real.sqrt x * Real.log x) / (x * Real.log x) = 1 / Real.sqrt x := by
    calc
      _ = Real.sqrt x / x := by field_simp [hLogPos.ne']
      _ = _ := hRatio
  have hLowerEq : (Real.sqrt x * Real.log x) *
      (2 * Chebyshev.theta (Real.sqrt x) / (x * Real.log x)) =
        2 * Chebyshev.theta (Real.sqrt x) / Real.sqrt x := by
    calc
      _ = (2 * Chebyshev.theta (Real.sqrt x)) *
          ((Real.sqrt x * Real.log x) / (x * Real.log x)) := by ring
      _ = _ := by rw [hCancel]; ring
  have hUpperEq : (Real.sqrt x * Real.log x) *
      ((Nat.primeCounting (Nat.floor (Real.sqrt x)) : Real) * (1 + 1 / Real.log x) / x) =
        ((Nat.primeCounting (Nat.floor (Real.sqrt x)) : Real) * Real.log x / Real.sqrt x) *
          (1 + 1 / Real.log x) := by
    calc
      _ = ((Nat.primeCounting (Nat.floor (Real.sqrt x)) : Real) *
          Real.log x * (1 + 1 / Real.log x)) * (Real.sqrt x / x) := by ring
      _ = _ := by rw [hRatio]; ring
  exact And.intro (hLowerEq.symm.trans_le hLower) (hUpper.trans_eq hUpperEq)

private theorem theta_sqrt_ratio_tendsto :
    Tendsto (fun x : Real => Chebyshev.theta (Real.sqrt x) / Real.sqrt x) atTop (nhds 1) := by
  have hNe : Filter.Eventually (fun x : Real => Not (id x = 0)) atTop := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    exact hx.ne'
  have h : Tendsto (fun x : Real => Chebyshev.theta x / x) atTop (nhds (1 : Real)) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hNe).1 chebyshev_asymptotic
  exact h.comp Real.tendsto_sqrt_atTop

/-- The full real moving principal correction has coefficient -2, not
merely along square endpoints. Only ordinary PNT is used. -/
theorem movingPrimorial_real_critical_re_tendsto :
    Tendsto (fun x : Real => (Real.sqrt x * Real.log x) *
      (movingPrimorialCorrection (Nat.floor (Real.sqrt x)) x).re) atTop (nhds (-2 : Real)) := by
  have hPiNe : Filter.Eventually (fun x : Real => Not (x / Real.log x = 0)) atTop := by
    filter_upwards [Filter.eventually_gt_atTop (1 : Real)] with x hx
    exact div_ne_zero (by linarith) (Real.log_pos hx).ne'
  have hPiReal := (Asymptotics.isEquivalent_iff_tendsto_one hPiNe).1 pi_alt'
  have hPiComp := hPiReal.comp Real.tendsto_sqrt_atTop
  change Tendsto (fun x : Real => (Nat.primeCounting (Nat.floor (Real.sqrt x)) : Real) /
    (Real.sqrt x / Real.log (Real.sqrt x))) atTop (nhds (1 : Real)) at hPiComp
  have hPi : Tendsto (fun x : Real =>
      (Nat.primeCounting (Nat.floor (Real.sqrt x)) : Real) * Real.log x / Real.sqrt x)
      atTop (nhds (2 : Real)) := by
    have hTwice := hPiComp.const_mul 2
    norm_num only [mul_one] at hTwice
    apply hTwice.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : Real)] with x hx
    rw [Real.log_sqrt hx, div_div_eq_mul_div]
    ring
  have hSmall : Tendsto (fun x : Real => 1 / Real.log x) atTop (nhds (0 : Real)) :=
    Real.tendsto_log_atTop.const_div_atTop 1
  have hUpper : Tendsto (fun x : Real =>
      ((Nat.primeCounting (Nat.floor (Real.sqrt x)) : Real) * Real.log x / Real.sqrt x) *
        (1 + 1 / Real.log x)) atTop (nhds (2 : Real)) := by
    simpa only [add_zero, mul_one] using hPi.mul (hSmall.const_add 1)
  have hLower : Tendsto (fun x : Real => 2 * Chebyshev.theta (Real.sqrt x) / Real.sqrt x)
      atTop (nhds (2 : Real)) := by
    simpa only [mul_div_assoc, mul_one] using theta_sqrt_ratio_tendsto.const_mul 2
  have hBounds := (Filter.eventually_ge_atTop (3 : Real)).mono
    (fun x hx => movingPrimorial_real_critical_sandwich hx)
  have hPositive := tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper
    (hBounds.mono (fun _ h => h.1)) (hBounds.mono (fun _ h => h.2))
  convert hPositive.neg using 1
  funext x
  ring

/-- The entire complete principal residual after the first two layers
vanishes at the critical scale for arbitrary real endpoints. -/
theorem movingPrimorial_real_prefix_remainder_tendsto :
    Tendsto (fun x : Real => -((Real.sqrt x * Real.log x) *
      (movingPrimorialCorrection (Nat.floor (Real.sqrt x)) x).re) -
        2 * Chebyshev.theta (Real.sqrt x) / Real.sqrt x) atTop (nhds (0 : Real)) := by
  have hTheta : Tendsto (fun x : Real => 2 * Chebyshev.theta (Real.sqrt x) / Real.sqrt x)
      atTop (nhds (2 : Real)) := by
    simpa only [mul_div_assoc, mul_one] using theta_sqrt_ratio_tendsto.const_mul 2
  simpa only [neg_neg, sub_self] using movingPrimorial_real_critical_re_tendsto.neg.sub hTheta

end

end RobinBV.NumberField
