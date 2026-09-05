import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Robin1984.Equivalence.WeightedKernelBounds
import RobinBV.NumberField.Proof.QuadraticCharacterOddGammaCorrection

/-!
# Quantitative quadratic-character gamma correction bounds

The even origin term and the odd negative-integer kernel family are bounded
uniformly at exponent two. These estimates make the canonical character
correction lower order after endpoint reweighting.
-/

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

theorem quadraticCharacterEvenOriginCorrection_eq
    {x : Real} (hx : 1 < x) :
    quadraticCharacterEvenOriginCorrection 2 x =
      ((x ^ (-(2 : Real)) : Real) : Complex) +
        Robin1984.robinCpowLogTail
          ((-(2 : Real) : Real) : Complex) 1 x := by
  have hPair :=
    Robin1984.robinCutoffMellin_resolvent_pairing
      (n := 2) (by norm_num : 1 <= (2 : Nat)) hx
      (c := (3 / 2 : Real))
      (by norm_num : (0 : Real) < 3 / 2)
      (by norm_num : (3 / 2 : Real) < 2)
      (rho := 0) (by norm_num)
  have hOrigin :
      quadraticCharacterEvenOriginCorrection 2 x =
        integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
          (u : Complex) ^ (-(1 : Complex)) *
            Robin1984.robinCutoffMellinTest 2 x u) := by
    unfold quadraticCharacterEvenOriginCorrection
    simpa [sub_zero] using! hPair
  have hInt :=
    Robin1984.integrableOn_robinCutoffMellinTest_power_tail
      (n := 2) hx (rho := 0) (by norm_num)
  have hLow :=
    hInt.mono_set (Ioc_subset_Ioi_self :
      Ioc (1 : Real) x <= Ioi 1)
  have hHigh :=
    hInt.mono_set (Ioi_subset_Ioi hx.le)
  have hLowValue :
      integral (volume.restrict (Ioc (1 : Real) x)) (fun u : Real =>
        (u : Complex) ^ (-(1 : Complex)) *
          Robin1984.robinCutoffMellinTest 2 x u) =
        ((x ^ (-(2 : Real)) : Real) : Complex) := by
    calc
      integral (volume.restrict (Ioc (1 : Real) x)) (fun u : Real =>
          (u : Complex) ^ (-(1 : Complex)) *
            Robin1984.robinCutoffMellinTest 2 x u) =
        integral (volume.restrict (Ioc (1 : Real) x)) (fun u : Real =>
          ((u ^ (-(1 : Real)) *
            (x ^ (-(2 : Real)) *
              Inv.inv (Real.log x)) : Real) : Complex)) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro u hu
          have huPos : 0 < u := lt_trans Real.zero_lt_one hu.1
          have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
          simp only [Robin1984.robinCutoffMellinTest,
            if_pos hu.2]
          have huPow :
              (u : Complex) ^ (-(1 : Complex)) =
                ((u ^ (-(1 : Real)) : Real) : Complex) := by
            rw [show (-(1 : Complex)) =
              ((-(1 : Real) : Real) : Complex) by norm_num]
            exact (Complex.ofReal_cpow huPos.le (-(1 : Real))).symm
          have hxPow :
              (x : Complex) ^ (-((2 : Nat) : Complex)) =
                ((x ^ (-(2 : Real)) : Real) : Complex) := by
            rw [show (-((2 : Nat) : Complex)) =
              ((-(2 : Real) : Real) : Complex) by norm_num]
            exact (Complex.ofReal_cpow hxPos.le (-(2 : Real))).symm
          rw [huPow, hxPow]
          push_cast
          rfl
      _ = ((integral (volume.restrict (Ioc (1 : Real) x))
          (fun u : Real =>
          u ^ (-(1 : Real)) *
            (x ^ (-(2 : Real)) *
              Inv.inv (Real.log x))) : Real) : Complex) := by
          rw [integral_complex_ofReal]
      _ = ((integral (volume.restrict (Ioc (1 : Real) x)) (fun u : Real =>
          Inv.inv u *
            (x ^ (-(2 : Real)) *
              Inv.inv (Real.log x))) : Real) : Complex) := by
          congr 1
          apply setIntegral_congr_fun measurableSet_Ioc
          intro u hu
          change u ^ (-(1 : Real)) *
            (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) =
            Inv.inv u *
              (x ^ (-(2 : Real)) * Inv.inv (Real.log x))
          rw [Real.rpow_neg_one]
      _ = (((integral (volume.restrict (Ioc (1 : Real) x))
            (fun u : Real => Inv.inv u)) *
          (x ^ (-(2 : Real)) *
            Inv.inv (Real.log x)) : Real) : Complex) := by
            congr 1
            rw [integral_mul_const]
      _ = ((Real.log x *
          (x ^ (-(2 : Real)) *
            Inv.inv (Real.log x)) : Real) : Complex) := by
            congr 1
            rw [<- intervalIntegral.integral_of_le hx.le,
              integral_inv_of_pos
                Real.zero_lt_one (lt_trans Real.zero_lt_one hx)]
            simp
      _ = ((x ^ (-(2 : Real)) : Real) : Complex) := by
            congr 1
            have hLog : Not (Real.log x = 0) :=
              ne_of_gt (Real.log_pos hx)
            field_simp [hLog]
  have hHighValue :
      integral (volume.restrict (Ioi x)) (fun u : Real =>
        (u : Complex) ^ (-(1 : Complex)) *
          Robin1984.robinCutoffMellinTest 2 x u) =
        Robin1984.robinCpowLogTail
          ((-(2 : Real) : Real) : Complex) 1 x := by
    unfold Robin1984.robinCpowLogTail
    simp only [pow_one]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simpa using!
      Robin1984.robinCutoffMellinIntegrand_eq_upper
        2 (0 : Complex) hx hu
  rw [hOrigin, <- Ioc_union_Ioi_eq_Ioi hx.le]
  have hUnion :=
    setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi hLow hHigh
  simp only [zero_sub] at hUnion
  rw [hUnion, hLowValue, hHighValue]

theorem norm_quadraticCharacterEvenOriginCorrection_le
    {x : Real} (hx : 1 < x) :
    norm (quadraticCharacterEvenOriginCorrection 2 x) <=
      x ^ (-(2 : Real)) +
        (x ^ (-(2 : Real)) / 2) *
          Inv.inv (Real.log x) := by
  rw [quadraticCharacterEvenOriginCorrection_eq hx]
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hPowNonneg : 0 <= x ^ (-(2 : Real)) :=
    Real.rpow_nonneg hxPos.le _
  have hTailEq :=
    Robin1984.robinCpowLogTail_ofReal_eq
      (-(2 : Real)) 1 hx
  have hTailNonneg :=
    Robin1984.robinCpowLogTail_ofReal_re_nonneg
      (-(2 : Real)) 1 hx
  have hTailBound :=
    Robin1984.robinCpowLogTail_ofReal_re_le
      (a := -(2 : Real)) (by norm_num) 1 hx
  have hIntegralNonneg :
      0 <= integral (volume.restrict (Ioi x)) (fun t : Real =>
        t ^ (-(2 : Real) - 1) *
          Inv.inv (Real.log t ^ (1 : Nat))) := by
    simpa only [hTailEq, Complex.ofReal_re] using hTailNonneg
  have hTailNorm :
      norm (Robin1984.robinCpowLogTail
          ((-(2 : Real) : Real) : Complex) 1 x) =
        (Robin1984.robinCpowLogTail
          ((-(2 : Real) : Real) : Complex) 1 x).re := by
    rw [hTailEq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hIntegralNonneg]
    simp only [Complex.ofReal_re]
  calc
    norm (((x ^ (-(2 : Real)) : Real) : Complex) +
        Robin1984.robinCpowLogTail
          ((-(2 : Real) : Real) : Complex) 1 x) <=
      norm (((x ^ (-(2 : Real)) : Real) : Complex)) +
        norm (Robin1984.robinCpowLogTail
          ((-(2 : Real) : Real) : Complex) 1 x) := norm_add_le _ _
    _ = x ^ (-(2 : Real)) +
        (Robin1984.robinCpowLogTail
          ((-(2 : Real) : Real) : Complex) 1 x).re := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hPowNonneg, hTailNorm]
    _ <= x ^ (-(2 : Real)) +
        (x ^ (-(2 : Real)) / 2) *
          Inv.inv (Real.log x) := by
      apply add_le_add le_rfl
      simpa only [neg_div_neg_eq, pow_one] using hTailBound


def quadraticNegativeOddAtom (n k : Nat) (t : Real) : Real :=
  Robin1984.robinRealWeight n t * (1 / t) ^ (2 * k + 1) /
    (2 * (k : Real) + 1)

theorem quadraticNegativeOddAtom_bounds
    (n k : Nat) {t : Real} (ht : 2 <= t) :
    And (0 <= quadraticNegativeOddAtom n k t)
      (quadraticNegativeOddAtom n k t <=
        (1 / 2 : Real) ^ (k + 1) * Robin1984.robinRealWeight n t) := by
  have hWeight : 0 <= Robin1984.robinRealWeight n t :=
    Robin1984.robinRealWeight_nonneg (by linarith)
  have hRatio : 1 / t <= (1 / 2 : Real) :=
    one_div_le_one_div_of_le (by norm_num) ht
  have hRatioNonneg : 0 <= 1 / t := by positivity
  have hHalfNonneg : 0 <= (1 / 2 : Real) := by norm_num
  have hPowerBase :
      (1 / t) ^ (2 * k + 1) <= (1 / 2 : Real) ^ (2 * k + 1) := by
    gcongr
  have hExponent : k + 1 <= 2 * k + 1 := by omega
  have hPowerExponent :
      (1 / 2 : Real) ^ (2 * k + 1) <= (1 / 2 : Real) ^ (k + 1) :=
    pow_le_pow_of_le_one hHalfNonneg (by norm_num) hExponent
  have hPower :
      (1 / t) ^ (2 * k + 1) <= (1 / 2 : Real) ^ (k + 1) :=
    hPowerBase.trans hPowerExponent
  have hDen : 1 <= 2 * (k : Real) + 1 := by
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  refine And.intro ?_ ?_
  . unfold quadraticNegativeOddAtom
    positivity
  . have hDiv :
        (1 / t) ^ (2 * k + 1) / (2 * (k : Real) + 1) <=
          (1 / t) ^ (2 * k + 1) := by
      have h := div_le_div_of_nonneg_left
        (pow_nonneg hRatioNonneg (2 * k + 1))
        (by norm_num : (0 : Real) < 1) hDen
      simpa only [div_one] using h
    unfold quadraticNegativeOddAtom
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left (hDiv.trans hPower) hWeight).trans_eq
      (mul_comm _ _)

theorem integrableOn_quadraticNegativeOddAtom
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) (k : Nat) :
    IntegrableOn (quadraticNegativeOddAtom n k) (Ioi x) := by
  have hxOne : 1 < x := by linarith
  have hMeas : Measurable (quadraticNegativeOddAtom n k) := by
    unfold quadraticNegativeOddAtom Robin1984.robinRealWeight
    fun_prop
  apply ((Robin1984.integrableOn_robinRealWeight hn hxOne).const_mul
    ((1 / 2 : Real) ^ (k + 1))).mono' hMeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hBounds := quadraticNegativeOddAtom_bounds n k
    (le_trans hx (le_of_lt ht))
  rw [Real.norm_eq_abs, abs_of_nonneg hBounds.1]
  exact hBounds.2

theorem summable_integral_norm_quadraticNegativeOddAtoms
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    Summable (fun k : Nat => integral (volume.restrict (Ioi x))
      (fun t : Real => norm (quadraticNegativeOddAtom n k t : Complex))) := by
  have hxOne : 1 < x := by linarith
  have hWeight := Robin1984.integrableOn_robinRealWeight hn hxOne
  have hGeom : Summable (fun k : Nat => (1 / 2 : Real) ^ (k + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_norm_lt_one
        (by norm_num : norm (1 / 2 : Real) < 1)).mul_right (1 / 2)
  have hBound : forall k : Nat,
      integral (volume.restrict (Ioi x))
          (fun t : Real => norm (quadraticNegativeOddAtom n k t : Complex)) <=
        (1 / 2 : Real) ^ (k + 1) *
          integral (volume.restrict (Ioi x)) (Robin1984.robinRealWeight n) := by
    intro k
    have hF : IntegrableOn
        (fun t : Real => (quadraticNegativeOddAtom n k t : Complex)) (Ioi x) :=
      (integrableOn_quadraticNegativeOddAtom hn hx k).ofReal
    calc
      integral (volume.restrict (Ioi x))
          (fun t : Real => norm (quadraticNegativeOddAtom n k t : Complex)) <=
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (1 / 2 : Real) ^ (k + 1) *
            Robin1984.robinRealWeight n t) := by
          apply integral_mono_ae hF.norm (hWeight.const_mul _)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have hBounds := quadraticNegativeOddAtom_bounds n k
            (le_trans hx (le_of_lt ht))
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hBounds.1]
          exact hBounds.2
      _ = _ := integral_const_mul _ _
  exact Summable.of_nonneg_of_le
    (fun k => integral_nonneg
      (fun t => norm_nonneg (quadraticNegativeOddAtom n k t : Complex)))
    hBound (hGeom.mul_right _)

theorem quadraticNegativeOddAtom_eq_kernel_integrand
    (n k : Nat) {t : Real} (ht : 1 < t) :
    ((t : Complex) ^ (-(2 * (k : Complex) + 1) - (n : Complex) - 1) *
        (((n : Real) * Real.log t + 1) / (Real.log t) ^ 2 : Real)) /
          (2 * (k : Complex) + 1) =
      (quadraticNegativeOddAtom n k t : Complex) := by
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  have hPower :
      t ^ (-(2 * (k : Real) + 1) - (n : Real) - 1) =
        t ^ (-(n : Real) - 1) * (1 / t) ^ (2 * k + 1) := by
    rw [show -(2 * (k : Real) + 1) - (n : Real) - 1 =
        (-(n : Real) - 1) + (-(1 : Real)) * (2 * (k : Real) + 1) by ring,
      Real.rpow_add htPos, show 2 * (k : Real) + 1 =
        ((2 * k + 1 : Nat) : Real) by norm_num,
      Real.rpow_mul htPos.le, Real.rpow_natCast, Real.rpow_neg_one]
    simp only [one_div]
  have hExponent :
      -(2 * (k : Complex) + 1) - (n : Complex) - 1 =
        ((-(2 * (k : Real) + 1) - (n : Real) - 1 : Real) : Complex) := by
    push_cast
    ring
  rw [hExponent, <- Complex.ofReal_cpow htPos.le, hPower]
  unfold quadraticNegativeOddAtom Robin1984.robinRealWeight
  push_cast
  ring

theorem quadraticNegativeOddKernel_eq_integral
    (n k : Nat) {x : Real} (hx : 1 < x) :
    Robin1984.robinZeroKernel n (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1) =
      integral (volume.restrict (Ioi x))
        (fun t : Real => (quadraticNegativeOddAtom n k t : Complex)) := by
  unfold Robin1984.robinZeroKernel
  rw [<- integral_div]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  exact quadraticNegativeOddAtom_eq_kernel_integrand n k (lt_trans hx ht)

theorem norm_quadraticNegativeOddKernel_le
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) (k : Nat) :
    norm (Robin1984.robinZeroKernel n (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1)) <=
      (1 / 2 : Real) ^ (k + 1) *
        integral (volume.restrict (Ioi x)) (Robin1984.robinRealWeight n) := by
  rw [quadraticNegativeOddKernel_eq_integral n k (by linarith)]
  calc
    norm (integral (volume.restrict (Ioi x))
        (fun t : Real => (quadraticNegativeOddAtom n k t : Complex))) <=
      integral (volume.restrict (Ioi x))
        (fun t : Real => norm (quadraticNegativeOddAtom n k t : Complex)) :=
      norm_integral_le_integral_norm _
    _ <= _ := by
      have hWeight := Robin1984.integrableOn_robinRealWeight hn (by linarith : 1 < x)
      have hF : IntegrableOn
          (fun t : Real => (quadraticNegativeOddAtom n k t : Complex)) (Ioi x) :=
        (integrableOn_quadraticNegativeOddAtom hn hx k).ofReal
      apply integral_mono_ae hF.norm (hWeight.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hBounds := quadraticNegativeOddAtom_bounds n k
        (le_trans hx (le_of_lt ht))
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hBounds.1]
      exact hBounds.2
    _ = _ := integral_const_mul _ _

theorem summable_quadraticNegativeOddKernels
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    Summable (fun k : Nat =>
      Robin1984.robinZeroKernel n (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1)) := by
  have hGeom : Summable (fun k : Nat => (1 / 2 : Real) ^ (k + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_norm_lt_one
        (by norm_num : norm (1 / 2 : Real) < 1)).mul_right (1 / 2)
  have hMajor := hGeom.mul_right
    (integral (volume.restrict (Ioi x)) (Robin1984.robinRealWeight n))
  exact hMajor.of_norm_bounded
    (norm_quadraticNegativeOddKernel_le hn hx)

theorem norm_tsum_quadraticNegativeOddKernels_le
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    norm (tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1))) <=
      integral (volume.restrict (Ioi x)) (Robin1984.robinRealWeight n) := by
  have hSeries := summable_quadraticNegativeOddKernels hn hx
  have hNormSeries := hSeries.norm
  have hGeomSum : HasSum (fun k : Nat => (1 / 2 : Real) ^ (k + 1)) 1 := by
    have h := (hasSum_geometric_of_norm_lt_one
      (by norm_num : norm (1 / 2 : Real) < 1)).mul_left (1 / 2 : Real)
    norm_num at h
    simpa only [pow_succ, mul_comm] using h
  have hMajor := hGeomSum.summable.mul_right
    (integral (volume.restrict (Ioi x)) (Robin1984.robinRealWeight n))
  calc
    norm (tsum (fun k : Nat =>
        Robin1984.robinZeroKernel n (-(2 * (k : Complex) + 1)) x /
          (2 * (k : Complex) + 1))) <=
      tsum (fun k : Nat =>
        norm (Robin1984.robinZeroKernel n (-(2 * (k : Complex) + 1)) x /
          (2 * (k : Complex) + 1))) :=
      norm_tsum_le_tsum_norm hNormSeries
    _ <= tsum (fun k : Nat =>
        (1 / 2 : Real) ^ (k + 1) *
          integral (volume.restrict (Ioi x)) (Robin1984.robinRealWeight n)) :=
      hNormSeries.tsum_le_tsum
        (norm_quadraticNegativeOddKernel_le hn hx) hMajor
    _ = (tsum (fun k : Nat => (1 / 2 : Real) ^ (k + 1))) *
        integral (volume.restrict (Ioi x)) (Robin1984.robinRealWeight n) := by
      rw [tsum_mul_right]
    _ = _ := by rw [hGeomSum.tsum_eq, one_mul]

end

end RobinBV.NumberField
