import RobinBV.NumberField.Proof.QuadraticDedekindNicolasCompact

/-!
# Large-tail quadratic Dedekind continuation

Focused infrastructure for the quadratic Dedekind Nicolas-Landau Omega theorem.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section
theorem quadraticDedekindPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 < s.re) :
    quadraticDedekindPsiMellinTailContinuationFilled D s =
      quadraticDedekindPsiMellinTailContinuation D 3 s := by
  have hsZero : Not (s = 0) := by
    intro hEq
    subst s
    norm_num at hs
  have hsOne : Not (s = 1) := by
    intro hEq
    subst s
    norm_num at hs
  have hZeta : Not (quadraticDedekindZetaContinuation D s = 0) := by
    unfold quadraticDedekindZetaContinuation
    exact mul_ne_zero
      (riemannZeta_ne_zero_of_one_lt_re hs)
      (D.character.LFunction_ne_zero_of_one_le_re
        (Or.inl (quadraticCharacter_ne_one D)) hs.le)
  exact (quadraticDedekindPsiMellinTailContinuation_eq_filled
    D hsZero hsOne hZeta).symm

theorem abs_quadraticDedekindPsiError_le_linear
    (D : NumberField.OddFundamentalDiscriminant)
    {t : Real} (ht : 0 <= t) :
    abs (quadraticDedekindPsiError D t) <=
      (2 * (Real.log 4 + 4) + 1) * t := by
  have hStepNonneg : 0 <= quadraticDedekindMellinStep D t :=
    quadraticDedekindMellinStep_nonneg D t
  have hPsi := Chebyshev.psi_le_const_mul_self ht
  have hStep : quadraticDedekindMellinStep D t <=
      2 * (Real.log 4 + 4) * t := by
    calc
      quadraticDedekindMellinStep D t <= 2 * Chebyshev.psi t :=
        quadraticDedekindMellinStep_le_two_psi D t
      _ <= 2 * ((Real.log 4 + 4) * t) :=
        mul_le_mul_of_nonneg_left hPsi (by norm_num)
      _ = 2 * (Real.log 4 + 4) * t := by ring
  unfold quadraticDedekindPsiError
  calc
    abs (quadraticDedekindMellinStep D t - t) <=
        abs (quadraticDedekindMellinStep D t) + abs t := abs_sub _ _
    _ = quadraticDedekindMellinStep D t + t := by
      rw [abs_of_nonneg hStepNonneg, abs_of_nonneg ht]
    _ <= 2 * (Real.log 4 + 4) * t + t := add_le_add hStep le_rfl
    _ = (2 * (Real.log 4 + 4) + 1) * t := by ring

theorem norm_quadraticDedekindPsiMellinTailContinuationFilled_le
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 < s.re) :
    norm (quadraticDedekindPsiMellinTailContinuationFilled D s) <=
      (2 * (Real.log 4 + 4) + 1) *
        (3 ^ (1 - s.re) / (s.re - 1)) := by
  let c : Real := 2 * (Real.log 4 + 4) + 1
  have hcPos : 0 < c := by
    dsimp [c]
    positivity
  have hPowerIntegrable : IntegrableOn
      (fun t : Real => t ^ (-s.re)) (Ioi (3 : Real)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hMajorantIntegrable : IntegrableOn
      (fun t : Real => c * t ^ (-s.re)) (Ioi (3 : Real)) :=
    hPowerIntegrable.const_mul c
  have hIntegralEq :
      integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          (quadraticDedekindPsiError D t : Complex) *
            (t : Complex) ^ (-(s + 1))) =
        quadraticDedekindPsiMellinTailContinuationFilled D s := by
    calc
      integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          (quadraticDedekindPsiError D t : Complex) *
            (t : Complex) ^ (-(s + 1))) =
          quadraticDedekindPsiMellinTailContinuation D 3 s :=
        quadraticDedekindPsiErrorTailMellin_eq_continuation D (by norm_num) hs
      _ = quadraticDedekindPsiMellinTailContinuationFilled D s :=
        (quadraticDedekindPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re
          D hs).symm
  have hNormIntegral :
      norm (integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          (quadraticDedekindPsiError D t : Complex) *
            (t : Complex) ^ (-(s + 1)))) <=
        integral (volume.restrict (Ioi (3 : Real)))
          (fun t : Real => c * t ^ (-s.re)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hMajorantIntegrable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htPos : 0 < t := lt_trans (by norm_num) ht
    have hError := abs_quadraticDedekindPsiError_le_linear D htPos.le
    have hPowNonneg : 0 <= t ^ (-(s + 1)).re :=
      Real.rpow_nonneg htPos.le _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos htPos]
    calc
      abs (quadraticDedekindPsiError D t) * t ^ (-(s + 1)).re <=
          (c * t) * t ^ (-(s + 1)).re :=
        mul_le_mul_of_nonneg_right (by simpa [c] using hError) hPowNonneg
      _ = c * t ^ (-s.re) := by
        calc
          (c * t) * t ^ (-(s + 1)).re =
              c * (t ^ (1 : Real) * t ^ (-(s + 1)).re) := by
            rw [Real.rpow_one]
            ring
          _ = c * t ^ ((1 : Real) + (-(s + 1)).re) := by
            rw [Real.rpow_add htPos]
          _ = c * t ^ (-s.re) := by
            congr 2
            simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
            ring
  rw [<- hIntegralEq]
  calc
    norm (integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        (quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-(s + 1)))) <=
        integral (volume.restrict (Ioi (3 : Real)))
          (fun t : Real => c * t ^ (-s.re)) := hNormIntegral
    _ = c * (-3 ^ (-s.re + 1) / (-s.re + 1)) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
    _ = (2 * (Real.log 4 + 4) + 1) *
        (3 ^ (1 - s.re) / (s.re - 1)) := by
      dsimp [c]
      have hDen : Not (s.re - 1 = 0) := ne_of_gt (sub_pos.mpr hs)
      have hDenLeft : Not (-s.re + 1 = 0) := by linarith
      field_simp [hDen, hDenLeft]
      ring

theorem norm_quadraticDedekindJShiftNumeratorFilled_le_of_re_le_threeQuarter
    (D : NumberField.OddFundamentalDiscriminant)
    {u : Real} (hu : 1 < u) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) :
    norm (quadraticDedekindJShiftNumeratorFilled D z u) <=
      5 * (2 * (Real.log 4 + 4) + 1) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 < s0.re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hDen1 : (1 / 4 : Real) < s1.re - 1 := by
    dsimp [s1, s0]
    linarith
  have hShiftRaw := norm_quadraticDedekindPsiMellinTailContinuationFilled_le D hs1
  have hShiftNumerator : (3 : Real) ^ (1 - s1.re) <=
      (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [s1, s0]
    linarith
  have hShiftPowerNonneg : 0 <= (3 : Real) ^ (1 - s1.re) :=
    Real.rpow_nonneg (by norm_num) _
  have hShiftFraction : (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
      4 * (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
          (3 : Real) ^ (1 - s1.re) / (1 / 4 : Real) :=
        div_le_div_of_nonneg_left hShiftPowerNonneg (by norm_num) hDen1.le
      _ = 4 * (3 : Real) ^ (1 - s1.re) := by ring
      _ <= 4 * (3 : Real) ^ (-u + (3 / 4 : Real)) :=
        mul_le_mul_of_nonneg_left hShiftNumerator (by norm_num)
  have hShift : norm (quadraticDedekindPsiMellinTailContinuationFilled D s1) <=
      4 * (2 * (Real.log 4 + 4) + 1) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      norm (quadraticDedekindPsiMellinTailContinuationFilled D s1) <=
          (2 * (Real.log 4 + 4) + 1) *
            ((3 : Real) ^ (1 - s1.re) / (s1.re - 1)) := hShiftRaw
      _ <= (2 * (Real.log 4 + 4) + 1) *
          (4 * (3 : Real) ^ (-u + (3 / 4 : Real))) :=
        mul_le_mul_of_nonneg_left hShiftFraction (by positivity)
      _ = 4 * (2 * (Real.log 4 + 4) + 1) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring
  have hBaseRaw := norm_quadraticDedekindPsiMellinTailContinuationFilled_le D hs0
  have hBase : norm (quadraticDedekindPsiMellinTailContinuationFilled D s0) <=
      (2 * (Real.log 4 + 4) + 1) * (3 : Real) ^ (-u) := by
    have hPowNonneg : 0 <= (3 : Real) ^ (-u) :=
      Real.rpow_nonneg (by norm_num) _
    have hS0Exponent : 1 - s0.re = -u := by
      dsimp [s0]
      ring
    have hS0Denominator : s0.re - 1 = u := by
      dsimp [s0]
      ring
    rw [hS0Exponent, hS0Denominator] at hBaseRaw
    calc
      norm (quadraticDedekindPsiMellinTailContinuationFilled D s0) <=
          (2 * (Real.log 4 + 4) + 1) * ((3 : Real) ^ (-u) / u) := hBaseRaw
      _ <= (2 * (Real.log 4 + 4) + 1) * ((3 : Real) ^ (-u) / 1) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hPowNonneg zero_lt_one hu.le)
          (by positivity)
      _ = (2 * (Real.log 4 + 4) + 1) * (3 : Real) ^ (-u) := by ring
  have hPowerNorm : norm ((3 : Complex) ^ z) =
      (3 : Real) ^ z.re := by
    change norm (((3 : Real) : Complex) ^ z) = (3 : Real) ^ z.re
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hPowerProduct : norm ((3 : Complex) ^ z *
      quadraticDedekindPsiMellinTailContinuationFilled D s0) <=
      (2 * (Real.log 4 + 4) + 1) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    rw [norm_mul, hPowerNorm]
    calc
      (3 : Real) ^ z.re *
          norm (quadraticDedekindPsiMellinTailContinuationFilled D s0) <=
          (3 : Real) ^ z.re *
            ((2 * (Real.log 4 + 4) + 1) * (3 : Real) ^ (-u)) :=
        mul_le_mul_of_nonneg_left hBase
          (Real.rpow_nonneg (by norm_num) _)
      _ = (2 * (Real.log 4 + 4) + 1) *
          ((3 : Real) ^ z.re * (3 : Real) ^ (-u)) := by ring
      _ = (2 * (Real.log 4 + 4) + 1) * (3 : Real) ^ (z.re + (-u)) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 3)]
      _ = (2 * (Real.log 4 + 4) + 1) * (3 : Real) ^ (z.re - u) := by
        congr 2
      _ <= (2 * (Real.log 4 + 4) + 1) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
  unfold quadraticDedekindJShiftNumeratorFilled
  change norm (quadraticDedekindPsiMellinTailContinuationFilled D s1 -
      (3 : Complex) ^ z * quadraticDedekindPsiMellinTailContinuationFilled D s0) <= _
  calc
    norm (quadraticDedekindPsiMellinTailContinuationFilled D s1 -
        (3 : Complex) ^ z * quadraticDedekindPsiMellinTailContinuationFilled D s0) <=
        norm (quadraticDedekindPsiMellinTailContinuationFilled D s1) +
          norm ((3 : Complex) ^ z *
            quadraticDedekindPsiMellinTailContinuationFilled D s0) := norm_sub_le _ _
    _ <= 4 * (2 * (Real.log 4 + 4) + 1) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) +
        (2 * (Real.log 4 + 4) + 1) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) :=
      add_le_add hShift hPowerProduct
    _ = 5 * (2 * (Real.log 4 + 4) + 1) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring

def quadraticDedekindJLargeMajorantAtDistance (d u : Real) : Real :=
  (5 / d) * (2 * (Real.log 4 + 4) + 1) * (u + 1) *
    (3 : Real) ^ (-u + (3 / 4 : Real))

theorem quadraticDedekindJLargeMajorantAtDistance_integrableOn
    {d : Real} (hd : 0 < d) :
    IntegrableOn (quadraticDedekindJLargeMajorantAtDistance d)
      (Ioi (1 : Real)) := by
  have hLog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hExp : IntegrableOn
      (fun u : Real => Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : Real)) (s := (0 : Real)) (b := Real.log 3)
      (by norm_num) (by norm_num) hLog
    have hSubset : Ioi (1 : Real) <= Ioi (0 : Real) := by
      intro u hu
      exact zero_lt_one.trans (mem_Ioi.mp hu)
    apply (h.mono_set hSubset).congr_fun _ measurableSet_Ioi
    intro u hu
    simp
  have hUExp : IntegrableOn
      (fun u : Real => u * Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : Real)) (s := (1 : Real)) (b := Real.log 3)
      (by norm_num) (by norm_num) hLog
    have hSubset : Ioi (1 : Real) <= Ioi (0 : Real) := by
      intro u hu
      exact zero_lt_one.trans (mem_Ioi.mp hu)
    apply (h.mono_set hSubset).congr_fun _ measurableSet_Ioi
    intro u hu
    simp
  have hLinear : IntegrableOn
      (fun u : Real => (u + 1) * Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    apply (hUExp.add hExp).congr_fun _ measurableSet_Ioi
    intro u hu
    change u * Real.exp (-(Real.log 3) * u) +
      Real.exp (-(Real.log 3) * u) =
        (u + 1) * Real.exp (-(Real.log 3) * u)
    ring
  have hScaled : IntegrableOn
      (fun u : Real =>
        (((5 / d) * (2 * (Real.log 4 + 4) + 1)) *
          Real.exp (Real.log 3 * (3 / 4 : Real))) *
          ((u + 1) * Real.exp (-(Real.log 3) * u)))
      (Ioi (1 : Real)) :=
    hLinear.const_mul
      (((5 / d) * (2 * (Real.log 4 + 4) + 1)) *
        Real.exp (Real.log 3 * (3 / 4 : Real)))
  apply hScaled.congr_fun _ measurableSet_Ioi
  intro u hu
  unfold quadraticDedekindJLargeMajorantAtDistance
  rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 3)]
  rw [show Real.log 3 * (-u + (3 / 4 : Real)) =
      Real.log 3 * (3 / 4 : Real) + (-(Real.log 3) * u) by ring]
  rw [Real.exp_add]
  ring

theorem norm_quadraticDedekindJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge
    (D : NumberField.OddFundamentalDiscriminant)
    {d u : Real} (hd : 0 < d) (hu : 1 < u) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) (hzNorm : d <= norm z) :
    norm (quadraticDedekindJMellinShiftIntegrandFilled D z u) <=
      quadraticDedekindJLargeMajorantAtDistance d u := by
  have hzNe : Not (z = 0) := by
    intro hEq
    rw [hEq, norm_zero] at hzNorm
    linarith
  have hNumerator :=
    norm_quadraticDedekindJShiftNumeratorFilled_le_of_re_le_threeQuarter
      D hu hzRe
  have hInv : norm (Inv.inv z) <= 1 / d := by
    rw [norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le hd hzNorm
  have huPos : 0 < u + 1 := by linarith
  unfold quadraticDedekindJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzNe]
  unfold slope
  change norm (((u + 1 : Real) : Complex) *
      (Inv.inv (z - 0) *
        (quadraticDedekindJShiftNumeratorFilled D z u -
          quadraticDedekindJShiftNumeratorFilled D 0 u))) <=
    quadraticDedekindJLargeMajorantAtDistance d u
  rw [quadraticDedekindJShiftNumeratorFilled_zero]
  simp only [smul_eq_mul, vsub_eq_sub, sub_zero]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huPos,
    norm_mul]
  calc
    (u + 1) * (norm (Inv.inv z) *
        norm (quadraticDedekindJShiftNumeratorFilled D z u)) <=
        (u + 1) * ((1 / d) *
          (5 * (2 * (Real.log 4 + 4) + 1) *
            (3 : Real) ^ (-u + (3 / 4 : Real)))) := by
      apply mul_le_mul_of_nonneg_left _ huPos.le
      exact mul_le_mul hInv hNumerator (norm_nonneg _)
        (by positivity)
    _ = quadraticDedekindJLargeMajorantAtDistance d u := by
      unfold quadraticDedekindJLargeMajorantAtDistance
      field_simp [hd.ne']


theorem quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    (D : NumberField.OddFundamentalDiscriminant)
    {center : Complex} {R d : Real} (hRPos : 0 < R) (hd : 0 < d)
    (hGeometry : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (z.re <= (3 / 4 : Real)) (d <= norm z)) :
    AnalyticAt Complex (quadraticDedekindJShiftedComplexContinuationFilledLarge D)
      center := by
  have hPointData : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          And (Not (z = 0))
            (And (Not ((((u + 1 : Real) : Complex) - z) = 0))
              (Not (quadraticDedekindZetaPoleFactor D
                (((u + 1 : Real) : Complex) - z) = 0))) := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGeometry := hGeometry z hzBall
    have hzNe : Not (z = 0) := by
      intro hEq
      rw [hEq, norm_zero] at hzGeometry
      linarith
    have hsRe : 1 < ((((u + 1 : Real) : Complex) - z).re) := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [hzGeometry.1]
    have hsZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hFactor : Not (quadraticDedekindZetaPoleFactor D
        (((u + 1 : Real) : Complex) - z) = 0) :=
      quadraticDedekindZetaPoleFactor_ne_zero_of_one_le_re D hsRe.le
    exact And.intro hzNe (And.intro hsZero hFactor)
  have hKernelBound : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          norm (quadraticDedekindJMellinShiftIntegrandFilled D z u) <=
            quadraticDedekindJLargeMajorantAtDistance d u := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGeometry := hGeometry z hzBall
    exact norm_quadraticDedekindJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge D
      hd hu hzGeometry.1 hzGeometry.2
  have hContinuousU : forall z : Complex,
      Membership.mem (Metric.closedBall center (R / 2)) z ->
        ContinuousOn (fun u : Real =>
          quadraticDedekindJMellinShiftIntegrandFilled D z u) (Ioi (1 : Real)) := by
    intro z hz u hu
    have hData := hPointData u (mem_Ioi.mp hu) z hz
    have hJoint := quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne D
      (by linarith [mem_Ioi.mp hu] : 0 <= u)
      hData.1 hData.2.1 hData.2.2
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        quadraticDedekindJMellinShiftIntegrandFilled D z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hAnalytic : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          AnalyticAt Complex (fun w : Complex =>
            quadraticDedekindJMellinShiftIntegrandFilled D w u) z := by
    intro u hu z hz
    have hData := hPointData u hu z hz
    exact
      quadraticDedekindJMellinShiftIntegrandFilled_analyticAt D
        (by linarith [hu] : 0 <= u) hData.2.1 hData.2.2
  have hDerivativeMeasurable : forall z : Complex,
      Membership.mem (Metric.ball center (R / 4)) z ->
        AEStronglyMeasurable (fun u : Real =>
          deriv (fun w : Complex =>
            quadraticDedekindJMellinShiftIntegrandFilled D w u) z)
          (volume.restrict (Ioi (1 : Real))) := by
    intro z hz
    let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
      slope (fun w : Complex => quadraticDedekindJMellinShiftIntegrandFilled D w u)
        z (z + Robin1984.nicolasCompactStripDerivativeStep R n)
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      linarith
    have hShiftClosed : forall n : Nat,
        Membership.mem (Metric.closedBall center (R / 2))
          (z + Robin1984.nicolasCompactStripDerivativeStep R n) := by
      intro n
      rw [Metric.mem_closedBall]
      calc
        dist (z + Robin1984.nicolasCompactStripDerivativeStep R n) center <=
            dist (z + Robin1984.nicolasCompactStripDerivativeStep R n) z +
              dist z center := dist_triangle _ z _
        _ = norm (Robin1984.nicolasCompactStripDerivativeStep R n) +
              dist z center := by rw [dist_eq_norm]; simp
        _ <= R / 8 + R / 4 :=
          (add_lt_add_of_le_of_lt
            (Robin1984.norm_nicolasCompactStripDerivativeStep_le hRPos n) hzDist).le
        _ <= R / 2 := by linarith
    have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
        (volume.restrict (Ioi (1 : Real))) := by
      intro n
      have hShift := hContinuousU _ (hShiftClosed n)
      have hBase := hContinuousU z hzClosed
      have hShiftMeas : AEStronglyMeasurable
          (fun u : Real => quadraticDedekindJMellinShiftIntegrandFilled D
            (z + Robin1984.nicolasCompactStripDerivativeStep R n) u)
          (volume.restrict (Ioi (1 : Real))) :=
        hShift.aestronglyMeasurable measurableSet_Ioi
      have hBaseMeas : AEStronglyMeasurable
          (fun u : Real => quadraticDedekindJMellinShiftIntegrandFilled D z u)
          (volume.restrict (Ioi (1 : Real))) :=
        hBase.aestronglyMeasurable measurableSet_Ioi
      have hEq : slopeSeq n = fun u : Real =>
          Inv.inv ((z + Robin1984.nicolasCompactStripDerivativeStep R n) - z) *
            (quadraticDedekindJMellinShiftIntegrandFilled D
                (z + Robin1984.nicolasCompactStripDerivativeStep R n) u -
              quadraticDedekindJMellinShiftIntegrandFilled D z u) := by
        funext u
        dsimp [slopeSeq]
        unfold slope
        simp only [smul_eq_mul, vsub_eq_sub]
      rw [hEq]
      exact ((hShiftMeas.sub hBaseMeas).const_mul
        (Inv.inv ((z + Robin1984.nicolasCompactStripDerivativeStep R n) - z))).aemeasurable
    have hStepWithin : Tendsto (Robin1984.nicolasCompactStripDerivativeStep R) atTop
        (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact And.intro (Robin1984.nicolasCompactStripDerivativeStep_tendsto_zero R)
        (Eventually.of_forall (fun n : Nat =>
          Set.mem_compl_singleton_iff.mpr
            (Robin1984.nicolasCompactStripDerivativeStep_ne_zero hRPos n)))
    have hTendsto : Filter.Eventually
        (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
          (nhds (deriv (fun w : Complex =>
            quadraticDedekindJMellinShiftIntegrandFilled D w u) z)))
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hSlope := (hAnalytic u hu z hzClosed).differentiableAt.hasDerivAt
        |>.tendsto_slope_zero.comp hStepWithin
      change Tendsto (fun n : Nat =>
        Inv.inv (Robin1984.nicolasCompactStripDerivativeStep R n) *
          (quadraticDedekindJMellinShiftIntegrandFilled D
              (z + Robin1984.nicolasCompactStripDerivativeStep R n) u -
            quadraticDedekindJMellinShiftIntegrandFilled D z u))
        atTop (nhds (deriv (fun w : Complex =>
          quadraticDedekindJMellinShiftIntegrandFilled D w u) z)) at hSlope
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
      exact hSlope
    exact (aemeasurable_of_tendsto_metrizable_ae'
      hMeas hTendsto).aestronglyMeasurable
  have hDerivativeBound : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.ball center (R / 4)) z ->
          norm (deriv (fun w : Complex =>
            quadraticDedekindJMellinShiftIntegrandFilled D w u) z) <=
              (8 / R) * quadraticDedekindJLargeMajorantAtDistance d u := by
    intro u hu z hz
    let f : Complex -> Complex := fun w =>
      quadraticDedekindJMellinShiftIntegrandFilled D w u
    let r : Real := R / 4
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hSmallSubset : Metric.ball z r <=
        Metric.closedBall center (R / 2) := by
      intro w hw
      rw [Metric.mem_ball] at hw
      rw [Metric.mem_closedBall]
      calc
        dist w center <= dist w z + dist z center := dist_triangle _ z _
        _ <= R / 4 + R / 4 := by
          dsimp [r] at hw
          exact (add_lt_add hw hzDist).le
        _ <= R / 2 := by linarith
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      apply hSmallSubset
      exact Metric.mem_ball_self (by dsimp [r]; linarith)
    have hDiff : DifferentiableOn Complex f (Metric.ball z r) := by
      intro w hw
      exact (hAnalytic u hu w (hSmallSubset hw)).differentiableAt.differentiableWithinAt
    have hMaps : MapsTo f (Metric.ball z r)
        (Metric.closedBall (f z)
          (2 * quadraticDedekindJLargeMajorantAtDistance d u)) := by
      intro w hw
      have hwBound := hKernelBound u hu w (hSmallSubset hw)
      have hzBound := hKernelBound u hu z hzClosed
      rw [Metric.mem_closedBall]
      calc
        dist (f w) (f z) <= norm (f w) + norm (f z) := by
          simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
        _ <= quadraticDedekindJLargeMajorantAtDistance d u +
            quadraticDedekindJLargeMajorantAtDistance d u :=
          add_le_add hwBound hzBound
        _ = 2 * quadraticDedekindJLargeMajorantAtDistance d u := by ring
    have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
      hDiff hMaps (by dsimp [r]; linarith)
    change norm (deriv f z) <=
      (8 / R) * quadraticDedekindJLargeMajorantAtDistance d u
    calc
      norm (deriv f z) <=
          (2 * quadraticDedekindJLargeMajorantAtDistance d u) / r := hCauchy
      _ = (8 / R) * quadraticDedekindJLargeMajorantAtDistance d u := by
        dsimp [r]
        field_simp [hRPos.ne']
        ring
  let s : Set Complex := Metric.ball center (R / 4)
  have hHasDeriv : forall z : Complex, Membership.mem s z ->
      HasDerivAt (quadraticDedekindJShiftedComplexContinuationFilledLarge D)
        (integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
          deriv (fun w : Complex =>
            quadraticDedekindJMellinShiftIntegrandFilled D w u) z)) z := by
    intro z hz
    let F : Complex -> Real -> Complex := fun w => fun u =>
      quadraticDedekindJMellinShiftIntegrandFilled D w u
    let F' : Complex -> Real -> Complex := fun w => fun u =>
      deriv (fun v : Complex => quadraticDedekindJMellinShiftIntegrandFilled D v u) w
    have hsNhd : Membership.mem (nhds z) s :=
      Metric.isOpen_ball.mem_nhds hz
    have hFMeas : Filter.Eventually
        (fun w : Complex => AEStronglyMeasurable (F w)
          (volume.restrict (Ioi (1 : Real)))) (nhds z) := by
      filter_upwards [hsNhd] with w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [F]
      exact (hContinuousU w hwClosed).aestronglyMeasurable measurableSet_Ioi
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      have hzDist : dist z center < R / 4 := by
        simpa [s, Metric.mem_ball] using hz
      linarith
    have hFInt : Integrable (F z)
        (volume.restrict (Ioi (1 : Real))) := by
      apply Integrable.mono'
        (quadraticDedekindJLargeMajorantAtDistance_integrableOn hd)
        ((hContinuousU z hzClosed).aestronglyMeasurable measurableSet_Ioi)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hKernelBound u hu z hzClosed
    have hF'Meas : AEStronglyMeasurable (F' z)
        (volume.restrict (Ioi (1 : Real))) := by
      dsimp [F']
      exact hDerivativeMeasurable z hz
    have hBound : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          norm (F' w u) <=
            (8 / R) * quadraticDedekindJLargeMajorantAtDistance d u)
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro w hw
      exact hDerivativeBound u hu w hw
    have hBoundInt : IntegrableOn
        (fun u : Real => (8 / R) * quadraticDedekindJLargeMajorantAtDistance d u)
        (Ioi (1 : Real)) :=
      (quadraticDedekindJLargeMajorantAtDistance_integrableOn hd).const_mul (8 / R)
    have hDiff : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          HasDerivAt (fun v : Complex => F v u) (F' w u) w)
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [F, F']
      exact (hAnalytic u hu w hwClosed).differentiableAt.hasDerivAt
    have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F')
      (bound := fun u : Real =>
        (8 / R) * quadraticDedekindJLargeMajorantAtDistance d u)
      hsNhd hFMeas hFInt hF'Meas hBound hBoundInt hDiff
    unfold quadraticDedekindJShiftedComplexContinuationFilledLarge
    simpa [F, F'] using hMain.2
  have hDiffOn : DifferentiableOn Complex
      (quadraticDedekindJShiftedComplexContinuationFilledLarge D) s := by
    intro z hz
    exact (hHasDeriv z hz).differentiableAt.differentiableWithinAt
  apply hDiffOn.analyticAt
  dsimp [s]
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith : 0 < R / 4))

theorem quadraticDedekindJMellinShiftIntegrandFilled_integrableOn_large_of_geometry
    (D : NumberField.OddFundamentalDiscriminant)
    {d : Real} (hd : 0 < d) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) (hzNorm : d <= norm z) :
    IntegrableOn (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D z u)
      (Ioi (1 : Real)) := by
  have hzNe : Not (z = 0) := by
    intro hEq
    rw [hEq, norm_zero] at hzNorm
    linarith
  have hContinuous : ContinuousOn (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D z u)
      (Ioi (1 : Real)) := by
    intro u hu
    have hsRe : 1 < ((((u + 1 : Real) : Complex) - z).re) := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [hzRe, mem_Ioi.mp hu]
    have hsZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hFactor : Not (quadraticDedekindZetaPoleFactor D
        (((u + 1 : Real) : Complex) - z) = 0) :=
      quadraticDedekindZetaPoleFactor_ne_zero_of_one_le_re D hsRe.le
    have hJoint :=
      quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne
        D (by linarith [mem_Ioi.mp hu] : 0 <= u) hzNe hsZero hFactor
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        quadraticDedekindJMellinShiftIntegrandFilled D z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  apply Integrable.mono'
    (quadraticDedekindJLargeMajorantAtDistance_integrableOn hd)
    (hContinuous.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact
    norm_quadraticDedekindJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge
      D hd hu hzRe hzNorm

theorem exists_quadraticDedekindRightmostRayLargeGeometry
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re)
    {eps : Real} (hEps : 0 < eps) :
    Exists fun d : Real => Exists fun R : Real =>
      And (0 < d) (And (0 < R)
        (forall z : Complex,
          Membership.mem
            (Metric.ball ((1 - rho) - (eps : Complex)) R) z ->
            And (z.re <= (3 / 4 : Real)) (d <= norm z))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  have hCenterIm : center.im = -rho.im := by
    dsimp [center]
    simp
  have hCenterNe : Not (center = 0) := by
    intro hEq
    have hZeroIm : center.im = 0 := by rw [hEq]; simp
    exact hIm (neg_eq_zero.mp (hCenterIm.symm.trans hZeroIm))
  have hCenterNorm : 0 < norm center := norm_pos_iff.mpr hCenterNe
  have hCenterRe : center.re = 1 - rho.re - eps := by
    dsimp [center]
  have hReMargin : 0 < (3 / 4 : Real) - center.re := by
    rw [hCenterRe]
    linarith
  let d : Real := norm center / 2
  let R : Real := min (norm center / 2)
    (((3 / 4 : Real) - center.re) / 2)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hRPos : 0 < R := by
    dsimp [R]
    exact lt_min (by positivity) (by positivity)
  have hGeometry : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (z.re <= (3 / 4 : Real)) (d <= norm z) := by
    intro z hz
    have hzDist : dist z center < R := by
      simpa [Metric.mem_ball] using hz
    have hDistNorm : dist z center < norm center / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_left _ _)
    have hDistRe : dist z center <
        ((3 / 4 : Real) - center.re) / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_right _ _)
    have hReDiff : z.re - center.re <= dist z center := by
      calc
        z.re - center.re <= abs (z.re - center.re) := le_abs_self _
        _ = abs ((z - center).re) :=
          congrArg abs (Complex.sub_re z center).symm
        _ <= norm (z - center) := Complex.abs_re_le_norm _
        _ = dist z center := by rw [dist_eq_norm]
    have hTriangle : norm center <= dist center z + norm z := by
      have h := dist_triangle center z 0
      simpa [dist_zero_right] using h
    have hNorm : d <= norm z := by
      dsimp [d]
      rw [dist_comm center z] at hTriangle
      linarith
    exact And.intro (by linarith) hNorm
  exact Exists.intro d (Exists.intro R
    (And.intro hd (And.intro hRPos (by simpa [center] using hGeometry))))

theorem quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRay
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re)
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex (quadraticDedekindJShiftedComplexContinuationFilledLarge D)
      ((1 - rho) - (eps : Complex)) := by
  choose d R hd hRPos hGeometry using
    exists_quadraticDedekindRightmostRayLargeGeometry hIm hHalf hEps
  exact quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    D hRPos hd hGeometry

theorem eventually_quadraticDedekindJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Filter.Eventually (fun z : Complex =>
      IntegrableOn (fun u : Real =>
        quadraticDedekindJMellinShiftIntegrandFilled D z u) (Ioc (0 : Real) 1))
      (nhds ((1 - rho) - (eps : Complex))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  choose R hRPos hGood using
    exists_quadraticDedekindRightmostRayCompactTubeRadius D hIm hRay hEps
  have hBall : Membership.mem (nhds center)
      (Metric.ball center (R / 2)) :=
    Metric.ball_mem_nhds _ (by linarith)
  filter_upwards [hBall] with z hz
  have hzClosed : Membership.mem
      (Metric.closedBall center (R / 2)) z :=
    Metric.ball_subset_closedBall hz
  have hzBall : Membership.mem (Metric.ball center R) z := by
    rw [Metric.mem_closedBall] at hzClosed
    rw [Metric.mem_ball]
    linarith
  have hzGood := hGood z (by simpa [center] using hzBall)
  have hContinuous : ContinuousOn (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D z u) (Icc (0 : Real) 1) := by
    intro u hu
    have hJoint := quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne D
      hu.1 hzGood.1 (hzGood.2 u hu).1 (hzGood.2 u hu).2
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        quadraticDedekindJMellinShiftIntegrandFilled D z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hInt : IntegrableOn (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D z u) (Icc (0 : Real) 1) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact hContinuous
  exact hInt.mono_set Ioc_subset_Icc_self

theorem eventually_quadraticDedekindJMellinShiftIntegrandFilled_integrableOn_large_rightmostRay
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re)
    {eps : Real} (hEps : 0 < eps) :
    Filter.Eventually (fun z : Complex =>
      IntegrableOn (fun u : Real =>
        quadraticDedekindJMellinShiftIntegrandFilled D z u) (Ioi (1 : Real)))
      (nhds ((1 - rho) - (eps : Complex))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  choose d R hd hRPos hGeometry using
    exists_quadraticDedekindRightmostRayLargeGeometry hIm hHalf hEps
  have hBall : Membership.mem (nhds center) (Metric.ball center R) :=
    Metric.ball_mem_nhds _ hRPos
  filter_upwards [hBall] with z hz
  have hzGeometry := hGeometry z (by simpa [center] using hz)
  exact quadraticDedekindJMellinShiftIntegrandFilled_integrableOn_large_of_geometry D
    hd hzGeometry.1 hzGeometry.2

theorem eventually_quadraticDedekindJShiftedComplexContinuationFilled_eq_compact_add_large_rightmostRay
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Filter.EventuallyEq (nhds ((1 - rho) - (eps : Complex)))
      (quadraticDedekindJShiftedComplexContinuationFilled D)
      (fun z : Complex =>
        quadraticDedekindJShiftedComplexContinuationFilledCompact D z +
          quadraticDedekindJShiftedComplexContinuationFilledLarge D z) := by
  have hCompact :=
    eventually_quadraticDedekindJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
      D hIm hRay hEps
  have hLarge :=
    eventually_quadraticDedekindJMellinShiftIntegrandFilled_integrableOn_large_rightmostRay
      D hIm hHalf hEps
  filter_upwards [hCompact, hLarge] with z hCompactInt hLargeInt
  unfold quadraticDedekindJShiftedComplexContinuationFilled
    quadraticDedekindJShiftedComplexContinuationFilledCompact
    quadraticDedekindJShiftedComplexContinuationFilledLarge
  rw [<- Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) <= 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hCompactInt
  . exact hLargeInt


end

end RobinBV.NumberField
