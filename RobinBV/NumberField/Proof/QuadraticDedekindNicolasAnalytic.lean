import RobinBV.NumberField.Proof.QuadraticDedekindNicolasLarge

/-!
# Analytic quadratic Dedekind continuation

Focused infrastructure for the quadratic Dedekind Nicolas-Landau Omega theorem.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section
theorem quadraticDedekindJShiftedComplexContinuationFilled_analyticAt_rightmostRay
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex (quadraticDedekindJShiftedComplexContinuationFilled D)
      ((1 - rho) - (eps : Complex)) := by
  have hCompact :=
    quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_rightmostRay
      D hIm hRay hEps
  have hLarge :=
    quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRay
      D hIm hHalf hEps
  have hSum : AnalyticAt Complex (fun z : Complex =>
      quadraticDedekindJShiftedComplexContinuationFilledCompact D z +
        quadraticDedekindJShiftedComplexContinuationFilledLarge D z)
      ((1 - rho) - (eps : Complex)) := hCompact.add hLarge
  have hEq :=
    eventually_quadraticDedekindJShiftedComplexContinuationFilled_eq_compact_add_large_rightmostRay
      D hIm hHalf hRay hEps
  exact (analyticAt_congr hEq).mpr hSum

theorem quadraticDedekindJComplexMellinStartup_differentiableAt
    (D : NumberField.OddFundamentalDiscriminant)
    {X : Real} (hX : 3 <= X) (s0 : Complex) :
    DifferentiableAt Complex (quadraticDedekindJComplexMellinStartup D X) s0 := by
  let F : Complex -> Real -> Complex := fun s x =>
    (x : Complex) ^ (s - 1) * (quadraticDedekindNicolasJ D x : Complex)
  let F' : Complex -> Real -> Complex := fun s x =>
    ((Real.log x : Real) : Complex) * F s x
  let base : Real -> Complex := fun x =>
    (x : Complex) ^ (-3 : Complex) * (quadraticDedekindNicolasJ D x : Complex)
  let ratio : Complex -> Real -> Complex := fun s x =>
    (x : Complex) ^ (s + 2)
  let majorant : Real -> Real := fun x =>
    norm (base x) * X ^ (abs s0.re + 4)
  have hRealBase : IntegrableOn (fun x : Real =>
      x ^ (-3 : Real) * quadraticDedekindNicolasJ D x) (Ioc (3 : Real) X) := by
    have h := quadraticDedekindNicolasJ_realMellin_integrableOn_Ioi_three D
      (a := (-2 : Real)) (by norm_num)
    have hRestricted := h.mono_set
      (show Ioc (3 : Real) X <= Ioi 3 from Ioc_subset_Ioi_self)
    apply hRestricted.congr_fun
    . intro x hx
      congr 2
      norm_num
    . exact measurableSet_Ioc
  have hCastBase : IntegrableOn (fun x : Real =>
      ((x ^ (-3 : Real) * quadraticDedekindNicolasJ D x : Real) : Complex))
      (Ioc (3 : Real) X) :=
    Complex.ofRealCLM.integrable_comp hRealBase
  have hBaseIntegrable : Integrable base
      (volume.restrict (Ioc (3 : Real) X)) := by
    apply hCastBase.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    dsimp [base]
    rw [show (-3 : Complex) = ((-3 : Real) : Complex) by norm_num,
      <- Complex.ofReal_cpow hxPos.le]
    push_cast
    rfl
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hMajorantIntegrable : Integrable majorant
      (volume.restrict (Ioc (3 : Real) X)) := by
    have h := hBaseIntegrable.norm.const_mul
      (X ^ (abs s0.re + 4))
    simpa [majorant, mul_comm] using h
  have hMeasurable : forall s : Complex, AEStronglyMeasurable (F s)
      (volume.restrict (Ioc (3 : Real) X)) := by
    intro s
    have hRatioContinuous : ContinuousOn (ratio s) (Ioc (3 : Real) X) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      dsimp [ratio]
      have hxPos : 0 < x := lt_trans (by norm_num) hx.1
      exact (continuousAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 hxPos)).comp
          Complex.continuous_ofReal.continuousAt
    have hProduct := hBaseIntegrable.aestronglyMeasurable.mul
      (hRatioContinuous.aestronglyMeasurable measurableSet_Ioc)
    apply hProduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hPower : (x : Complex) ^ (-3 : Complex) *
        (x : Complex) ^ (s + 2) = (x : Complex) ^ (s - 1) := by
      rw [<- Complex.cpow_add _ _ hxZero]
      congr 1
      ring
    dsimp [F, base, ratio]
    calc
      (x : Complex) ^ (-3 : Complex) * (quadraticDedekindNicolasJ D x : Complex) *
          (x : Complex) ^ (s + 2) =
          ((x : Complex) ^ (-3 : Complex) *
            (x : Complex) ^ (s + 2)) * (quadraticDedekindNicolasJ D x : Complex) := by ring
      _ = (x : Complex) ^ (s - 1) * (quadraticDedekindNicolasJ D x : Complex) := by
        rw [hPower]
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall x : Real, 3 < x -> x <= X ->
        norm (F s x) <= majorant x := by
    intro s hs x hxThree hxX
    have hDist : norm (s - s0) < 1 := by
      simpa [dist_eq_norm] using hs
    have hReAbs : abs (s.re - s0.re) <= norm (s - s0) := by
      simpa using Complex.abs_re_le_norm (s - s0)
    have hReUpper : s.re < s0.re + 1 := by
      have hAbsLt : abs (s.re - s0.re) < 1 := lt_of_le_of_lt hReAbs hDist
      linarith [(abs_lt.mp hAbsLt).2]
    have hxPos : 0 < x := lt_trans (by norm_num) hxThree
    have hxOne : 1 <= x := by linarith
    have hExponent : s.re + 2 <= abs s0.re + 4 := by
      have hPosPart : s0.re <= abs s0.re := le_abs_self s0.re
      linarith
    have hExponentNonneg : 0 <= abs s0.re + 4 := by positivity
    have hRatioBound : norm (ratio s x) <=
        X ^ (abs s0.re + 4) := by
      dsimp [ratio]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
      calc
        x ^ (s.re + 2) <= x ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow_of_exponent_le hxOne hExponent
        _ <= X ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow hxPos.le hxX hExponentNonneg
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hFactor : F s x = base x * ratio s x := by
      have hPower : (x : Complex) ^ (-3 : Complex) *
          (x : Complex) ^ (s + 2) = (x : Complex) ^ (s - 1) := by
        rw [<- Complex.cpow_add _ _ hxZero]
        congr 1
        ring
      dsimp [F, base, ratio]
      calc
        (x : Complex) ^ (s - 1) * (quadraticDedekindNicolasJ D x : Complex) =
            ((x : Complex) ^ (-3 : Complex) *
              (x : Complex) ^ (s + 2)) * (quadraticDedekindNicolasJ D x : Complex) := by
          rw [hPower]
        _ = ((x : Complex) ^ (-3 : Complex) *
            (quadraticDedekindNicolasJ D x : Complex)) * (x : Complex) ^ (s + 2) := by ring
    rw [hFactor, norm_mul]
    dsimp [majorant]
    exact mul_le_mul_of_nonneg_left hRatioBound (norm_nonneg (base x))
  have hFIntegrable : Integrable (F s0)
      (volume.restrict (Ioc (3 : Real) X)) := by
    apply Integrable.mono hMajorantIntegrable (hMeasurable s0)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hMajorantNonneg : 0 <= majorant x := by
      dsimp [majorant]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hMajorantNonneg]
    exact hBound s0 (by simp [dist_self]) x hx.1 hx.2
  have hDerivativeMeasurable : AEStronglyMeasurable (F' s0)
      (volume.restrict (Ioc (3 : Real) X)) := by
    have hRealLogOn : ContinuousOn (fun x : Real => Real.log x)
        (Ioc (3 : Real) X) := by
      apply Real.continuousOn_log.mono
      intro x hx
      exact Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (lt_trans (by norm_num) hx.1))
    have hRealLog : AEStronglyMeasurable (fun x : Real => Real.log x)
        (volume.restrict (Ioc (3 : Real) X)) :=
      hRealLogOn.aestronglyMeasurable measurableSet_Ioc
    have hLog : AEStronglyMeasurable
        (fun x : Real => ((Real.log x : Real) : Complex))
        (volume.restrict (Ioc (3 : Real) X)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hRealLog
    exact hLog.mul (hMeasurable s0)
  have hDerivativeBound : Filter.Eventually
      (fun x : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        norm (F' s x) <= X * majorant x)
      (ae (volume.restrict (Ioc (3 : Real) X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro s hs
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxOne : 1 <= x := by linarith [hx.1]
    have hLogNonneg : 0 <= Real.log x := Real.log_nonneg hxOne
    have hLogBound : Real.log x <= X := by
      have hLogSub := Real.log_le_sub_one_of_pos hxPos
      linarith [hx.2]
    have hFBound : norm (F s x) <= majorant x :=
      hBound s (by simpa [Metric.mem_ball] using hs) x hx.1 hx.2
    dsimp [F']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hLogNonneg]
    exact mul_le_mul hLogBound hFBound (norm_nonneg _) hXPos.le
  have hDerivativeIntegrable : Integrable (fun x : Real => X * majorant x)
      (volume.restrict (Ioc (3 : Real) X)) :=
    hMajorantIntegrable.const_mul X
  have hDerivative : Filter.Eventually
      (fun x : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        HasDerivAt (fun z : Complex => F z x) (F' s x) s)
      (ae (volume.restrict (Ioc (3 : Real) X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro s hs
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hExponent : HasDerivAt (fun z : Complex => z - 1) 1 s :=
      (hasDerivAt_id' s).sub_const 1
    have hPower := hExponent.const_cpow (Or.inl hxZero)
    have hProduct := hPower.mul_const (quadraticDedekindNicolasJ D x : Complex)
    dsimp [F, F']
    apply hProduct.congr_deriv
    rw [Complex.ofReal_log hxPos.le]
    ring
  unfold quadraticDedekindJComplexMellinStartup
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s0 zero_lt_one)
    (Eventually.of_forall hMeasurable) hFIntegrable
    hDerivativeMeasurable hDerivativeBound hDerivativeIntegrable hDerivative
  exact hMain.2.differentiableAt

theorem quadraticDedekindJComplexMellinStartup_analyticAt
    (D : NumberField.OddFundamentalDiscriminant)
    {X : Real} (hX : 3 <= X) (s0 : Complex) :
    AnalyticAt Complex (quadraticDedekindJComplexMellinStartup D X) s0 := by
  have hDifferentiable : Differentiable Complex
      (quadraticDedekindJComplexMellinStartup D X) := by
    intro s
    exact quadraticDedekindJComplexMellinStartup_differentiableAt D hX s
  exact hDifferentiable.analyticAt s0

def quadraticDedekindJLargeMajorantZero (u : Real) : Real :=
  20 * (2 * (Real.log 4 + 4) + 1) * (u + 1) *
    (3 : Real) ^ (-u + (3 / 4 : Real))

theorem quadraticDedekindJLargeMajorantZero_integrableOn :
    IntegrableOn quadraticDedekindJLargeMajorantZero
      (Ioi (1 : Real)) := by
  have h := quadraticDedekindJLargeMajorantAtDistance_integrableOn
    (d := (1 / 4 : Real)) (by norm_num)
  apply h.congr_fun
  next =>
    intro u hu
    unfold quadraticDedekindJLargeMajorantZero
      quadraticDedekindJLargeMajorantAtDistance
    ring
  next => exact measurableSet_Ioi

theorem quadraticDedekindJShiftNumeratorFilled_differentiableOn_quarter
    (D : NumberField.OddFundamentalDiscriminant)
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex
      (fun z : Complex => quadraticDedekindJShiftNumeratorFilled D z u)
      (Metric.ball (0 : Complex) (1 / 4 : Real)) := by
  intro z hz
  have hzNorm : norm z < (1 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (1 / 4 : Real) :=
    (Complex.re_le_norm z).trans_lt hzNorm
  have hsRe : 1 < ((((u + 1 : Real) : Complex) - z).re) := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hsZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
    intro hEq
    rw [hEq] at hsRe
    norm_num at hsRe
  have hFactor : Not (quadraticDedekindZetaPoleFactor D
      (((u + 1 : Real) : Complex) - z) = 0) :=
    quadraticDedekindZetaPoleFactor_ne_zero_of_one_le_re D hsRe.le
  exact (quadraticDedekindJShiftNumeratorFilled_analyticAt
    D (le_trans zero_le_one hu.le) hsZero hFactor).differentiableAt.differentiableWithinAt

theorem norm_quadraticDedekindJMellinShiftIntegrandFilled_le_zeroBall
    (D : NumberField.OddFundamentalDiscriminant)
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z) :
    norm (quadraticDedekindJMellinShiftIntegrandFilled D z u) <=
      quadraticDedekindJLargeMajorantZero u := by
  let R : Real := 1 / 4
  let M : Real := 5 * (2 * (Real.log 4 + 4) + 1) *
    (3 : Real) ^ (-u + (3 / 4 : Real))
  have hMNonneg : 0 <= M := by
    dsimp [M]
    positivity
  have hMaps : MapsTo
      (fun w : Complex => quadraticDedekindJShiftNumeratorFilled D w u)
      (Metric.ball (0 : Complex) R)
      (Metric.closedBall
        (quadraticDedekindJShiftNumeratorFilled D 0 u) M) := by
    intro w hw
    rw [quadraticDedekindJShiftNumeratorFilled_zero]
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_quadraticDedekindJShiftNumeratorFilled_le_of_re_le_threeQuarter
      D hu (by
        have hwNorm : norm w < (1 / 4 : Real) := by
          simpa [R, Metric.mem_ball, dist_zero_right] using hw
        exact (Complex.re_le_norm w).trans
          (hwNorm.le.trans (by norm_num : (1 / 4 : Real) <= 3 / 4)))
  have hDslope := Complex.norm_dslope_le_div_of_mapsTo_ball
    (quadraticDedekindJShiftNumeratorFilled_differentiableOn_quarter D hu)
    hMaps (by simpa [R] using hz)
  have huPos : 0 < u + 1 := by linarith
  unfold quadraticDedekindJMellinShiftIntegrandFilled
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huPos]
  calc
    (u + 1) * norm
        (dslope (fun w : Complex =>
          quadraticDedekindJShiftNumeratorFilled D w u) 0 z) <=
        (u + 1) * (M / R) :=
      mul_le_mul_of_nonneg_left hDslope huPos.le
    _ = quadraticDedekindJLargeMajorantZero u := by
      unfold quadraticDedekindJLargeMajorantZero
      dsimp [M, R]
      ring

theorem quadraticDedekindJMellinShiftIntegrandFilled_differentiableOn_quarter
    (D : NumberField.OddFundamentalDiscriminant)
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex
      (fun z : Complex => quadraticDedekindJMellinShiftIntegrandFilled D z u)
      (Metric.ball (0 : Complex) (1 / 4 : Real)) := by
  intro z hz
  have hzNorm : norm z < (1 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (1 / 4 : Real) :=
    (Complex.re_le_norm z).trans_lt hzNorm
  have hsRe : 1 < ((((u + 1 : Real) : Complex) - z).re) := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hsZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
    intro hEq
    rw [hEq] at hsRe
    norm_num at hsRe
  have hFactor : Not (quadraticDedekindZetaPoleFactor D
      (((u + 1 : Real) : Complex) - z) = 0) :=
    quadraticDedekindZetaPoleFactor_ne_zero_of_one_le_re D hsRe.le
  exact (quadraticDedekindJMellinShiftIntegrandFilled_analyticAt
    D (le_trans zero_le_one hu.le) hsZero hFactor).differentiableAt.differentiableWithinAt

theorem norm_deriv_quadraticDedekindJMellinShiftIntegrandFilled_le
    (D : NumberField.OddFundamentalDiscriminant)
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    norm (deriv (fun w : Complex =>
      quadraticDedekindJMellinShiftIntegrandFilled D w u) z) <=
      16 * quadraticDedekindJLargeMajorantZero u := by
  let f : Complex -> Complex := fun w : Complex =>
    quadraticDedekindJMellinShiftIntegrandFilled D w u
  let R : Real := 1 / 8
  let M : Real := quadraticDedekindJLargeMajorantZero u
  have hSmallSubset : Metric.ball z R <=
      Metric.ball (0 : Complex) (1 / 4 : Real) := by
    intro w hw
    rw [Metric.mem_ball] at hw hz
    rw [Metric.mem_ball]
    calc
      dist w 0 <= dist w z + dist z 0 := dist_triangle w z 0
      _ < (1 / 8 : Real) + (1 / 8 : Real) := add_lt_add hw hz
      _ = (1 / 4 : Real) := by norm_num
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self (by norm_num)
  have hDiff : DifferentiableOn Complex f (Metric.ball z R) :=
    (quadraticDedekindJMellinShiftIntegrandFilled_differentiableOn_quarter D hu).mono
      hSmallSubset
  have hMaps : MapsTo f (Metric.ball z R)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwQuarter := hSmallSubset hw
    have hwBound : norm (f w) <= M := by
      dsimp [f, M]
      simpa [quadraticDedekindJLargeMajorantZero] using
        norm_quadraticDedekindJMellinShiftIntegrandFilled_le_zeroBall D hu hwQuarter
    have hzBound : norm (f z) <= M := by
      dsimp [f, M]
      simpa [quadraticDedekindJLargeMajorantZero] using
        norm_quadraticDedekindJMellinShiftIntegrandFilled_le_zeroBall D hu hzQuarter
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) <= norm (f w) + norm (f z) := by
        simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
      _ <= M + M := add_le_add hwBound hzBound
      _ = 2 * M := by ring
  have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
    hDiff hMaps (by norm_num : 0 < R)
  change norm (deriv f z) <= 16 * M
  calc
    norm (deriv f z) <= (2 * M) / R := hCauchy
    _ = 16 * M := by
      dsimp [R]
      ring

theorem quadraticDedekindJShiftNumeratorFilled_continuousOn_u
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z) :
    ContinuousOn (fun u : Real => quadraticDedekindJShiftNumeratorFilled D z u)
      (Ioi (1 : Real)) := by
  let s0 : Real -> Complex := fun u : Real => ((u + 1 : Real) : Complex)
  let s1 : Real -> Complex := fun u : Real => s0 u - z
  have hS0 : Continuous s0 := by
    dsimp [s0]
    fun_prop
  have hS1 : Continuous s1 := by
    dsimp [s1]
    exact hS0.sub continuous_const
  intro u hu
  have huOne : 1 < u := mem_Ioi.mp hu
  have hzNorm : norm z < (1 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (1 / 4 : Real) :=
    (Complex.re_le_norm z).trans_lt hzNorm
  have hs0 : 1 < (s0 u).re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < (s1 u).re := by
    dsimp [s1, s0]
    linarith
  have hTail0 : ContinuousAt (fun v : Real =>
      quadraticDedekindPsiMellinTailContinuationFilled D (s0 v)) u :=
    (quadraticDedekindPsiMellinTailContinuationFilled_analyticAt_of_one_le_re D hs0.le).continuousAt.comp
      hS0.continuousAt
  have hTail1 : ContinuousAt (fun v : Real =>
      quadraticDedekindPsiMellinTailContinuationFilled D (s1 v)) u :=
    (quadraticDedekindPsiMellinTailContinuationFilled_analyticAt_of_one_le_re D hs1.le).continuousAt.comp
      hS1.continuousAt
  unfold quadraticDedekindJShiftNumeratorFilled
  change ContinuousWithinAt (fun v : Real =>
    quadraticDedekindPsiMellinTailContinuationFilled D (s1 v) -
      (3 : Complex) ^ z *
        quadraticDedekindPsiMellinTailContinuationFilled D (s0 v))
    (Ioi (1 : Real)) u
  exact (hTail1.sub (continuousAt_const.mul hTail0)).continuousWithinAt

theorem quadraticDedekindJMellinShiftIntegrandFilled_continuousOn_u_of_ne
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z)
    (hzZero : Not (z = 0)) :
    ContinuousOn (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D z u) (Ioi (1 : Real)) := by
  have hNumeratorZ := quadraticDedekindJShiftNumeratorFilled_continuousOn_u D hz
  have hZeroMem : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) (0 : Complex) :=
    Metric.mem_ball_self (by norm_num)
  have hNumeratorZero :=
    quadraticDedekindJShiftNumeratorFilled_continuousOn_u D hZeroMem
  have hU : Continuous (fun u : Real => ((u + 1 : Real) : Complex)) := by
    fun_prop
  have hInv : Continuous (fun _ : Real => Inv.inv (z - 0)) :=
    continuous_const
  have hEq : (fun u : Real => quadraticDedekindJMellinShiftIntegrandFilled D z u) =
      (fun u : Real => ((u + 1 : Real) : Complex) *
        Inv.inv (z - 0) *
          (quadraticDedekindJShiftNumeratorFilled D z u -
            quadraticDedekindJShiftNumeratorFilled D 0 u)) := by
    funext u
    unfold quadraticDedekindJMellinShiftIntegrandFilled
    rw [dslope_of_ne _ hzZero]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub]
    ring
  rw [hEq]
  exact (hU.continuousOn.mul hInv.continuousOn).mul
    (hNumeratorZ.sub hNumeratorZero)

theorem quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z)
    (hzZero : Not (z = 0)) :
    AEStronglyMeasurable (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D z u)
      (volume.restrict (Ioi (1 : Real))) :=
  (quadraticDedekindJMellinShiftIntegrandFilled_continuousOn_u_of_ne D
    hz hzZero).aestronglyMeasurable measurableSet_Ioi

theorem quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable_zero
    (D : NumberField.OddFundamentalDiscriminant) :
    AEStronglyMeasurable (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D 0 u)
      (volume.restrict (Ioi (1 : Real))) := by
  let zseq : Nat -> Complex := fun n : Nat =>
    (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex)
  have hZPos : forall n : Nat,
      0 < (1 : Real) / (8 * ((n : Real) + 1)) := by
    intro n
    positivity
  have hZMem : forall n : Nat, Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) (zseq n) := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [zseq]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hZPos n)]
    have hn : 0 <= (n : Real) := by positivity
    apply one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 4)
    nlinarith
  have hZNe : forall n : Nat, Not (zseq n = 0) := by
    intro n
    dsimp [zseq]
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero (by norm_num) (by positivity))
  have hRecip : Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hScaled : Tendsto
      (fun n : Nat => (1 / 8 : Real) *
        ((1 : Real) / ((n : Real) + 1)))
      atTop (nhds ((1 / 8 : Real) * 0)) :=
    tendsto_const_nhds.mul hRecip
  have hReal : Tendsto
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1)))
      atTop (nhds 0) := by
    have hFunctions :
        (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1))) =
          (fun n : Nat => (1 / 8 : Real) *
            ((1 : Real) / ((n : Real) + 1))) := by
      funext n
      field_simp
    rw [hFunctions]
    simpa using hScaled
  have hZ : Tendsto zseq atTop (nhds (0 : Complex)) := by
    have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
    change Tendsto
      (fun n : Nat =>
        (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex))
      atTop (nhds (0 : Complex)) at hCast
    change Tendsto
      (fun n : Nat =>
        (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex))
      atTop (nhds (0 : Complex))
    exact hCast
  have hMeas : forall n : Nat, AEMeasurable
      (fun u : Real => quadraticDedekindJMellinShiftIntegrandFilled D (zseq n) u)
      (volume.restrict (Ioi (1 : Real))) := by
    intro n
    exact (quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne D
      (hZMem n) (hZNe n)).aemeasurable
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto
        (fun n : Nat => quadraticDedekindJMellinShiftIntegrandFilled D (zseq n) u)
        atTop (nhds (quadraticDedekindJMellinShiftIntegrandFilled D 0 u)))
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huPos : 0 < u := zero_lt_one.trans hu
    exact (quadraticDedekindJMellinShiftIntegrandFilled_analyticAt_zero D
      huPos.le).continuousAt.tendsto.comp hZ
  exact (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D z u)
      (volume.restrict (Ioi (1 : Real))) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable_zero D
  case neg =>
    exact quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne D
      hz hzZero

theorem quadraticDedekindJMellinShiftIntegrandFilled_integrableOn_large
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    IntegrableOn (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D z u) (Ioi (1 : Real)) := by
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  apply Integrable.mono' quadraticDedekindJLargeMajorantZero_integrableOn
    (quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable D hzQuarter)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa [quadraticDedekindJLargeMajorantZero] using
    norm_quadraticDedekindJMellinShiftIntegrandFilled_le_zeroBall D (mem_Ioi.mp hu) hzQuarter

def quadraticDedekindJLargeDerivativeMajorant (u : Real) : Real :=
  16 * quadraticDedekindJLargeMajorantZero u

theorem quadraticDedekindJLargeDerivativeMajorant_integrableOn :
    IntegrableOn quadraticDedekindJLargeDerivativeMajorant (Ioi (1 : Real)) := by
  unfold quadraticDedekindJLargeDerivativeMajorant
  exact quadraticDedekindJLargeMajorantZero_integrableOn.const_mul 16

def quadraticDedekindJDerivativeStep (n : Nat) : Complex :=
  (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex)

theorem quadraticDedekindJDerivativeStep_ne_zero (n : Nat) :
    Not (quadraticDedekindJDerivativeStep n = 0) := by
  unfold quadraticDedekindJDerivativeStep
  exact Complex.ofReal_ne_zero.mpr
    (div_ne_zero (by norm_num) (by positivity))

theorem norm_quadraticDedekindJDerivativeStep_lt (n : Nat) :
    norm (quadraticDedekindJDerivativeStep n) <= (1 / 8 : Real) := by
  unfold quadraticDedekindJDerivativeStep
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity :
      0 < (1 : Real) / (8 * ((n : Real) + 1)))]
  apply one_div_le_one_div_of_le (by norm_num : (0 : Real) < 8)
  have hn : 0 <= (n : Real) := by positivity
  nlinarith

theorem quadraticDedekindJDerivativeStep_tendsto_zero :
    Tendsto quadraticDedekindJDerivativeStep atTop (nhds (0 : Complex)) := by
  have hRecip : Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hScaled : Tendsto
      (fun n : Nat => (1 / 8 : Real) *
        ((1 : Real) / ((n : Real) + 1)))
      atTop (nhds ((1 / 8 : Real) * 0)) :=
    tendsto_const_nhds.mul hRecip
  have hFunctions :
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1))) =
        (fun n : Nat => (1 / 8 : Real) *
          ((1 : Real) / ((n : Real) + 1))) := by
    funext n
    field_simp
  have hReal : Tendsto
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1)))
      atTop (nhds 0) := by
    rw [hFunctions]
    simpa using hScaled
  have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
  change Tendsto quadraticDedekindJDerivativeStep atTop (nhds (0 : Complex)) at hCast
  exact hCast

theorem deriv_quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        quadraticDedekindJMellinShiftIntegrandFilled D w u) z)
      (volume.restrict (Ioi (1 : Real))) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => quadraticDedekindJMellinShiftIntegrandFilled D w u)
      z (z + quadraticDedekindJDerivativeStep n)
  have hzNorm : norm z < (1 / 8 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hShiftQuarter : forall n : Nat, Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real))
      (z + quadraticDedekindJDerivativeStep n) := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    calc
      norm (z + quadraticDedekindJDerivativeStep n) <=
          norm z + norm (quadraticDedekindJDerivativeStep n) := norm_add_le _ _
      _ < (1 / 8 : Real) + (1 / 8 : Real) :=
        add_lt_add_of_lt_of_le hzNorm (norm_quadraticDedekindJDerivativeStep_lt n)
      _ = (1 / 4 : Real) := by norm_num
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioi (1 : Real))) := by
    intro n
    have hShift :=
      quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable D
        (hShiftQuarter n)
    have hBase :=
      quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable D hzQuarter
    have hEq : slopeSeq n = fun u : Real =>
        Inv.inv ((z + quadraticDedekindJDerivativeStep n) - z) *
          (quadraticDedekindJMellinShiftIntegrandFilled D
              (z + quadraticDedekindJDerivativeStep n) u -
            quadraticDedekindJMellinShiftIntegrandFilled D z u) := by
      funext u
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub]
    rw [hEq]
    exact ((hShift.sub hBase).const_mul
      (Inv.inv ((z + quadraticDedekindJDerivativeStep n) - z))).aemeasurable
  have hStepWithin : Tendsto quadraticDedekindJDerivativeStep atTop
      (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro quadraticDedekindJDerivativeStep_tendsto_zero
      (Eventually.of_forall (fun n : Nat =>
        Set.mem_compl_singleton_iff.mpr
          (quadraticDedekindJDerivativeStep_ne_zero n)))
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
        (nhds (deriv (fun w : Complex =>
          quadraticDedekindJMellinShiftIntegrandFilled D w u) z)))
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huOne : 1 < u := mem_Ioi.mp hu
    have hDiffAt : DifferentiableAt Complex
        (fun w : Complex => quadraticDedekindJMellinShiftIntegrandFilled D w u) z :=
      (quadraticDedekindJMellinShiftIntegrandFilled_differentiableOn_quarter D
        huOne z hzQuarter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hzQuarter)
    have hSlope := hDiffAt.hasDerivAt.tendsto_slope_zero.comp hStepWithin
    change Tendsto (fun n : Nat =>
      Inv.inv (quadraticDedekindJDerivativeStep n) *
        (quadraticDedekindJMellinShiftIntegrandFilled D
            (z + quadraticDedekindJDerivativeStep n) u -
          quadraticDedekindJMellinShiftIntegrandFilled D z u))
      atTop (nhds (deriv (fun w : Complex =>
        quadraticDedekindJMellinShiftIntegrandFilled D w u) z)) at hSlope
    dsimp [slopeSeq]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
    exact hSlope
  exact (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable


end

end RobinBV.NumberField
