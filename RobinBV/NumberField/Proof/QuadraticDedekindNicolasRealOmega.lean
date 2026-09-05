import RobinBV.NumberField.Proof.QuadraticDedekindNicolasRealFrontier

/-!
# Real-zero quadratic Dedekind Omega-minus theorem

Focused infrastructure for the quadratic Dedekind Nicolas-Landau Omega theorem.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section
theorem exists_quadraticDedekindRealRightmostRayCompactAwayKernel_bound
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real} (hBetaPos : 0 < beta)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0))
    {r : Real} (hrPos : 0 < r) (hrGap : r < 1 - beta) :
    Exists fun M : Real => And (0 <= M)
      (forall eps u : Real,
        Membership.mem (Icc (0 : Real) (r / 2)) eps ->
        Membership.mem (Icc (r / 2) (1 : Real)) u ->
        norm (quadraticDedekindJMellinShiftIntegrandFilled D
          (quadraticDedekindRightmostRayPoint (beta : Complex) eps) u) <= M) := by
  let K : Set (Prod Real Real) := fun p =>
    And (Membership.mem (Icc (0 : Real) (r / 2)) p.1)
      (Membership.mem (Icc (r / 2) (1 : Real)) p.2)
  let F : Prod Real Real -> Complex := fun p =>
    quadraticDedekindJMellinShiftIntegrandFilled D
      (quadraticDedekindRightmostRayPoint (beta : Complex) p.1) p.2
  have hKCompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_Icc : IsCompact (Icc (0 : Real) (r / 2))).prod
      (isCompact_Icc : IsCompact (Icc (r / 2) (1 : Real)))
  have hKNonempty : K.Nonempty := by
    refine Exists.intro ((0 : Real), r / 2) ?_
    dsimp [K]
    exact And.intro (And.intro le_rfl (by positivity))
      (And.intro le_rfl (by linarith))
  have hContinuous : ContinuousOn F K := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    change And (Membership.mem (Icc (0 : Real) (r / 2)) p.1)
      (Membership.mem (Icc (r / 2) (1 : Real)) p.2) at hp
    have hzZero : Not
        (quadraticDedekindRightmostRayPoint (beta : Complex) p.1 = 0) := by
      intro hEq
      have hRe := congrArg Complex.re hEq
      unfold quadraticDedekindRightmostRayPoint at hRe
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.zero_re] at hRe
      linarith [hp.1.2]
    let t : Real := p.1 + p.2
    let s : Complex := (beta : Complex) + (t : Complex)
    have htPos : 0 < t := by
      dsimp [t]
      linarith [hp.1.1, hp.2.1, hrPos]
    have hsRe : s.re = beta + t := by
      dsimp [s]
    have hsZero : Not (s = 0) := by
      intro hEq
      have hRe := congrArg Complex.re hEq
      rw [hsRe, Complex.zero_re] at hRe
      linarith
    have hFactor : Not (quadraticDedekindZetaPoleFactor D s = 0) := by
      by_cases hsOne : s = 1
      next =>
        rw [hsOne]
        exact quadraticDedekindZetaPoleFactor_one_ne_zero D
      next =>
        have hZeta : Not (quadraticDedekindZetaContinuation D s = 0) := by
          dsimp [s]
          exact hRay t htPos
        intro hFactorZero
        have hIdentity :=
          quadraticDedekindZetaContinuation_eq_poleFactor_div D hsOne
        rw [hFactorZero, zero_div] at hIdentity
        exact hZeta hIdentity
    have hShift :
        ((((p.2 + 1 : Real) : Complex) -
            quadraticDedekindRightmostRayPoint (beta : Complex) p.1)) =
          s := by
      dsimp [s, t, quadraticDedekindRightmostRayPoint]
      push_cast
      ring
    have hShiftZero : Not
        ((((p.2 + 1 : Real) : Complex) -
            quadraticDedekindRightmostRayPoint (beta : Complex) p.1) = 0) := by
      rw [hShift]
      exact hsZero
    have hShiftFactor : Not
        (quadraticDedekindZetaPoleFactor D
          (((p.2 + 1 : Real) : Complex) -
            quadraticDedekindRightmostRayPoint (beta : Complex) p.1) = 0) := by
      rw [hShift]
      exact hFactor
    have hJoint :=
      quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne D
        (u := p.2)
        (z := quadraticDedekindRightmostRayPoint (beta : Complex) p.1)
        (by linarith [hp.2.1, hrPos]) hzZero hShiftZero hShiftFactor
    have hEmbed : ContinuousAt (fun q : Prod Real Real =>
        (q.2,
          quadraticDedekindRightmostRayPoint (beta : Complex) q.1)) p := by
      unfold quadraticDedekindRightmostRayPoint
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    simpa [F, Function.comp_def] using hComp
  choose p hpK hpMax using
    hKCompact.exists_isMaxOn hKNonempty hContinuous.norm
  let M : Real := norm (F p)
  refine Exists.intro M (And.intro (norm_nonneg _) ?_)
  intro eps u hEps hU
  have hPair : K (eps, u) := by
    dsimp [K]
    exact And.intro hEps hU
  simpa [M, F] using hpMax hPair

theorem exists_quadraticDedekindRealRightmostRayCompactAwayIntegral_bound
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real} (hBetaPos : 0 < beta)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0))
    {r : Real} (hrPos : 0 < r) (hrHalf : r < 1 / 2)
    (hrGap : r < 1 - beta) :
    Exists fun M : Real => And (0 <= M)
      (forall eps : Real, 0 <= eps -> eps <= r / 2 ->
        norm (intervalIntegral
          (quadraticDedekindJMellinShiftIntegrandFilled D
            (quadraticDedekindRightmostRayPoint (beta : Complex) eps))
          (r - eps) 1 volume) <= M) := by
  choose M hMNonneg hKernel using
    exists_quadraticDedekindRealRightmostRayCompactAwayKernel_bound
      D hBetaPos hRay hrPos hrGap
  refine Exists.intro M (And.intro hMNonneg ?_)
  intro eps hEps hEpsLe
  have hLowerNonneg : 0 <= r - eps := by linarith
  have hLowerOne : r - eps <= 1 := by linarith
  have hPointwise : forall u : Real,
      Membership.mem (uIoc (r - eps) (1 : Real)) u ->
      norm (quadraticDedekindJMellinShiftIntegrandFilled D
        (quadraticDedekindRightmostRayPoint (beta : Complex) eps) u) <= M := by
    intro u hu
    have huIoc : Membership.mem (Ioc (r - eps) (1 : Real)) u := by
      simpa [uIoc, min_eq_left hLowerOne,
        max_eq_right hLowerOne] using hu
    apply hKernel eps u
    next => exact And.intro hEps hEpsLe
    next => exact And.intro (by linarith [huIoc.1]) huIoc.2
  have hNorm := intervalIntegral.norm_integral_le_of_norm_le_const hPointwise
  rw [abs_of_nonneg (by linarith : 0 <= (1 : Real) - (r - eps))] at hNorm
  nlinarith

theorem quadraticDedekindJMellinShiftIntegrandFilled_intervalIntegrable_compact_realRay
    (D : NumberField.OddFundamentalDiscriminant)
    {beta eps : Real} (hBetaPos : 0 < beta) (hEps : 0 < eps)
    (hEpsGap : eps < 1 - beta)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0)) :
    IntervalIntegrable
      (quadraticDedekindJMellinShiftIntegrandFilled D
        (quadraticDedekindRightmostRayPoint (beta : Complex) eps))
      volume 0 1 := by
  have hzZero : Not
      (quadraticDedekindRightmostRayPoint (beta : Complex) eps = 0) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    unfold quadraticDedekindRightmostRayPoint at hRe
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.zero_re] at hRe
    linarith
  apply ContinuousOn.intervalIntegrable
  intro u hu
  have huIcc : Membership.mem (Icc (0 : Real) 1) u := by
    simpa [uIcc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using hu
  let t : Real := eps + u
  let s : Complex := (beta : Complex) + (t : Complex)
  have htPos : 0 < t := by
    dsimp [t]
    linarith [huIcc.1]
  have hsRe : s.re = beta + t := by
    dsimp [s]
  have hsZero : Not (s = 0) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    rw [hsRe, Complex.zero_re] at hRe
    linarith
  have hFactor : Not (quadraticDedekindZetaPoleFactor D s = 0) := by
    by_cases hsOne : s = 1
    next =>
      rw [hsOne]
      exact quadraticDedekindZetaPoleFactor_one_ne_zero D
    next =>
      have hZeta : Not (quadraticDedekindZetaContinuation D s = 0) := by
        dsimp [s]
        exact hRay t htPos
      intro hFactorZero
      have hIdentity :=
        quadraticDedekindZetaContinuation_eq_poleFactor_div D hsOne
      rw [hFactorZero, zero_div] at hIdentity
      exact hZeta hIdentity
  have hShift :
      ((((u + 1 : Real) : Complex) -
          quadraticDedekindRightmostRayPoint (beta : Complex) eps)) = s := by
    dsimp [s, t, quadraticDedekindRightmostRayPoint]
    push_cast
    ring
  have hShiftZero : Not
      ((((u + 1 : Real) : Complex) -
          quadraticDedekindRightmostRayPoint (beta : Complex) eps) = 0) := by
    rw [hShift]
    exact hsZero
  have hShiftFactor : Not
      (quadraticDedekindZetaPoleFactor D
        (((u + 1 : Real) : Complex) -
          quadraticDedekindRightmostRayPoint (beta : Complex) eps) = 0) := by
    rw [hShift]
    exact hFactor
  have hJoint :=
    quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne D
      (u := u) (z := quadraticDedekindRightmostRayPoint (beta : Complex) eps)
      huIcc.1 hzZero hShiftZero hShiftFactor
  have hEmbed : ContinuousAt (fun v : Real =>
      (v, quadraticDedekindRightmostRayPoint (beta : Complex) eps)) u := by
    fun_prop
  have hComp := hJoint.comp_of_eq hEmbed (by rfl)
  have hAt : ContinuousAt (fun v : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D
        (quadraticDedekindRightmostRayPoint (beta : Complex) eps) v) u := by
    simpa [Function.comp_def] using hComp
  exact hAt.continuousWithinAt

theorem exists_quadraticDedekindRealRightmostRayCompactIntegral_re_log_upperBound
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real}
    (hZero : quadraticDedekindZetaContinuation D (beta : Complex) = 0)
    (hBetaPos : 0 < beta) (hBetaOne : beta < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0)) :
    Exists fun d : Real => Exists fun r : Real => Exists fun M : Real =>
      And (d < 0) (And (0 < r) (And (r < 1 / 2)
        (And (r < 1 - beta) (And (0 <= M)
          (forall eps : Real, 0 < eps -> eps <= r / 2 ->
            (intervalIntegral
              (quadraticDedekindJMellinShiftIntegrandFilled D
                (quadraticDedekindRightmostRayPoint (beta : Complex) eps))
              0 1 volume).re <=
                (3 / 4 : Real) * d * Real.log (r / eps) + M))))) := by
  choose d r hdNeg hrPos hrHalf hrGap hSingular using
    exists_quadraticDedekindRealRightmostRayCompactSingularIntegral_re_upperBound
      D hZero hBetaPos hBetaOne hRay
  choose M hMNonneg hAway using
    exists_quadraticDedekindRealRightmostRayCompactAwayIntegral_bound
      D hBetaPos hRay hrPos hrHalf hrGap
  refine Exists.intro d (Exists.intro r (Exists.intro M
    (And.intro hdNeg (And.intro hrPos (And.intro hrHalf
      (And.intro hrGap (And.intro hMNonneg ?_)))))))
  intro eps hEps hEpsLe
  have hEpsR : eps < r := by linarith [hrPos]
  have hEpsGap : eps < 1 - beta := hEpsR.trans hrGap
  have hLowerNonneg : 0 <= r - eps := by linarith [hEpsLe, hrPos]
  have hLowerOne : r - eps <= 1 := by linarith [hrHalf]
  let f : Real -> Complex :=
    quadraticDedekindJMellinShiftIntegrandFilled D
      (quadraticDedekindRightmostRayPoint (beta : Complex) eps)
  have hFullIntegrable : IntervalIntegrable f volume 0 1 := by
    dsimp [f]
    exact
      quadraticDedekindJMellinShiftIntegrandFilled_intervalIntegrable_compact_realRay
        D hBetaPos hEps hEpsGap hRay
  have hLeftIntegrable : IntervalIntegrable f volume 0 (r - eps) := by
    apply hFullIntegrable.mono_set
    intro u hu
    have huSmall : Membership.mem (Icc (0 : Real) (r - eps)) u := by
      simpa [uIcc, min_eq_left hLowerNonneg,
        max_eq_right hLowerNonneg] using hu
    have huFull : Membership.mem (Icc (0 : Real) 1) u :=
      And.intro huSmall.1 (huSmall.2.trans hLowerOne)
    simpa [uIcc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using huFull
  have hRightIntegrable : IntervalIntegrable f volume (r - eps) 1 := by
    apply hFullIntegrable.mono_set
    intro u hu
    have huSmall : Membership.mem (Icc (r - eps) (1 : Real)) u := by
      simpa [uIcc, min_eq_left hLowerOne,
        max_eq_right hLowerOne] using hu
    have huFull : Membership.mem (Icc (0 : Real) 1) u :=
      And.intro (hLowerNonneg.trans huSmall.1) huSmall.2
    simpa [uIcc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using huFull
  let L : Complex := intervalIntegral f 0 (r - eps) volume
  let R : Complex := intervalIntegral f (r - eps) 1 volume
  let T : Complex := intervalIntegral f 0 1 volume
  have hDecomp : L + R = T := by
    dsimp [L, R, T]
    exact intervalIntegral.integral_add_adjacent_intervals
      hLeftIntegrable hRightIntegrable
  have hSing : L.re <=
      (3 / 4 : Real) * d * Real.log (r / eps) := by
    dsimp [L, f]
    exact hSingular eps hEps hEpsR
  have hAwayNorm : norm R <= M := by
    dsimp [R, f]
    exact hAway eps hEps.le hEpsLe
  have hAwayRe : R.re <= M :=
    (le_trans (le_trans (le_abs_self R.re) (Complex.abs_re_le_norm R))
      hAwayNorm)
  have hTRe : T.re = L.re + R.re := by
    have hRe := congrArg Complex.re hDecomp
    simpa using hRe.symm
  rw [hTRe]
  linarith

theorem quadraticDedekindRealRightmostRayCompactIntegral_re_tendsto_atBot
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real}
    (hZero : quadraticDedekindZetaContinuation D (beta : Complex) = 0)
    (hBetaPos : 0 < beta) (hBetaOne : beta < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        (intervalIntegral
          (quadraticDedekindJMellinShiftIntegrandFilled D
            (quadraticDedekindRightmostRayPoint (beta : Complex) eps))
          0 1 volume).re)
      (nhdsWithin 0 (Ioi (0 : Real))) atBot := by
  choose d r M hdNeg hrPos hrHalf hrGap hMNonneg hUpper using
    exists_quadraticDedekindRealRightmostRayCompactIntegral_re_log_upperBound
      D hZero hBetaPos hBetaOne hRay
  have hInv : Tendsto (fun eps : Real => Inv.inv eps)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    simpa using (tendsto_inv_nhdsGT_zero :
      Tendsto (fun eps : Real => Inv.inv eps)
        (nhdsWithin 0 (Ioi (0 : Real))) atTop)
  have hRatio : Tendsto (fun eps : Real => r / eps)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    have hMul := Tendsto.const_mul_atTop hrPos hInv
    simpa [div_eq_mul_inv] using hMul
  have hLog : Tendsto (fun eps : Real => Real.log (r / eps))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop :=
    Real.tendsto_log_atTop.comp hRatio
  have hCoefficient : (3 / 4 : Real) * d < 0 :=
    mul_neg_of_pos_of_neg (by norm_num) hdNeg
  have hScaled : Tendsto (fun eps : Real =>
      ((3 / 4 : Real) * d) * Real.log (r / eps))
      (nhdsWithin 0 (Ioi (0 : Real))) atBot :=
    Tendsto.const_mul_atTop_of_neg hCoefficient hLog
  have hUpperTendsto : Tendsto (fun eps : Real =>
      (3 / 4 : Real) * d * Real.log (r / eps) + M)
      (nhdsWithin 0 (Ioi (0 : Real))) atBot := by
    simpa [mul_assoc] using
      (tendsto_atBot_add_const_right
        (nhdsWithin 0 (Ioi (0 : Real))) M hScaled)
  have hSmall : Filter.Eventually (fun eps : Real => eps <= r / 2)
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    have hNhd : Membership.mem (nhds (0 : Real)) (Iio (r / 2)) :=
      Iio_mem_nhds (by positivity)
    have hNhdWithin : Filter.Eventually (fun eps : Real => eps < r / 2)
        (nhdsWithin 0 (Ioi (0 : Real))) :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hNhd
    filter_upwards [hNhdWithin] with eps hEps
    exact hEps.le
  have hEventualUpper : Filter.Eventually (fun eps : Real =>
      (intervalIntegral
        (quadraticDedekindJMellinShiftIntegrandFilled D
          (quadraticDedekindRightmostRayPoint (beta : Complex) eps))
        0 1 volume).re <=
          (3 / 4 : Real) * d * Real.log (r / eps) + M)
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    filter_upwards [self_mem_nhdsWithin, hSmall] with eps hEps hEpsLe
    exact hUpper eps (mem_Ioi.mp hEps) hEpsLe
  exact tendsto_atBot_mono'
    (nhdsWithin 0 (Ioi (0 : Real))) hEventualUpper hUpperTendsto

theorem quadraticDedekindLandauPositiveRealContinuationFilledSplit_realRightmostRay_tendsto_atBot
    (D : NumberField.OddFundamentalDiscriminant)
    {X b beta : Real} (hX : 3 <= X)
    (hZero : quadraticDedekindZetaContinuation D (beta : Complex) = 0)
    (hBetaHalf : (1 / 2 : Real) < beta) (hBetaOne : beta < 1)
    (hFrontierB : 1 - beta < b)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b
          (1 - beta - eps))
      (nhdsWithin 0 (Ioi (0 : Real))) atBot := by
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let point : Real -> Complex := fun eps : Real =>
    quadraticDedekindRightmostRayPoint (beta : Complex) eps
  let compact : Real -> Real := fun eps : Real =>
    (quadraticDedekindJShiftedComplexContinuationFilledCompact D
      (point eps)).re
  let correction : Real -> Real := fun eps : Real =>
    (quadraticDedekindJShiftedComplexContinuationFilledLarge D (point eps) -
      quadraticDedekindJComplexMellinStartup D X (point eps) +
      Robin1984.nicolasLandauRpowComplexContinuation X b (point eps)).re
  have hBetaPos : 0 < beta := lt_trans (by norm_num) hBetaHalf
  have hCompact : Tendsto compact l atBot := by
    have hBase :=
      quadraticDedekindRealRightmostRayCompactIntegral_re_tendsto_atBot
        D hZero hBetaPos hBetaOne hRay
    simpa [l, compact, point,
      quadraticDedekindJShiftedComplexContinuationFilledCompact,
      intervalIntegral.integral_of_le zero_le_one] using hBase
  let endpoint : Complex := ((1 - beta : Real) : Complex)
  have hEndpointPos : 0 < 1 - beta := by linarith
  have hEndpointHalf : 1 - beta < 1 / 2 := by linarith
  have hEndpointEq : point 0 = endpoint := by
    dsimp [point, endpoint, quadraticDedekindRightmostRayPoint]
    push_cast
    ring
  have hLarge : AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledLarge D)
      endpoint := by
    simpa [endpoint] using
      (quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_pos_real
        D hEndpointPos hEndpointHalf)
  have hStartup : AnalyticAt Complex
      (quadraticDedekindJComplexMellinStartup D X) endpoint :=
    quadraticDedekindJComplexMellinStartup_analyticAt D hX endpoint
  have hEndpointNeB : Not (endpoint = (b : Complex)) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    change 1 - beta = b at hRe
    linarith
  have hRpow : AnalyticAt Complex
      (Robin1984.nicolasLandauRpowComplexContinuation X b) endpoint :=
    Robin1984.nicolasLandauRpowComplexContinuation_analyticAt
      (lt_of_lt_of_le (by norm_num) hX) hEndpointNeB
  have hCorrectionAnalytic : AnalyticAt Complex (fun z : Complex =>
      quadraticDedekindJShiftedComplexContinuationFilledLarge D z -
        quadraticDedekindJComplexMellinStartup D X z +
        Robin1984.nicolasLandauRpowComplexContinuation X b z) endpoint :=
    (hLarge.sub hStartup).add hRpow
  have hPoint : Tendsto point l (nhds endpoint) := by
    have hContinuous : ContinuousAt point 0 := by
      dsimp [point, quadraticDedekindRightmostRayPoint]
      fun_prop
    simpa [hEndpointEq] using
      hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  let correction0 : Real :=
    (quadraticDedekindJShiftedComplexContinuationFilledLarge D endpoint -
      quadraticDedekindJComplexMellinStartup D X endpoint +
      Robin1984.nicolasLandauRpowComplexContinuation X b endpoint).re
  have hCorrection : Tendsto correction l (nhds correction0) := by
    have hComplex := hCorrectionAnalytic.continuousAt.tendsto.comp hPoint
    have hReal :=
      Complex.continuous_re.continuousAt.tendsto.comp hComplex
    simpa [correction, correction0, Function.comp_def] using hReal
  have hSum : Tendsto (fun eps : Real =>
      compact eps + correction eps) l atBot :=
    Tendsto.atBot_add hCompact hCorrection
  have hEq : (fun eps : Real =>
      quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b
        (1 - beta - eps)) =
      fun eps : Real => compact eps + correction eps := by
    funext eps
    have hCast : ((1 - beta - eps : Real) : Complex) =
        1 - (beta : Complex) - (eps : Complex) := by
      push_cast
      ring
    unfold quadraticDedekindLandauPositiveRealContinuationFilledSplit
      quadraticDedekindLandauPositiveComplexContinuationFilledSplit
      quadraticDedekindJShiftedComplexContinuationFilledSplit
    dsimp [compact, correction, point,
      quadraticDedekindRightmostRayPoint]
    rw [hCast]
    ring
  simpa [hEq] using hSum

theorem exists_quadraticDedekindNicolasJ_omegaMinus_of_real_rightmost_zero
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real}
    (hZero : quadraticDedekindZetaContinuation D (beta : Complex) = 0)
    (hBetaHalf : (1 / 2 : Real) < beta) (hBetaOne : beta < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0)) :
    Exists fun b : Real => And (0 < b) (And (b < 1 / 2)
      (Robin1984.AtTopOmegaMinus (quadraticDedekindNicolasJ D)
        (fun x : Real => x ^ (-b)))) := by
  let b : Real := ((1 - beta) + 1 / 2) / 2
  have hBetaPos : 0 < beta := lt_trans (by norm_num) hBetaHalf
  have hbPos : 0 < b := by
    dsimp [b]
    linarith
  have hbLower : 1 - beta < b := by
    dsimp [b]
    linarith
  have hbHalf : b < 1 / 2 := by
    dsimp [b]
    linarith
  refine Exists.intro b (And.intro hbPos (And.intro hbHalf ?_))
  by_contra hNot
  choose X hX hPos using
    exists_quadraticDedekindLandauPositiveTail_start D hNot
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let H : Real -> Real := fun eps : Real =>
    quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b
      (1 - beta - eps)
  have hH : Tendsto H l atBot := by
    simpa [H, l] using
      quadraticDedekindLandauPositiveRealContinuationFilledSplit_realRightmostRay_tendsto_atBot
        D hX hZero hBetaHalf hBetaOne hbLower hRay
  have hHNeg : Filter.Eventually (fun eps : Real => H eps < 0) l :=
    hH (Iio_mem_atBot (0 : Real))
  have hImpossible : Filter.Eventually (fun _ : Real => False) l := by
    filter_upwards [self_mem_nhdsWithin, hHNeg] with eps hEps hNeg
    have hSigma : 1 - beta - eps < 1 - beta := by
      linarith [mem_Ioi.mp hEps]
    have hEq :=
      quadraticDedekindLandau_mgf_eq_realContinuation_below_realZero
        D hX hbPos hBetaPos hBetaHalf hBetaOne hRay hPos hbLower hSigma
    have hNonneg : 0 <= mgf (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b)
        (1 - beta - eps) := mgf_nonneg
    dsimp [H] at hNeg
    linarith
  choose eps hFalse using hImpossible.exists
  exact hFalse


end

end RobinBV.NumberField
