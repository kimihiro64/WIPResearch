import RobinBV.NumberField.Proof.QuadraticDedekindNicolasRealResidue

/-!
# Real-zero Landau frontier

Focused infrastructure for the quadratic Dedekind Nicolas-Landau Omega theorem.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section
theorem exists_quadraticDedekindRealZeroCompactTubeRadius
    (D : NumberField.OddFundamentalDiscriminant)
    {beta sigma : Real}
    (hBetaPos : 0 < beta)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0))
    (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 - beta) :
    Exists fun R : Real => And (0 < R)
      (forall z : Complex,
        Membership.mem (Metric.ball (sigma : Complex) R) z ->
          And (Not (z = 0))
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              And (Not ((((u + 1 : Real) : Complex) - z) = 0))
                (Not (quadraticDedekindZetaPoleFactor D
                  (((u + 1 : Real) : Complex) - z) = 0)))) := by
  have hCenterNe : Not ((sigma : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hSigmaPos.ne'
  have hZeroNhd : Filter.Eventually (fun z : Complex => Not (z = 0))
      (nhds (sigma : Complex)) := continuousAt_id.eventually_ne hCenterNe
  have hShiftNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not ((((u + 1 : Real) : Complex) - z) = 0))
      (nhds (sigma : Complex)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    have hAt : Not
        ((((u + 1 : Real) : Complex) - (sigma : Complex)) = 0) := by
      intro hEq
      have hRe := congrArg Complex.re hEq
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hRe
      linarith [hu.1, hBetaPos]
    let G : Prod Complex Real -> Complex := fun p =>
      ((p.2 + 1 : Real) : Complex) - p.1
    have hContinuous : Continuous G := by
      dsimp [G]
      fun_prop
    have hPair : Not (G ((sigma : Complex), u) = 0) := by
      simpa [G] using hAt
    exact hContinuous.continuousAt.eventually_ne hPair
  have hFactorNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not (quadraticDedekindZetaPoleFactor D
          (((u + 1 : Real) : Complex) - z) = 0))
      (nhds (sigma : Complex)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    let t : Real := u + 1 - sigma
    have hShift : (((u + 1 : Real) : Complex) - (sigma : Complex)) =
        (t : Complex) := by
      dsimp [t]
      push_cast
      ring
    have htBeta : beta < t := by
      dsimp [t]
      linarith [hu.1]
    have htPos : 0 < t := hBetaPos.trans htBeta
    have hFactor : Not
        (quadraticDedekindZetaPoleFactor D (t : Complex) = 0) := by
      by_cases htOne : t = 1
      next =>
        rw [htOne]
        exact quadraticDedekindZetaPoleFactor_one_ne_zero D
      next =>
        have hZeta : Not
            (quadraticDedekindZetaContinuation D (t : Complex) = 0) := by
          have hPoint : (beta : Complex) + ((t - beta : Real) : Complex) =
              (t : Complex) := by
            push_cast
            ring
          rw [<- hPoint]
          exact hRay (t - beta) (by linarith)
        intro hFactorZero
        have htOneComplex : Not ((t : Complex) = 1) := by
          exact_mod_cast htOne
        have hIdentity :=
          quadraticDedekindZetaContinuation_eq_poleFactor_div D
            htOneComplex
        rw [hFactorZero, zero_div] at hIdentity
        exact hZeta hIdentity
    let G : Prod Complex Real -> Complex := fun p =>
      quadraticDedekindZetaPoleFactor D
        (((p.2 + 1 : Real) : Complex) - p.1)
    have hContinuous : Continuous G := by
      dsimp [G]
      exact (quadraticDedekindZetaPoleFactor_differentiable D).continuous.comp
        (by fun_prop)
    have hPair : Not (G ((sigma : Complex), u) = 0) := by
      dsimp [G]
      rw [hShift]
      exact hFactor
    exact hContinuous.continuousAt.eventually_ne hPair
  have hAll := hZeroNhd.and (hShiftNhd.and hFactorNhd)
  choose R hRPos hR using Metric.mem_nhds_iff.1 hAll
  refine Exists.intro R (And.intro hRPos ?_)
  intro z hz
  have hzGood := hR hz
  exact And.intro hzGood.1 (fun u hu =>
    And.intro (hzGood.2.1 u hu) (hzGood.2.2 u hu))

theorem quadraticDedekindJShiftedComplexContinuationFilledSplit_analyticAt_pos_below_realZero
    (D : NumberField.OddFundamentalDiscriminant)
    {beta sigma : Real}
    (hBetaPos : 0 < beta)
    (hBetaHalf : (1 / 2 : Real) < beta)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0))
    (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 - beta) :
    AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledSplit D)
      (sigma : Complex) := by
  choose R hRPos hGood using
    exists_quadraticDedekindRealZeroCompactTubeRadius
      D hBetaPos hRay hSigmaPos hSigma
  have hCompact :=
    quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_of_tube
      D hRPos hGood
  have hSigmaHalf : sigma < 1 / 2 := by linarith [hBetaHalf]
  have hLarge :=
    quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_pos_real
      D hSigmaPos hSigmaHalf
  unfold quadraticDedekindJShiftedComplexContinuationFilledSplit
  exact hCompact.add hLarge

theorem quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_pos_below_realZero
    (D : NumberField.OddFundamentalDiscriminant)
    {X b beta sigma : Real} (hX : 3 <= X) (hb : 0 < b)
    (hBetaPos : 0 < beta)
    (hBetaHalf : (1 / 2 : Real) < beta)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0))
    (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 - beta)
    (hSigmaB : sigma < b) :
    AnalyticAt Real
      (quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b)
      sigma := by
  have hShift :=
    quadraticDedekindJShiftedComplexContinuationFilledSplit_analyticAt_pos_below_realZero
      D hBetaPos hBetaHalf hRay hSigmaPos hSigma
  have hStartup :=
    quadraticDedekindJComplexMellinStartup_analyticAt D hX (sigma : Complex)
  have hPointNe : Not ((sigma : Complex) = (b : Complex)) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    simp only [Complex.ofReal_re] at hRe
    linarith
  have hRpow := Robin1984.nicolasLandauRpowComplexContinuation_analyticAt
    (lt_of_lt_of_le (by norm_num) hX) hPointNe
  have hComplex : AnalyticAt Complex
      (quadraticDedekindLandauPositiveComplexContinuationFilledSplit D X b)
      (sigma : Complex) := by
    unfold quadraticDedekindLandauPositiveComplexContinuationFilledSplit
    exact (hShift.sub hStartup).add hRpow
  unfold quadraticDedekindLandauPositiveRealContinuationFilledSplit
  exact Robin1984.realAnalyticAt_re_comp_of_complexAnalyticAt hComplex

theorem quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_below_realZero
    (D : NumberField.OddFundamentalDiscriminant)
    {X b beta sigma : Real} (hX : 3 <= X) (hb : 0 < b)
    (hBetaPos : 0 < beta)
    (hBetaHalf : (1 / 2 : Real) < beta)
    (hBetaOne : beta < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0))
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    (hFrontierB : 1 - beta < b)
    (hSigma : sigma < 1 - beta) :
    AnalyticAt Real
      (quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b)
      sigma := by
  rcases lt_trichotomy sigma 0 with hNeg | hZero | hPosSigma
  next =>
    exact
      quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_neg
        D hX hb hPos hNeg
  next =>
    subst sigma
    exact
      quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_zero
        D hX hb
  next =>
    exact
      quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_pos_below_realZero
        D hX hb hBetaPos hBetaHalf hRay hPosSigma hSigma
          (lt_trans hSigma hFrontierB)

theorem Iio_realZeroFrontier_subset_interior_integrableExpSet_quadraticDedekindLandau
    (D : NumberField.OddFundamentalDiscriminant)
    {X b beta : Real} (hX : 3 <= X) (hb : 0 < b)
    (hBetaPos : 0 < beta) (hBetaHalf : (1 / 2 : Real) < beta)
    (hBetaOne : beta < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0))
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    (hFrontierB : 1 - beta < b) :
    Iio (1 - beta) <= interior
      (integrableExpSet (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b)) := by
  apply Robin1984.Iio_subset_interior_integrableExpSet_of_analyticContinuation
    (H := quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b)
  next => exact ae_log_nonneg_quadraticDedekindLandauPositiveMeasure D hX
  next =>
    intro a ha
    exact Iio_zero_subset_interior_integrableExpSet_quadraticDedekindLandau
      D hX hb hPos ha
  next =>
    intro sigma hSigma
    exact
      quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_below_realZero
        D hX hb hBetaPos hBetaHalf hBetaOne hRay hPos hFrontierB hSigma
  next =>
    intro a ha
    exact
      (quadraticDedekindLandauPositiveRealContinuationFilledSplit_eq_mgf_of_neg
        D hX hb hPos ha).symm

theorem quadraticDedekindLandau_mgf_eq_realContinuation_below_realZero
    (D : NumberField.OddFundamentalDiscriminant)
    {X b beta sigma : Real} (hX : 3 <= X) (hb : 0 < b)
    (hBetaPos : 0 < beta) (hBetaHalf : (1 / 2 : Real) < beta)
    (hBetaOne : beta < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0))
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    (hFrontierB : 1 - beta < b)
    (hSigma : sigma < 1 - beta) :
    mgf (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b) sigma =
      quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b sigma := by
  let F : Real -> Real := mgf (fun x : Real => Real.log x)
    (quadraticDedekindLandauPositiveMeasure D X b)
  let G : Real -> Real :=
    quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b
  have hInterior :=
    Iio_realZeroFrontier_subset_interior_integrableExpSet_quadraticDedekindLandau
      D hX hb hBetaPos hBetaHalf hBetaOne hRay hPos hFrontierB
  have hF : AnalyticOnNhd Real F (Iio (1 - beta)) := by
    intro a ha
    dsimp [F]
    exact analyticAt_mgf (hInterior ha)
  have hG : AnalyticOnNhd Real G (Iio (1 - beta)) := by
    intro a ha
    dsimp [G]
    exact
      quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_below_realZero
        D hX hb hBetaPos hBetaHalf hBetaOne hRay hPos hFrontierB
          (mem_Iio.mp ha)
  have hBaseMem : (-1 : Real) < 1 - beta := by linarith
  have hEqNhd : Filter.EventuallyEq (nhds (-1 : Real)) F G := by
    filter_upwards [Iio_mem_nhds (by norm_num : (-1 : Real) < 0)] with a ha
    dsimp [F, G]
    exact
      (quadraticDedekindLandauPositiveRealContinuationFilledSplit_eq_mgf_of_neg
        D hX hb hPos ha).symm
  have hEqOn : EqOn F G (Iio (1 - beta)) :=
    hF.eqOn_of_preconnected_of_eventuallyEq hG
      (convex_Iio (1 - beta)).isPreconnected hBaseMem hEqNhd
  exact hEqOn hSigma

theorem quadraticDedekindJMellinShiftIntegrandFilled_eq_raw_realRightmostRay
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real}
    (hBetaPos : 0 < beta)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0))
    {eps u : Real} (hEps : 0 < eps) (hU : 0 < u)
    (hBelowOne : eps + u < 1 - beta) :
    quadraticDedekindJMellinShiftIntegrandFilled D
        (quadraticDedekindRightmostRayPoint (beta : Complex) eps) u =
      quadraticDedekindJMellinShiftIntegrand D
        (quadraticDedekindRightmostRayPoint (beta : Complex) eps) u := by
  have hzPos : 0 < 1 - beta - eps := by linarith
  have hzZero : Not
      (quadraticDedekindRightmostRayPoint (beta : Complex) eps = 0) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    unfold quadraticDedekindRightmostRayPoint at hRe
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.zero_re] at hRe
    linarith
  let s : Complex := (beta : Complex) + ((eps + u : Real) : Complex)
  have hShift :
      (((u + 1 : Real) : Complex) -
          quadraticDedekindRightmostRayPoint (beta : Complex) eps) = s := by
    dsimp [s, quadraticDedekindRightmostRayPoint]
    push_cast
    ring
  have hsRe : s.re = beta + eps + u := by
    dsimp [s]
    ring
  have hsZero : Not (s = 0) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    rw [hsRe, Complex.zero_re] at hRe
    linarith
  have hsOne : Not (s = 1) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    rw [hsRe, Complex.one_re] at hRe
    linarith
  have hZeta : Not (quadraticDedekindZetaContinuation D s = 0) := by
    dsimp [s]
    exact hRay (eps + u) (by linarith)
  let base : Complex := ((u + 1 : Real) : Complex)
  have hBaseZero : Not (base = 0) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    change u + 1 = 0 at hRe
    linarith
  have hBaseOne : Not (base = 1) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    change u + 1 = 1 at hRe
    linarith
  have hBaseZeta : Not
      (quadraticDedekindZetaContinuation D base = 0) := by
    unfold quadraticDedekindZetaContinuation
    apply mul_ne_zero
    next => exact riemannZeta_ne_zero_of_one_le_re (by dsimp [base]; simp; linarith)
    next =>
      exact D.character.LFunction_ne_zero_of_one_le_re
        (Or.inl (quadraticCharacter_ne_one D)) (by dsimp [base]; simp; linarith)
  have hBaseEq :=
    quadraticDedekindPsiMellinTailContinuation_eq_filled
      D hBaseZero hBaseOne hBaseZeta
  have hShiftEq :=
    quadraticDedekindPsiMellinTailContinuation_eq_filled
      D hsZero hsOne hZeta
  unfold quadraticDedekindJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzZero]
  unfold slope
  change ((u + 1 : Real) : Complex) *
      (Inv.inv
          (quadraticDedekindRightmostRayPoint (beta : Complex) eps - 0) *
        (quadraticDedekindJShiftNumeratorFilled D
            (quadraticDedekindRightmostRayPoint (beta : Complex) eps) u -
          quadraticDedekindJShiftNumeratorFilled D 0 u)) =
    quadraticDedekindJMellinShiftIntegrand D
      (quadraticDedekindRightmostRayPoint (beta : Complex) eps) u
  rw [quadraticDedekindJShiftNumeratorFilled_zero]
  simp only [smul_eq_mul, vsub_eq_sub, sub_zero, inv_mul_eq_div]
  unfold quadraticDedekindJShiftNumeratorFilled
    quadraticDedekindJMellinShiftIntegrand
  rw [hShift]
  change ((u + 1 : Real) : Complex) *
      ((quadraticDedekindPsiMellinTailContinuationFilled D s -
        (3 : Complex) ^
            (quadraticDedekindRightmostRayPoint (beta : Complex) eps) *
          quadraticDedekindPsiMellinTailContinuationFilled D base) /
        quadraticDedekindRightmostRayPoint (beta : Complex) eps) =
    ((u + 1 : Real) : Complex) *
      ((quadraticDedekindPsiMellinTailContinuation D 3 s -
        (3 : Complex) ^
            (quadraticDedekindRightmostRayPoint (beta : Complex) eps) *
          quadraticDedekindPsiMellinTailContinuation D 3 base) /
        quadraticDedekindRightmostRayPoint (beta : Complex) eps)
  rw [<- hShiftEq, <- hBaseEq]

theorem quadraticDedekindJRightmostRayTranslatedScaledKernelFilled_eq_raw_real
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real}
    (hBetaPos : 0 < beta)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0))
    {eps v : Real} (hEps : 0 < eps) (hEpsV : eps < v)
    (hVBelow : v < 1 - beta) :
    quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
        D (beta : Complex) eps v =
      quadraticDedekindJRightmostRayTranslatedScaledKernel
        D (beta : Complex) eps v := by
  unfold quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
    quadraticDedekindJRightmostRayTranslatedScaledKernel
  rw [quadraticDedekindJMellinShiftIntegrandFilled_eq_raw_realRightmostRay
    D hBetaPos hRay hEps (by linarith) (by linarith)]

theorem exists_quadraticDedekindRealRightmostRayScaledKernelFilled_uniform_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real}
    (hZero : quadraticDedekindZetaContinuation D (beta : Complex) = 0)
    (hBetaPos : 0 < beta) (hBetaOne : beta < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0)) :
    Exists fun d : Real => Exists fun r : Real =>
      And (d < 0) (And (0 < r) (And (r < 1 / 2)
        (And (r < 1 - beta)
          (forall eps v : Real, 0 < eps -> eps < v -> v <= r ->
            norm
              (quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
                D (beta : Complex) eps v - (d : Complex)) <= (-d) / 4)))) := by
  choose d r0 hdNeg hr0Pos hr0Half hRaw using
    exists_quadraticDedekindRealRightmostRayScaledKernel_uniform_neg
      D hZero hBetaPos hBetaOne
  let r : Real := min r0 ((1 - beta) / 2)
  have hGapPos : 0 < 1 - beta := by linarith
  have hrPos : 0 < r := by
    dsimp [r]
    exact lt_min hr0Pos (by positivity)
  have hrHalf : r < 1 / 2 :=
    lt_of_le_of_lt (min_le_left _ _) hr0Half
  have hrGap : r < 1 - beta :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine Exists.intro d (Exists.intro r
    (And.intro hdNeg (And.intro hrPos (And.intro hrHalf
      (And.intro hrGap ?_)))))
  intro eps v hEps hEpsV hVr
  rw [quadraticDedekindJRightmostRayTranslatedScaledKernelFilled_eq_raw_real
    D hBetaPos hRay hEps hEpsV (hVr.trans_lt hrGap)]
  exact hRaw eps v hEps hEpsV (hVr.trans (min_le_left _ _))

theorem quadraticDedekindJRightmostRayTranslatedScaledKernelFilled_intervalIntegrable_real
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real} (hBetaPos : 0 < beta)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0))
    {eps r : Real} (hEps : 0 < eps) (hEpsR : eps < r)
    (hRBelow : r < 1 - beta) (hWidth : r - eps <= 1) :
    IntervalIntegrable
      (quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
        D (beta : Complex) eps) volume eps r := by
  have hzZero : Not
      (quadraticDedekindRightmostRayPoint (beta : Complex) eps = 0) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    unfold quadraticDedekindRightmostRayPoint at hRe
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.zero_re] at hRe
    linarith
  apply ContinuousOn.intervalIntegrable
  intro v hv
  have hvIcc : Membership.mem (Icc eps r) v := by
    simpa [uIcc, min_eq_left hEpsR.le, max_eq_right hEpsR.le] using hv
  have hU : 0 <= v - eps := by linarith [hvIcc.1]
  have hULe : v - eps <= 1 := by linarith [hvIcc.2]
  let s : Complex := (beta : Complex) + (v : Complex)
  have hsRe : s.re = beta + v := by
    dsimp [s]
  have hsZero : Not (s = 0) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    rw [hsRe, Complex.zero_re] at hRe
    linarith [hBetaPos, hvIcc.1, hEps]
  have hsOne : Not (s = 1) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    rw [hsRe, Complex.one_re] at hRe
    linarith [hvIcc.2]
  have hVPos : 0 < v := hEps.trans_le hvIcc.1
  have hZeta : Not (quadraticDedekindZetaContinuation D s = 0) := by
    dsimp [s]
    exact hRay v hVPos
  have hFactor : Not (quadraticDedekindZetaPoleFactor D s = 0) := by
    intro hFactorZero
    have hIdentity :=
      quadraticDedekindZetaContinuation_eq_poleFactor_div D hsOne
    rw [hFactorZero, zero_div] at hIdentity
    exact hZeta hIdentity
  have hShift :
      ((((v - eps + 1 : Real) : Complex) -
          quadraticDedekindRightmostRayPoint (beta : Complex) eps)) = s := by
    dsimp [s, quadraticDedekindRightmostRayPoint]
    push_cast
    ring
  have hShiftZero : Not
      ((((v - eps + 1 : Real) : Complex) -
          quadraticDedekindRightmostRayPoint (beta : Complex) eps) = 0) := by
    rw [hShift]
    exact hsZero
  have hShiftFactor : Not
      (quadraticDedekindZetaPoleFactor D
        (((v - eps + 1 : Real) : Complex) -
          quadraticDedekindRightmostRayPoint (beta : Complex) eps) = 0) := by
    rw [hShift]
    exact hFactor
  have hJoint :=
    quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne D
      (u := v - eps)
      (z := quadraticDedekindRightmostRayPoint (beta : Complex) eps)
      hU hzZero hShiftZero hShiftFactor
  have hEmbed : ContinuousAt (fun w : Real =>
      (w - eps,
        quadraticDedekindRightmostRayPoint (beta : Complex) eps)) v := by
    fun_prop
  have hTail : ContinuousAt (fun w : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D
        (quadraticDedekindRightmostRayPoint (beta : Complex) eps)
        (w - eps)) v := by
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    simpa [Function.comp_def] using hComp
  have hCast : ContinuousAt (fun w : Real => (w : Complex)) v := by
    fun_prop
  unfold quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
  exact (hCast.mul hTail).continuousWithinAt

theorem exists_quadraticDedekindRealRightmostRayScaledKernel_log_interval_estimate
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real}
    (hZero : quadraticDedekindZetaContinuation D (beta : Complex) = 0)
    (hBetaPos : 0 < beta) (hBetaOne : beta < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0)) :
    Exists fun d : Real => Exists fun r : Real =>
      And (d < 0) (And (0 < r) (And (r < 1 / 2)
        (And (r < 1 - beta)
          (forall eps : Real, 0 < eps -> eps < r ->
            norm (intervalIntegral (fun v : Real =>
                HSMul.hSMul (Inv.inv v)
                  (quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
                    D (beta : Complex) eps v)) eps r volume -
              HSMul.hSMul (Real.log (r / eps)) (d : Complex)) <=
                ((-d) / 4) * abs (Real.log (r / eps)))))) := by
  choose d r hdNeg hrPos hrHalf hrGap hUniform using
    exists_quadraticDedekindRealRightmostRayScaledKernelFilled_uniform_neg
      D hZero hBetaPos hBetaOne hRay
  refine Exists.intro d (Exists.intro r
    (And.intro hdNeg (And.intro hrPos (And.intro hrHalf
      (And.intro hrGap ?_)))))
  intro eps hEps hEpsR
  have hInt :=
    quadraticDedekindJRightmostRayTranslatedScaledKernelFilled_intervalIntegrable_real
      D hBetaPos hRay hEps hEpsR hrGap (by linarith)
  apply Robin1984.norm_intervalIntegral_inv_smul_sub_le_of_intervalIntegrable
    hInt hEps hrPos (div_nonneg (neg_nonneg.mpr hdNeg.le) (by norm_num))
  intro v hv
  have hvIoc : Membership.mem (Ioc eps r) v := by
    simpa [uIoc, min_eq_left hEpsR.le, max_eq_right hEpsR.le] using hv
  exact hUniform eps v hEps hvIoc.1 hvIoc.2

theorem exists_quadraticDedekindRealRightmostRayCompactSingularIntegral_re_upperBound
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real}
    (hZero : quadraticDedekindZetaContinuation D (beta : Complex) = 0)
    (hBetaPos : 0 < beta) (hBetaOne : beta < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        ((beta : Complex) + (v : Complex)) = 0)) :
    Exists fun d : Real => Exists fun r : Real =>
      And (d < 0) (And (0 < r) (And (r < 1 / 2)
        (And (r < 1 - beta)
          (forall eps : Real, 0 < eps -> eps < r ->
            (intervalIntegral
              (quadraticDedekindJMellinShiftIntegrandFilled D
                (quadraticDedekindRightmostRayPoint (beta : Complex) eps))
              0 (r - eps) volume).re <=
                (3 / 4 : Real) * d * Real.log (r / eps))))) := by
  choose d r hdNeg hrPos hrHalf hrGap hEstimate using
    exists_quadraticDedekindRealRightmostRayScaledKernel_log_interval_estimate
      D hZero hBetaPos hBetaOne hRay
  refine Exists.intro d (Exists.intro r
    (And.intro hdNeg (And.intro hrPos (And.intro hrHalf
      (And.intro hrGap ?_)))))
  intro eps hEps hEpsR
  let I : Complex := intervalIntegral (fun v : Real =>
      HSMul.hSMul (Inv.inv v)
        (quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
          D (beta : Complex) eps v)) eps r volume
  let A : Complex := HSMul.hSMul (Real.log (r / eps)) (d : Complex)
  have hRatio : 1 < r / eps := (one_lt_div hEps).mpr hEpsR
  have hLogPos : 0 < Real.log (r / eps) := Real.log_pos hRatio
  have hErr : norm (I - A) <=
      ((-d) / 4) * Real.log (r / eps) := by
    dsimp [I, A]
    simpa [abs_of_pos hLogPos] using hEstimate eps hEps hEpsR
  have hReDiff : I.re - A.re <= norm (I - A) := by
    calc
      I.re - A.re = (I - A).re := by simp
      _ <= abs ((I - A).re) := le_abs_self _
      _ <= norm (I - A) := Complex.abs_re_le_norm _
  have hARe : A.re = Real.log (r / eps) * d := by
    dsimp [A]
    simp
  have hIRe : I.re <= (3 / 4 : Real) * d * Real.log (r / eps) := by
    rw [hARe] at hReDiff
    nlinarith [hErr]
  dsimp [I] at hIRe
  have hIntegralEq :=
    quadraticDedekindRightmostRay_weighted_scaledKernelFilled_interval_eq
      D (rho := (beta : Complex)) hEps hEpsR
  have hIntegralRe := congrArg Complex.re hIntegralEq
  have hIntegralRe' :
      (intervalIntegral (fun v : Real =>
        ((Inv.inv v : Real) : Complex) *
          quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
            D (beta : Complex) eps v) eps r volume).re =
        (intervalIntegral
          (quadraticDedekindJMellinShiftIntegrandFilled D
            (quadraticDedekindRightmostRayPoint (beta : Complex) eps))
          0 (r - eps) volume).re := by
    simpa [smul_eq_mul] using hIntegralRe
  rw [hIntegralRe'] at hIRe
  exact hIRe


end

end RobinBV.NumberField
