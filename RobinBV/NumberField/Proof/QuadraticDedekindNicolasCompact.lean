import RobinBV.NumberField.Proof.QuadraticDedekindNicolasContinuation

/-!
# Compact filled quadratic Dedekind continuation

Focused infrastructure for the quadratic Dedekind Nicolas-Landau Omega theorem.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section
theorem quadraticDedekindZetaPoleFactor_ne_zero_of_one_le_re
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 <= s.re) :
    Not (quadraticDedekindZetaPoleFactor D s = 0) := by
  by_cases hsOne : s = 1
  next =>
    subst s
    exact quadraticDedekindZetaPoleFactor_one_ne_zero D
  next =>
    unfold quadraticDedekindZetaPoleFactor
    apply mul_ne_zero
    next =>
      exact Robin1984.nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne
        (riemannZeta_ne_zero_of_one_le_re hs)
    next =>
      exact D.character.LFunction_ne_zero_of_one_le_re
        (Or.inl (quadraticCharacter_ne_one D)) hs

theorem quadraticDedekindPsiMellinTailContinuationFilled_analyticAt_of_one_le_re
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 <= s.re) :
    AnalyticAt Complex
      (quadraticDedekindPsiMellinTailContinuationFilled D) s := by
  have hsZero : Not (s = 0) := by
    intro hEq
    subst s
    norm_num at hs
  exact quadraticDedekindPsiMellinTailContinuationFilled_analyticAt D
    hsZero (quadraticDedekindZetaPoleFactor_ne_zero_of_one_le_re D hs)

theorem quadraticDedekindJShiftNumeratorFilled_analyticAt
    (D : NumberField.OddFundamentalDiscriminant)
    {u : Real} (hu : 0 <= u) {z : Complex}
    (hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0))
    (hFactor : Not (quadraticDedekindZetaPoleFactor D
      (((u + 1 : Real) : Complex) - z) = 0)) :
    AnalyticAt Complex
      (fun w : Complex => quadraticDedekindJShiftNumeratorFilled D w u) z := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 <= s0.re := by
    dsimp [s0]
    linarith
  have hTail0 : AnalyticAt Complex
      (quadraticDedekindPsiMellinTailContinuationFilled D) s0 :=
    quadraticDedekindPsiMellinTailContinuationFilled_analyticAt_of_one_le_re
      D hs0
  have hTail1 : AnalyticAt Complex
      (quadraticDedekindPsiMellinTailContinuationFilled D) s1 := by
    apply quadraticDedekindPsiMellinTailContinuationFilled_analyticAt D
    next => simpa [s1, s0] using hShiftZero
    next => simpa [s1, s0] using hFactor
  have hAffine : AnalyticAt Complex (fun w : Complex => s0 - w) z :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex (fun w : Complex =>
      quadraticDedekindPsiMellinTailContinuationFilled D (s0 - w)) z := by
    have hComp := hTail1.comp_of_eq hAffine (by simp [s1])
    exact hComp.congr (Eventually.of_forall (fun _ => rfl))
  have hPower : AnalyticAt Complex (fun w : Complex =>
      (3 : Complex) ^ w) z := by
    have hDiff : Differentiable Complex (fun w : Complex =>
        (3 : Complex) ^ w) := by
      intro w
      exact DifferentiableAt.const_cpow differentiableAt_id
        (Or.inl (by norm_num))
    exact hDiff.analyticAt z
  unfold quadraticDedekindJShiftNumeratorFilled
  change AnalyticAt Complex (fun w : Complex =>
    quadraticDedekindPsiMellinTailContinuationFilled D (s0 - w) -
      (3 : Complex) ^ w *
        quadraticDedekindPsiMellinTailContinuationFilled D s0) z
  exact hShift.sub (hPower.mul analyticAt_const)

theorem quadraticDedekindJMellinShiftIntegrandFilled_analyticAt_zero
    (D : NumberField.OddFundamentalDiscriminant)
    {u : Real} (hu : 0 <= u) :
    AnalyticAt Complex
      (fun z : Complex => quadraticDedekindJMellinShiftIntegrandFilled D z u)
      0 := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  have hs0 : 1 <= s0.re := by
    dsimp [s0]
    linarith
  have hs0Zero : Not (s0 = 0) := by
    intro hEq
    have hRe := congrArg Complex.re hEq
    simp only [Complex.zero_re] at hRe
    linarith
  have hFactor : Not (quadraticDedekindZetaPoleFactor D s0 = 0) :=
    quadraticDedekindZetaPoleFactor_ne_zero_of_one_le_re D hs0
  have hNumerator : AnalyticAt Complex
      (fun z : Complex => quadraticDedekindJShiftNumeratorFilled D z u) 0 := by
    apply quadraticDedekindJShiftNumeratorFilled_analyticAt D hu
    next => simpa [s0] using hs0Zero
    next => simpa [s0] using hFactor
  choose p hp using hNumerator
  have hSlope : AnalyticAt Complex
      (dslope (fun z : Complex => quadraticDedekindJShiftNumeratorFilled D z u) 0)
      0 :=
    Exists.intro p.fslope hp.has_fpower_series_dslope_fslope
  unfold quadraticDedekindJMellinShiftIntegrandFilled
  exact analyticAt_const.mul hSlope

theorem quadraticDedekindJMellinShiftIntegrandFilled_analyticAt
    (D : NumberField.OddFundamentalDiscriminant)
    {u : Real} (hu : 0 <= u) {z : Complex}
    (hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0))
    (hFactor : Not (quadraticDedekindZetaPoleFactor D
      (((u + 1 : Real) : Complex) - z) = 0)) :
    AnalyticAt Complex
      (fun w : Complex => quadraticDedekindJMellinShiftIntegrandFilled D w u)
      z := by
  by_cases hz : z = 0
  next =>
    subst z
    exact quadraticDedekindJMellinShiftIntegrandFilled_analyticAt_zero D hu
  next =>
    have hNumerator := quadraticDedekindJShiftNumeratorFilled_analyticAt
      D hu hShiftZero hFactor
    let raw : Complex -> Complex := fun w =>
      ((u + 1 : Real) : Complex) *
        slope (fun v : Complex => quadraticDedekindJShiftNumeratorFilled D v u)
          0 w
    have hRaw : AnalyticAt Complex raw z := by
      have hDifference : AnalyticAt Complex (fun w : Complex =>
          quadraticDedekindJShiftNumeratorFilled D w u -
            quadraticDedekindJShiftNumeratorFilled D 0 u) z :=
        hNumerator.sub analyticAt_const
      have hDenominator : AnalyticAt Complex (fun w : Complex => w - 0) z :=
        analyticAt_id.sub analyticAt_const
      have hQuotient := hDifference.div hDenominator
        (sub_ne_zero.mpr hz)
      have hDiv : AnalyticAt Complex (fun w : Complex =>
          ((u + 1 : Real) : Complex) *
            ((quadraticDedekindJShiftNumeratorFilled D w u -
              quadraticDedekindJShiftNumeratorFilled D 0 u) / (w - 0))) z :=
        analyticAt_const.mul hQuotient
      have hRawEq : Filter.EventuallyEq (nhds z) raw
          (fun w : Complex => ((u + 1 : Real) : Complex) *
            ((quadraticDedekindJShiftNumeratorFilled D w u -
              quadraticDedekindJShiftNumeratorFilled D 0 u) / (w - 0))) :=
        Eventually.of_forall (fun w => by
          unfold raw slope
          simp only [smul_eq_mul, vsub_eq_sub, div_eq_mul_inv]
          ring)
      exact (analyticAt_congr hRawEq).mpr hDiv
    have hEq : Filter.EventuallyEq (nhds z)
        (fun w : Complex => quadraticDedekindJMellinShiftIntegrandFilled D w u)
        raw := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
      unfold quadraticDedekindJMellinShiftIntegrandFilled raw
      rw [dslope_of_ne _ hw]
    exact (analyticAt_congr hEq).mpr hRaw

theorem quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne
    (D : NumberField.OddFundamentalDiscriminant)
    {u : Real} (hu : 0 <= u) {z : Complex}
    (hzZero : Not (z = 0))
    (hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0))
    (hFactor : Not (quadraticDedekindZetaPoleFactor D
      (((u + 1 : Real) : Complex) - z) = 0)) :
    ContinuousAt (fun p : Prod Real Complex =>
      quadraticDedekindJMellinShiftIntegrandFilled D p.2 p.1) (u, z) := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 <= s0.re := by
    dsimp [s0]
    linarith
  have hTail0 : AnalyticAt Complex
      (quadraticDedekindPsiMellinTailContinuationFilled D) s0 :=
    quadraticDedekindPsiMellinTailContinuationFilled_analyticAt_of_one_le_re
      D hs0
  have hTail1 : AnalyticAt Complex
      (quadraticDedekindPsiMellinTailContinuationFilled D) s1 := by
    apply quadraticDedekindPsiMellinTailContinuationFilled_analyticAt D
    next => simpa [s1, s0] using hShiftZero
    next => simpa [s1, s0] using hFactor
  let S0 : Prod Real Complex -> Complex := fun p =>
    ((p.1 + 1 : Real) : Complex)
  let S1 : Prod Real Complex -> Complex := fun p => S0 p - p.2
  have hS0 : Continuous S0 := by
    dsimp [S0]
    fun_prop
  have hS1 : Continuous S1 := by
    dsimp [S1]
    exact hS0.sub continuous_snd
  have hTail0Comp : ContinuousAt (fun p : Prod Real Complex =>
      quadraticDedekindPsiMellinTailContinuationFilled D (S0 p)) (u, z) := by
    have hAt : ContinuousAt
        (quadraticDedekindPsiMellinTailContinuationFilled D) (S0 (u, z)) := by
      simpa [S0, s0] using hTail0.continuousAt
    exact hAt.comp' hS0.continuousAt
  have hTail1Comp : ContinuousAt (fun p : Prod Real Complex =>
      quadraticDedekindPsiMellinTailContinuationFilled D (S1 p)) (u, z) := by
    have hAt : ContinuousAt
        (quadraticDedekindPsiMellinTailContinuationFilled D) (S1 (u, z)) := by
      simpa [S1, S0, s1, s0] using hTail1.continuousAt
    exact hAt.comp' hS1.continuousAt
  have hPower : Continuous (fun p : Prod Real Complex =>
      (3 : Complex) ^ p.2) := by
    fun_prop
  let raw : Prod Real Complex -> Complex := fun p =>
    ((p.1 + 1 : Real) : Complex) * Inv.inv (p.2 - 0) *
      (quadraticDedekindJShiftNumeratorFilled D p.2 p.1 -
        quadraticDedekindJShiftNumeratorFilled D 0 p.1)
  have hNumerator : ContinuousAt (fun p : Prod Real Complex =>
      quadraticDedekindJShiftNumeratorFilled D p.2 p.1) (u, z) := by
    unfold quadraticDedekindJShiftNumeratorFilled
    change ContinuousAt (fun p : Prod Real Complex =>
      quadraticDedekindPsiMellinTailContinuationFilled D (S1 p) -
        (3 : Complex) ^ p.2 *
          quadraticDedekindPsiMellinTailContinuationFilled D (S0 p)) (u, z)
    exact hTail1Comp.sub (hPower.continuousAt.mul hTail0Comp)
  have hNumeratorZero : ContinuousAt (fun p : Prod Real Complex =>
      quadraticDedekindJShiftNumeratorFilled D 0 p.1) (u, z) := by
    have hEq : (fun p : Prod Real Complex =>
        quadraticDedekindJShiftNumeratorFilled D 0 p.1) = fun _ => 0 := by
      funext p
      exact quadraticDedekindJShiftNumeratorFilled_zero D p.1
    rw [hEq]
    exact continuousAt_const
  have hRaw : ContinuousAt raw (u, z) := by
    dsimp [raw]
    have hInv : ContinuousAt (fun p : Prod Real Complex =>
        Inv.inv (p.2 - 0)) (u, z) := by
      have hDen : ContinuousAt (fun p : Prod Real Complex => p.2 - 0)
          (u, z) := continuousAt_snd.sub continuousAt_const
      have hDiv : ContinuousAt (fun p : Prod Real Complex =>
          (1 : Complex) / (p.2 - 0)) (u, z) :=
        continuousAt_const.div hDen (by simpa using hzZero)
      simpa [one_div] using hDiv
    have hU : Continuous (fun p : Prod Real Complex =>
        ((p.1 + 1 : Real) : Complex)) := by
      fun_prop
    exact (hU.continuousAt.mul hInv).mul
      (hNumerator.sub hNumeratorZero)
  have hSecondNe : Filter.Eventually
      (fun p : Prod Real Complex => Not (p.2 = 0)) (nhds (u, z)) := by
    have hSecondContinuous : ContinuousAt
        (fun p : Prod Real Complex => p.2) (u, z) := continuousAt_snd
    exact hSecondContinuous.eventually_ne hzZero
  have hEq : Filter.EventuallyEq (nhds (u, z))
      (fun p : Prod Real Complex =>
        quadraticDedekindJMellinShiftIntegrandFilled D p.2 p.1) raw := by
    filter_upwards [hSecondNe] with p hp
    unfold quadraticDedekindJMellinShiftIntegrandFilled raw
    rw [dslope_of_ne _ hp]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub]
    ring
  exact hRaw.congr_of_eventuallyEq hEq

theorem quadraticDedekindJShiftNumeratorFilled_joint_continuousAt
    (D : NumberField.OddFundamentalDiscriminant)
    {u : Real} (hu : 0 <= u) {z : Complex}
    (hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0))
    (hFactor : Not (quadraticDedekindZetaPoleFactor D
      (((u + 1 : Real) : Complex) - z) = 0)) :
    ContinuousAt (fun p : Prod Real Complex =>
      quadraticDedekindJShiftNumeratorFilled D p.2 p.1) (u, z) := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 <= s0.re := by
    dsimp [s0]
    linarith
  have hTail0 : AnalyticAt Complex
      (quadraticDedekindPsiMellinTailContinuationFilled D) s0 :=
    quadraticDedekindPsiMellinTailContinuationFilled_analyticAt_of_one_le_re
      D hs0
  have hTail1 : AnalyticAt Complex
      (quadraticDedekindPsiMellinTailContinuationFilled D) s1 := by
    apply quadraticDedekindPsiMellinTailContinuationFilled_analyticAt D
    next => simpa [s1, s0] using hShiftZero
    next => simpa [s1, s0] using hFactor
  let S0 : Prod Real Complex -> Complex := fun p =>
    ((p.1 + 1 : Real) : Complex)
  let S1 : Prod Real Complex -> Complex := fun p => S0 p - p.2
  have hS0 : Continuous S0 := by
    dsimp [S0]
    fun_prop
  have hS1 : Continuous S1 := by
    dsimp [S1]
    exact hS0.sub continuous_snd
  have hTail0Comp : ContinuousAt (fun p : Prod Real Complex =>
      quadraticDedekindPsiMellinTailContinuationFilled D (S0 p)) (u, z) := by
    have hAt : ContinuousAt
        (quadraticDedekindPsiMellinTailContinuationFilled D) (S0 (u, z)) := by
      simpa [S0, s0] using hTail0.continuousAt
    exact hAt.comp' hS0.continuousAt
  have hTail1Comp : ContinuousAt (fun p : Prod Real Complex =>
      quadraticDedekindPsiMellinTailContinuationFilled D (S1 p)) (u, z) := by
    have hAt : ContinuousAt
        (quadraticDedekindPsiMellinTailContinuationFilled D) (S1 (u, z)) := by
      simpa [S1, S0, s1, s0] using hTail1.continuousAt
    exact hAt.comp' hS1.continuousAt
  have hPower : Continuous (fun p : Prod Real Complex =>
      (3 : Complex) ^ p.2) := by
    fun_prop
  unfold quadraticDedekindJShiftNumeratorFilled
  change ContinuousAt (fun p : Prod Real Complex =>
    quadraticDedekindPsiMellinTailContinuationFilled D (S1 p) -
      (3 : Complex) ^ p.2 *
        quadraticDedekindPsiMellinTailContinuationFilled D (S0 p)) (u, z)
  exact hTail1Comp.sub (hPower.continuousAt.mul hTail0Comp)

theorem exists_quadraticDedekindZeroCompactTubeRadius
    (D : NumberField.OddFundamentalDiscriminant) :
    Exists fun R : Real => And (0 < R)
      (forall z : Complex,
        Membership.mem (Metric.ball (0 : Complex) R) z ->
          forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
            And (Not ((((u + 1 : Real) : Complex) - z) = 0))
              (Not (quadraticDedekindZetaPoleFactor D
                (((u + 1 : Real) : Complex) - z) = 0))) := by
  have hShiftNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not ((((u + 1 : Real) : Complex) - z) = 0))
      (nhds (0 : Complex)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    have hAt : Not ((((u + 1 : Real) : Complex) - 0) = 0) := by
      intro hEq
      have hRe := congrArg Complex.re hEq
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hRe
      linarith [hu.1]
    let G : Prod Complex Real -> Complex := fun p =>
      ((p.2 + 1 : Real) : Complex) - p.1
    have hContinuous : Continuous G := by
      dsimp [G]
      fun_prop
    have hPair : Not (G (0, u) = 0) := by
      simpa [G] using hAt
    exact hContinuous.continuousAt.eventually_ne hPair
  have hFactorNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not (quadraticDedekindZetaPoleFactor D
          (((u + 1 : Real) : Complex) - z) = 0))
      (nhds (0 : Complex)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    have hs : 1 <= (((u + 1 : Real) : Complex) - 0).re := by
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re]
      linarith [hu.1]
    have hAt : Not (quadraticDedekindZetaPoleFactor D
        (((u + 1 : Real) : Complex) - 0) = 0) :=
      quadraticDedekindZetaPoleFactor_ne_zero_of_one_le_re D hs
    let G : Prod Complex Real -> Complex := fun p =>
      quadraticDedekindZetaPoleFactor D
        (((p.2 + 1 : Real) : Complex) - p.1)
    have hContinuous : Continuous G := by
      dsimp [G]
      exact (quadraticDedekindZetaPoleFactor_differentiable D).continuous.comp
        (by fun_prop)
    have hPair : Not (G (0, u) = 0) := by
      simpa [G] using hAt
    exact hContinuous.continuousAt.eventually_ne hPair
  have hAll := hShiftNhd.and hFactorNhd
  choose R hRPos hR using Metric.mem_nhds_iff.1 hAll
  refine Exists.intro R (And.intro hRPos ?_)
  intro z hz u hu
  have hzGood := hR hz
  exact And.intro (hzGood.1 u hu) (hzGood.2 u hu)

def quadraticDedekindJShiftedComplexContinuationFilledCompact
    (D : NumberField.OddFundamentalDiscriminant)
    (z : Complex) : Complex :=
  integral (volume.restrict (Ioc (0 : Real) 1))
    (quadraticDedekindJMellinShiftIntegrandFilled D z)

def quadraticDedekindJShiftedComplexContinuationFilledLarge
    (D : NumberField.OddFundamentalDiscriminant)
    (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (1 : Real)))
    (quadraticDedekindJMellinShiftIntegrandFilled D z)

theorem quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_of_tube
    (D : NumberField.OddFundamentalDiscriminant)
    {center : Complex} {R : Real} (hRPos : 0 < R)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (Not (z = 0))
          (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
            And (Not ((((u + 1 : Real) : Complex) - z) = 0))
              (Not (quadraticDedekindZetaPoleFactor D
                (((u + 1 : Real) : Complex) - z) = 0)))) :
    AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledCompact D)
      center := by
  let K : Set (Prod Real Complex) := fun p =>
    And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem (Metric.closedBall center (R / 2)) p.2)
  let F : Prod Real Complex -> Complex := fun p =>
    quadraticDedekindJMellinShiftIntegrandFilled D p.2 p.1
  have hKCompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_Icc : IsCompact (Icc (0 : Real) 1)).prod
      (isCompact_closedBall center (R / 2))
  have hKNonempty : K.Nonempty := by
    refine Exists.intro ((0 : Real), center) ?_
    dsimp [K]
    exact And.intro (And.intro le_rfl zero_le_one)
      (Metric.mem_closedBall_self (by linarith))
  have hContinuous : ContinuousOn F K := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    change And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem (Metric.closedBall center (R / 2)) p.2) at hp
    have hpBall : Membership.mem (Metric.ball center R) p.2 := by
      rw [Metric.mem_closedBall] at hp
      rw [Metric.mem_ball]
      linarith
    have hpGood := hGood p.2 hpBall
    exact quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne D
      hp.1.1 hpGood.1 (hpGood.2 p.1 hp.1).1 (hpGood.2 p.1 hp.1).2
  choose p hpK hpMax using hKCompact.exists_isMaxOn hKNonempty hContinuous.norm
  let M : Real := norm (F p)
  have hMNonneg : 0 <= M := norm_nonneg _
  have hKernelBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.closedBall center (R / 2)) z ->
            norm (quadraticDedekindJMellinShiftIntegrandFilled D z u) <= M := by
    intro u hu z hz
    have hPair : K (u, z) := by
      dsimp [K]
      exact And.intro hu hz
    simpa [M, F] using hpMax hPair
  have hContinuousU : forall z : Complex,
      Membership.mem (Metric.closedBall center (R / 2)) z ->
        ContinuousOn (fun u : Real =>
          quadraticDedekindJMellinShiftIntegrandFilled D z u) (Icc (0 : Real) 1) := by
    intro z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGood := hGood z hzBall
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
  have hAnalytic : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.closedBall center (R / 2)) z ->
            AnalyticAt Complex (fun w : Complex =>
              quadraticDedekindJMellinShiftIntegrandFilled D w u) z := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGood := hGood z hzBall
    exact
      quadraticDedekindJMellinShiftIntegrandFilled_analyticAt D
        hu.1 (hzGood.2 u hu).1 (hzGood.2 u hu).2
  have hDerivativeMeasurable : forall z : Complex,
      Membership.mem (Metric.ball center (R / 4)) z ->
        AEStronglyMeasurable (fun u : Real =>
          deriv (fun w : Complex =>
            quadraticDedekindJMellinShiftIntegrandFilled D w u) z)
          (volume.restrict (Ioc (0 : Real) 1)) := by
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
        (volume.restrict (Ioc (0 : Real) 1)) := by
      intro n
      have hShift := (hContinuousU _ (hShiftClosed n)).mono
        Ioc_subset_Icc_self
      have hBase := (hContinuousU z hzClosed).mono Ioc_subset_Icc_self
      have hShiftMeas : AEStronglyMeasurable
          (fun u : Real => quadraticDedekindJMellinShiftIntegrandFilled D
            (z + Robin1984.nicolasCompactStripDerivativeStep R n) u)
          (volume.restrict (Ioc (0 : Real) 1)) :=
        hShift.aestronglyMeasurable measurableSet_Ioc
      have hBaseMeas : AEStronglyMeasurable
          (fun u : Real => quadraticDedekindJMellinShiftIntegrandFilled D z u)
          (volume.restrict (Ioc (0 : Real) 1)) :=
        hBase.aestronglyMeasurable measurableSet_Ioc
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
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have huIcc : Membership.mem (Icc (0 : Real) 1) u :=
        Ioc_subset_Icc_self hu
      have hSlope := (hAnalytic u huIcc z hzClosed).differentiableAt.hasDerivAt
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
  have hDerivativeBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.ball center (R / 4)) z ->
            norm (deriv (fun w : Complex =>
              quadraticDedekindJMellinShiftIntegrandFilled D w u) z) <= 8 * M / R := by
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
        (Metric.closedBall (f z) (2 * M)) := by
      intro w hw
      have hwBound : norm (f w) <= M := hKernelBound u hu w (hSmallSubset hw)
      have hzBound : norm (f z) <= M := hKernelBound u hu z hzClosed
      rw [Metric.mem_closedBall]
      calc
        dist (f w) (f z) <= norm (f w) + norm (f z) := by
          simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
        _ <= M + M := add_le_add hwBound hzBound
        _ = 2 * M := by ring
    have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
      hDiff hMaps (by dsimp [r]; linarith)
    change norm (deriv f z) <= 8 * M / R
    calc
      norm (deriv f z) <= (2 * M) / r := hCauchy
      _ = 8 * M / R := by
        dsimp [r]
        field_simp [hRPos.ne']
        ring
  let s : Set Complex := Metric.ball center (R / 4)
  have hHasDeriv : forall z : Complex, Membership.mem s z ->
      HasDerivAt (quadraticDedekindJShiftedComplexContinuationFilledCompact D)
        (integral (volume.restrict (Ioc (0 : Real) 1)) (fun u : Real =>
          deriv (fun w : Complex =>
            quadraticDedekindJMellinShiftIntegrandFilled D w u) z)) z := by
    intro z hz
    let G : Complex -> Real -> Complex := fun w => fun u =>
      quadraticDedekindJMellinShiftIntegrandFilled D w u
    let G' : Complex -> Real -> Complex := fun w => fun u =>
      deriv (fun v : Complex => quadraticDedekindJMellinShiftIntegrandFilled D v u) w
    have hsNhd : Membership.mem (nhds z) s :=
      Metric.isOpen_ball.mem_nhds hz
    have hGMeas : Filter.Eventually
        (fun w : Complex => AEStronglyMeasurable (G w)
          (volume.restrict (Ioc (0 : Real) 1))) (nhds z) := by
      filter_upwards [hsNhd] with w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [G]
      exact ((hContinuousU w hwClosed).mono Ioc_subset_Icc_self)
        |>.aestronglyMeasurable measurableSet_Ioc
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      have hzDist : dist z center < R / 4 := by
        simpa [s, Metric.mem_ball] using hz
      linarith
    have hGInt : Integrable (G z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      have hInt : IntegrableOn (fun u : Real =>
          quadraticDedekindJMellinShiftIntegrandFilled D z u) (Icc (0 : Real) 1) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact hContinuousU z hzClosed
      exact hInt.mono_set Ioc_subset_Icc_self
    have hG'Meas : AEStronglyMeasurable (G' z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      dsimp [G']
      exact hDerivativeMeasurable z hz
    have hBound : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          norm (G' w u) <= 8 * M / R)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      exact hDerivativeBound u (Ioc_subset_Icc_self hu) w hw
    have hBoundInt : IntegrableOn (fun _ : Real => 8 * M / R)
        (Ioc (0 : Real) 1) := by
      have hInt : IntegrableOn (fun _ : Real => 8 * M / R)
          (Icc (0 : Real) 1) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact continuousOn_const
      exact hInt.mono_set Ioc_subset_Icc_self
    have hDiff : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          HasDerivAt (fun v : Complex => G v u) (G' w u) w)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [G, G']
      exact (hAnalytic u (Ioc_subset_Icc_self hu) w hwClosed)
        |>.differentiableAt.hasDerivAt
    have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := G) (F' := G') (bound := fun _ : Real => 8 * M / R)
      hsNhd hGMeas hGInt hG'Meas hBound hBoundInt hDiff
    unfold quadraticDedekindJShiftedComplexContinuationFilledCompact
    simpa [G, G'] using hMain.2
  have hDiffOn : DifferentiableOn Complex
      (quadraticDedekindJShiftedComplexContinuationFilledCompact D) s := by
    intro z hz
    exact (hHasDeriv z hz).differentiableAt.differentiableWithinAt
  apply hDiffOn.analyticAt
  dsimp [s]
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith : 0 < R / 4))

theorem quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_of_zeroTube_punctured
    (D : NumberField.OddFundamentalDiscriminant)
    {R : Real} (hRPos : 0 < R)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball (0 : Complex) R) z ->
        forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
          And (Not ((((u + 1 : Real) : Complex) - z) = 0))
            (Not (quadraticDedekindZetaPoleFactor D
              (((u + 1 : Real) : Complex) - z) = 0)))
    {z : Complex} (hzBall : Membership.mem (Metric.ball (0 : Complex) R) z)
    (hzZero : Not (z = 0)) :
    AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledCompact D) z := by
  have hOpenBall : Membership.mem (nhds z) (Metric.ball (0 : Complex) R) :=
    Metric.isOpen_ball.mem_nhds hzBall
  have hOpenZero : Membership.mem (nhds z) (Set.compl {(0 : Complex)}) :=
    isOpen_compl_singleton.mem_nhds hzZero
  have hBoth : Membership.mem (nhds z)
      (Set.inter (Metric.ball (0 : Complex) R)
        (Set.compl {(0 : Complex)})) :=
    inter_mem hOpenBall hOpenZero
  choose r hrPos hr using Metric.mem_nhds_iff.1 hBoth
  apply quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_of_tube
    D hrPos
  intro w hw
  have hwBoth := hr hw
  have hwZero : Not (w = 0) :=
    Set.mem_compl_singleton_iff.mp hwBoth.2
  exact And.intro hwZero (hGood w hwBoth.1)

theorem exists_quadraticDedekindRightmostRayCompactTubeRadius
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Exists fun R : Real => And (0 < R)
      (forall z : Complex,
        Membership.mem
          (Metric.ball ((1 - rho) - (eps : Complex)) R) z ->
          And (Not (z = 0))
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              And (Not ((((u + 1 : Real) : Complex) - z) = 0))
                (Not (quadraticDedekindZetaPoleFactor D
                  (((u + 1 : Real) : Complex) - z) = 0)))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  have hCenterIm : center.im = -rho.im := by
    dsimp [center]
    simp
  have hCenterNe : Not (center = 0) := by
    intro hEq
    have hZeroIm : center.im = 0 := by rw [hEq]; simp
    exact hIm (neg_eq_zero.mp (hCenterIm.symm.trans hZeroIm))
  have hZeroNhd : Filter.Eventually (fun z : Complex => Not (z = 0))
      (nhds center) := continuousAt_id.eventually_ne hCenterNe
  have hShiftNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not ((((u + 1 : Real) : Complex) - z) = 0))
      (nhds center) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    have hShiftIm :
        ((((u + 1 : Real) : Complex) - center)).im = rho.im := by
      rw [Complex.sub_im, Complex.ofReal_im, hCenterIm]
      ring
    have hShiftNe : Not ((((u + 1 : Real) : Complex) - center) = 0) := by
      intro hEq
      have hZeroIm : ((((u + 1 : Real) : Complex) - center)).im = 0 := by
        rw [hEq]
        simp
      exact hIm (hShiftIm.symm.trans hZeroIm)
    let G : Prod Complex Real -> Complex := fun p =>
      ((p.2 + 1 : Real) : Complex) - p.1
    have hContinuous : Continuous G := by
      dsimp [G]
      fun_prop
    have hAt : Not (G (center, u) = 0) := by
      simpa [G] using hShiftNe
    exact hContinuous.continuousAt.eventually_ne hAt
  have hFactorNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not (quadraticDedekindZetaPoleFactor D
          (((u + 1 : Real) : Complex) - z) = 0))
      (nhds center) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    let s : Complex := rho + ((eps + u : Real) : Complex)
    have hShift : (((u + 1 : Real) : Complex) - center) = s := by
      dsimp [center, s]
      push_cast
      ring
    have hZeta : Not (quadraticDedekindZetaContinuation D s = 0) := by
      dsimp [s]
      exact hRay (eps + u) (by linarith [hu.1])
    have hFactor : Not (quadraticDedekindZetaPoleFactor D s = 0) := by
      by_cases hsOne : s = 1
      next =>
        rw [hsOne]
        exact quadraticDedekindZetaPoleFactor_one_ne_zero D
      next =>
        intro hFactorZero
        have hIdentity : quadraticDedekindZetaContinuation D s = 0 := by
          rw [quadraticDedekindZetaContinuation_eq_poleFactor_div D hsOne,
            hFactorZero, zero_div]
        exact hZeta hIdentity
    let G : Prod Complex Real -> Complex := fun p =>
      quadraticDedekindZetaPoleFactor D (((p.2 + 1 : Real) : Complex) - p.1)
    have hAffine : Continuous (fun p : Prod Complex Real =>
        (((p.2 + 1 : Real) : Complex) - p.1)) := by
      fun_prop
    have hContinuous : Continuous G := by
      dsimp [G]
      exact (quadraticDedekindZetaPoleFactor_differentiable D).continuous.comp hAffine
    have hAt : Not (quadraticDedekindZetaPoleFactor D
        (((u + 1 : Real) : Complex) - center) = 0) := by
      rw [hShift]
      exact hFactor
    have hPairAt : Not (G (center, u) = 0) := by
      simpa [G] using hAt
    exact hContinuous.continuousAt.eventually_ne hPairAt
  have hAll := hZeroNhd.and (hShiftNhd.and hFactorNhd)
  choose R hRPos hR using Metric.mem_nhds_iff.1 hAll
  refine Exists.intro R (And.intro hRPos ?_)
  intro z hz
  have hzGood := hR hz
  exact And.intro hzGood.1 (fun u hu =>
    And.intro (hzGood.2.1 u hu) (hzGood.2.2 u hu))

theorem quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_rightmostRay
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex (quadraticDedekindJShiftedComplexContinuationFilledCompact D)
      ((1 - rho) - (eps : Complex)) := by
  choose R hRPos hGood using
    exists_quadraticDedekindRightmostRayCompactTubeRadius D hIm hRay hEps
  exact quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_of_tube
    D hRPos hGood


end

end RobinBV.NumberField
