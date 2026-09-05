import RobinBV.NumberField.Proof.QuadraticDedekindNicolasAnalytic

/-!
# Zero and positive quadratic Dedekind continuation

Focused infrastructure for the quadratic Dedekind Nicolas-Landau Omega theorem.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section
theorem quadraticDedekindJShiftedComplexContinuationFilledLarge_hasDerivAt_zeroBall
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    HasDerivAt (quadraticDedekindJShiftedComplexContinuationFilledLarge D)
      (integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        deriv (fun w : Complex =>
          quadraticDedekindJMellinShiftIntegrandFilled D w u) z)) z := by
  let s : Set Complex := Metric.ball (0 : Complex) (1 / 8 : Real)
  let F : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    quadraticDedekindJMellinShiftIntegrandFilled D w u
  let F' : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    deriv (fun v : Complex => quadraticDedekindJMellinShiftIntegrandFilled D v u) w
  have hsNhd : Membership.mem (nhds z) s := by
    dsimp [s]
    exact Metric.isOpen_ball.mem_nhds hz
  have hFMeas : Filter.Eventually
      (fun w : Complex => AEStronglyMeasurable (F w)
        (volume.restrict (Ioi (1 : Real)))) (nhds z) := by
    filter_upwards [hsNhd] with w hw
    have hwQuarter : Membership.mem
        (Metric.ball (0 : Complex) (1 / 4 : Real)) w := by
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable D
      hwQuarter
  have hFInt : Integrable (F z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact quadraticDedekindJMellinShiftIntegrandFilled_integrableOn_large D hz
  have hF'Meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact deriv_quadraticDedekindJMellinShiftIntegrandFilled_aestronglyMeasurable D hz
  have hBound : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        norm (F' w u) <= quadraticDedekindJLargeDerivativeMajorant u)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    dsimp [F', s]
    unfold quadraticDedekindJLargeDerivativeMajorant
    exact norm_deriv_quadraticDedekindJMellinShiftIntegrandFilled_le D
      (mem_Ioi.mp hu) hw
  have hDiff : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        HasDerivAt (fun v : Complex => F v u) (F' w u) w)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hwQuarter : Membership.mem
        (Metric.ball (0 : Complex) (1 / 4 : Real)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hAt : DifferentiableAt Complex
        (fun v : Complex => quadraticDedekindJMellinShiftIntegrandFilled D v u) w :=
      (quadraticDedekindJMellinShiftIntegrandFilled_differentiableOn_quarter D
        (mem_Ioi.mp hu) w hwQuarter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hwQuarter)
    dsimp [F, F']
    exact hAt.hasDerivAt
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := quadraticDedekindJLargeDerivativeMajorant)
    hsNhd hFMeas hFInt hF'Meas hBound
    quadraticDedekindJLargeDerivativeMajorant_integrableOn hDiff
  unfold quadraticDedekindJShiftedComplexContinuationFilledLarge
  simpa [F, F'] using hMain.2

theorem quadraticDedekindJShiftedComplexContinuationFilledLarge_differentiableOn_zeroBall
    (D : NumberField.OddFundamentalDiscriminant) :
    DifferentiableOn Complex (quadraticDedekindJShiftedComplexContinuationFilledLarge D)
      (Metric.ball (0 : Complex) (1 / 8 : Real)) := by
  intro z hz
  exact (quadraticDedekindJShiftedComplexContinuationFilledLarge_hasDerivAt_zeroBall D
    hz).differentiableAt.differentiableWithinAt

theorem quadraticDedekindJShiftedComplexContinuationFilledCompact_continuousAt_zero
    (D : NumberField.OddFundamentalDiscriminant) :
    ContinuousAt
      (quadraticDedekindJShiftedComplexContinuationFilledCompact D) 0 := by
  choose R hRPos hGood using exists_quadraticDedekindZeroCompactTubeRadius D
  let r : Real := R / 2
  have hrPos : 0 < r := by
    dsimp [r]
    linarith
  let K : Set (Prod Real Complex) := fun p =>
    And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem (Metric.closedBall (0 : Complex) r) p.2)
  let N : Prod Real Complex -> Complex := fun p =>
    quadraticDedekindJShiftNumeratorFilled D p.2 p.1
  have hKCompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_Icc : IsCompact (Icc (0 : Real) 1)).prod
      (isCompact_closedBall (0 : Complex) r)
  have hKNonempty : K.Nonempty := by
    refine Exists.intro ((0 : Real), (0 : Complex)) ?_
    dsimp [K]
    exact And.intro (And.intro le_rfl zero_le_one)
      (Metric.mem_closedBall_self hrPos.le)
  have hNContinuous : ContinuousOn N K := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    change And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem (Metric.closedBall (0 : Complex) r) p.2) at hp
    have hpBall : Membership.mem (Metric.ball (0 : Complex) R) p.2 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hp
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [r] at hp
      linarith
    have hpGood := hGood p.2 hpBall p.1 hp.1
    exact quadraticDedekindJShiftNumeratorFilled_joint_continuousAt
      D hp.1.1 hpGood.1 hpGood.2
  choose p hpK hpMax using hKCompact.exists_isMaxOn hKNonempty hNContinuous.norm
  let M : Real := norm (N p)
  have hMNonneg : 0 <= M := norm_nonneg _
  have hNBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.closedBall (0 : Complex) r) z ->
            norm (quadraticDedekindJShiftNumeratorFilled D z u) <= M := by
    intro u hu z hz
    have hPair : K (u, z) := by
      dsimp [K]
      exact And.intro hu hz
    simpa [M, N] using hpMax hPair
  have hNumeratorDiff : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        DifferentiableOn Complex
          (fun z : Complex => quadraticDedekindJShiftNumeratorFilled D z u)
          (Metric.ball (0 : Complex) r) := by
    intro u hu z hz
    have hzBig : Membership.mem (Metric.ball (0 : Complex) R) z := by
      rw [Metric.mem_ball, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [r] at hz
      linarith
    have hzGood := hGood z hzBig u hu
    exact (quadraticDedekindJShiftNumeratorFilled_analyticAt
      D hu.1 hzGood.1 hzGood.2).differentiableAt.differentiableWithinAt
  have hKernelBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.ball (0 : Complex) r) z ->
            norm (quadraticDedekindJMellinShiftIntegrandFilled D z u) <=
              2 * (M / r) := by
    intro u hu z hz
    have hMaps : MapsTo
        (fun w : Complex => quadraticDedekindJShiftNumeratorFilled D w u)
        (Metric.ball (0 : Complex) r)
        (Metric.closedBall
          (quadraticDedekindJShiftNumeratorFilled D 0 u) M) := by
      intro w hw
      rw [quadraticDedekindJShiftNumeratorFilled_zero]
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hNBound u hu w (Metric.ball_subset_closedBall hw)
    have hDslope := Complex.norm_dslope_le_div_of_mapsTo_ball
      (hNumeratorDiff u hu) hMaps hz
    have huPos : 0 < u + 1 := by linarith [hu.1]
    unfold quadraticDedekindJMellinShiftIntegrandFilled
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huPos]
    calc
      (u + 1) * norm
          (dslope (fun w : Complex =>
            quadraticDedekindJShiftNumeratorFilled D w u) 0 z) <=
          (u + 1) * (M / r) :=
        mul_le_mul_of_nonneg_left hDslope huPos.le
      _ <= 2 * (M / r) := by
        apply mul_le_mul_of_nonneg_right _
        next => exact div_nonneg hMNonneg hrPos.le
        next => linarith [hu.2]
  have hContinuousUOfNe : forall z : Complex,
      Membership.mem (Metric.ball (0 : Complex) r) z ->
      Not (z = 0) ->
        ContinuousOn (fun u : Real =>
          quadraticDedekindJMellinShiftIntegrandFilled D z u)
          (Icc (0 : Real) 1) := by
    intro z hz hzZero u hu
    have hzBig : Membership.mem (Metric.ball (0 : Complex) R) z := by
      rw [Metric.mem_ball, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [r] at hz
      linarith
    have hzGood := hGood z hzBig u hu
    have hJoint :=
      quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne
        D hu.1 hzZero hzGood.1 hzGood.2
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        quadraticDedekindJMellinShiftIntegrandFilled D z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hMeasurableZero : AEStronglyMeasurable (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D 0 u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    let zseq : Nat -> Complex := fun n : Nat =>
      (((r / 2) * ((1 : Real) / ((n : Real) + 1)) : Real) : Complex)
    have hRecip : Tendsto
        (fun n : Nat => (1 : Real) / ((n : Real) + 1))
        atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hReal : Tendsto
        (fun n : Nat => (r / 2) * ((1 : Real) / ((n : Real) + 1)))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hRecip
    have hZ : Tendsto zseq atTop (nhds (0 : Complex)) := by
      have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
      change Tendsto (fun n : Nat =>
        (((r / 2) * ((1 : Real) / ((n : Real) + 1)) : Real) : Complex))
        atTop (nhds (0 : Complex)) at hCast
      exact hCast
    have hZPos : forall n : Nat,
        0 < (r / 2) * ((1 : Real) / ((n : Real) + 1)) := by
      intro n
      positivity
    have hZNe : forall n : Nat, Not (zseq n = 0) := by
      intro n
      dsimp [zseq]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (hZPos n))
    have hZMem : forall n : Nat,
        Membership.mem (Metric.ball (0 : Complex) r) (zseq n) := by
      intro n
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [zseq]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hZPos n)]
      have hn0 : 0 <= (n : Real) := Nat.cast_nonneg n
      have hn : (1 : Real) <= (n : Real) + 1 := by linarith
      have hRecipLe : (1 : Real) / ((n : Real) + 1) <= 1 := by
        simpa using one_div_le_one_div_of_le zero_lt_one hn
      have hrHalf : r / 2 < r := by linarith
      exact (mul_le_mul_of_nonneg_left hRecipLe (by positivity)).trans_lt
        (by simpa using hrHalf)
    have hMeas : forall n : Nat, AEMeasurable (fun u : Real =>
        quadraticDedekindJMellinShiftIntegrandFilled D (zseq n) u)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      intro n
      exact ((hContinuousUOfNe (zseq n) (hZMem n) (hZNe n)).mono
        Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc |>.aemeasurable
    have hTendsto : Filter.Eventually (fun u : Real => Tendsto
        (fun n : Nat =>
          quadraticDedekindJMellinShiftIntegrandFilled D (zseq n) u)
        atTop (nhds
          (quadraticDedekindJMellinShiftIntegrandFilled D 0 u)))
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact (quadraticDedekindJMellinShiftIntegrandFilled_analyticAt_zero
        D hu.1.le).continuousAt.tendsto.comp hZ
    exact (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable
  have hMeasurable : forall z : Complex,
      Membership.mem (Metric.ball (0 : Complex) r) z ->
        AEStronglyMeasurable (fun u : Real =>
          quadraticDedekindJMellinShiftIntegrandFilled D z u)
          (volume.restrict (Ioc (0 : Real) 1)) := by
    intro z hz
    by_cases hzZero : z = 0
    next =>
      subst z
      exact hMeasurableZero
    next =>
      exact ((hContinuousUOfNe z hz hzZero).mono Ioc_subset_Icc_self)
        |>.aestronglyMeasurable measurableSet_Ioc
  have hBoundIntegrable : Integrable (fun _ : Real => 2 * (M / r))
      (volume.restrict (Ioc (0 : Real) 1)) := by
    have hInt : IntegrableOn (fun _ : Real => 2 * (M / r))
        (Icc (0 : Real) 1) := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      exact continuousOn_const
    exact hInt.mono_set Ioc_subset_Icc_self
  have hBall : Membership.mem (nhds (0 : Complex))
      (Metric.ball (0 : Complex) r) :=
    Metric.ball_mem_nhds _ hrPos
  unfold ContinuousAt
  unfold quadraticDedekindJShiftedComplexContinuationFilledCompact
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ : Real => 2 * (M / r))
  next =>
    filter_upwards [hBall] with z hz
    exact hMeasurable z hz
  next =>
    filter_upwards [hBall] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact hKernelBound u (Ioc_subset_Icc_self hu) z hz
  next => exact hBoundIntegrable
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (quadraticDedekindJMellinShiftIntegrandFilled_analyticAt_zero
      D hu.1.le).continuousAt.tendsto

theorem quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_zero
    (D : NumberField.OddFundamentalDiscriminant) :
    AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledCompact D) 0 := by
  choose R hRPos hGood using exists_quadraticDedekindZeroCompactTubeRadius D
  have hBall : Membership.mem (nhds (0 : Complex))
      (Metric.ball (0 : Complex) R) :=
    Metric.ball_mem_nhds _ hRPos
  have hPunctured : Filter.Eventually
      (fun z : Complex => DifferentiableAt Complex
        (quadraticDedekindJShiftedComplexContinuationFilledCompact D) z)
      (nhdsWithin 0 (Set.compl {(0 : Complex)})) := by
    filter_upwards [nhdsWithin_le_nhds hBall,
      self_mem_nhdsWithin] with z hzBall hzZeroMem
    have hzZero : Not (z = 0) :=
      Set.mem_compl_singleton_iff.mp hzZeroMem
    exact
      (quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_of_zeroTube_punctured
        D hRPos hGood hzBall hzZero).differentiableAt
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hPunctured
    (quadraticDedekindJShiftedComplexContinuationFilledCompact_continuousAt_zero D)

theorem quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_zero
    (D : NumberField.OddFundamentalDiscriminant) :
    AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledLarge D) 0 := by
  apply
    (quadraticDedekindJShiftedComplexContinuationFilledLarge_differentiableOn_zeroBall
      D).analyticAt
  exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num))

def quadraticDedekindJShiftedComplexContinuationFilledSplit
    (D : NumberField.OddFundamentalDiscriminant)
    (z : Complex) : Complex :=
  quadraticDedekindJShiftedComplexContinuationFilledCompact D z +
    quadraticDedekindJShiftedComplexContinuationFilledLarge D z

theorem quadraticDedekindJShiftedComplexContinuationFilledSplit_analyticAt_zero
    (D : NumberField.OddFundamentalDiscriminant) :
    AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledSplit D) 0 := by
  unfold quadraticDedekindJShiftedComplexContinuationFilledSplit
  exact
    (quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_zero D).add
      (quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_zero D)

theorem quadraticDedekindJShiftedComplexContinuationFilledSplit_eq_full_of_re_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} (hz : z.re < 0) :
    quadraticDedekindJShiftedComplexContinuationFilledSplit D z =
      quadraticDedekindJShiftedComplexContinuationFilled D z := by
  have hzZero : Not (z = 0) := by
    intro hEq
    subst z
    norm_num at hz
  have hCompactContinuous : ContinuousOn (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D z u)
      (Icc (0 : Real) 1) := by
    intro u hu
    have hsRe : 1 < ((((u + 1 : Real) : Complex) - z).re) := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [hu.1]
    have hsZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hFactor : Not (quadraticDedekindZetaPoleFactor D
        (((u + 1 : Real) : Complex) - z) = 0) :=
      quadraticDedekindZetaPoleFactor_ne_zero_of_one_le_re D hsRe.le
    have hJoint :=
      quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne
        D hu.1 hzZero hsZero hFactor
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        quadraticDedekindJMellinShiftIntegrandFilled D z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hCompact : IntegrableOn (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D z u)
      (Ioc (0 : Real) 1) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc hCompactContinuous).mono_set
      Ioc_subset_Icc_self
  have hzNorm : 0 < norm z := norm_pos_iff.mpr hzZero
  have hLarge : IntegrableOn (fun u : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D z u)
      (Ioi (1 : Real)) :=
    quadraticDedekindJMellinShiftIntegrandFilled_integrableOn_large_of_geometry
      D hzNorm (by linarith) le_rfl
  unfold quadraticDedekindJShiftedComplexContinuationFilledSplit
    quadraticDedekindJShiftedComplexContinuationFilledCompact
    quadraticDedekindJShiftedComplexContinuationFilledLarge
    quadraticDedekindJShiftedComplexContinuationFilled
  rw [<- Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) <= 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  next => exact hCompact
  next => exact hLarge

theorem quadraticDedekindJShiftedComplexContinuationFilledSplit_eq_mellin_of_re_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} (hz : z.re < 0) :
    quadraticDedekindJShiftedComplexContinuationFilledSplit D z =
      quadraticDedekindJMellin D z := by
  rw [quadraticDedekindJShiftedComplexContinuationFilledSplit_eq_full_of_re_neg
    D hz]
  exact quadraticDedekindJShiftedComplexContinuationFilled_eq_mellin_of_re_neg
    D hz

def quadraticDedekindLandauPositiveComplexContinuationFilledSplit
    (D : NumberField.OddFundamentalDiscriminant)
    (X b : Real) (z : Complex) : Complex :=
  quadraticDedekindJShiftedComplexContinuationFilledSplit D z -
    quadraticDedekindJComplexMellinStartup D X z +
      Robin1984.nicolasLandauRpowComplexContinuation X b z

theorem quadraticDedekindLandauComplexMGF_eq_continuationFilledSplit_of_re_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    {z : Complex} (hz : z.re < 0) :
    complexMGF (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b) z =
      quadraticDedekindLandauPositiveComplexContinuationFilledSplit D X b z := by
  rw [quadraticDedekindLandauComplexMGF_eq_continuationFilled_of_re_neg
    D hX hb hPos hz]
  unfold quadraticDedekindLandauPositiveComplexContinuationFilled
    quadraticDedekindLandauPositiveComplexContinuationFilledSplit
  rw [quadraticDedekindJShiftedComplexContinuationFilledSplit_eq_full_of_re_neg
    D hz]

def QuadraticDedekindNoRealOffCriticalZero
    (D : NumberField.OddFundamentalDiscriminant) : Prop :=
  forall r : Real, (1 / 2 : Real) < r -> r < 1 ->
    Not (quadraticDedekindZetaContinuation D (r : Complex) = 0)

theorem exists_quadraticDedekindPositiveCompactTubeRadius
    (D : NumberField.OddFundamentalDiscriminant)
    (hNoReal : QuadraticDedekindNoRealOffCriticalZero D)
    {sigma : Real} (hSigmaPos : 0 < sigma)
    (hSigmaHalf : sigma < 1 / 2) :
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
    have hAt : Not ((((u + 1 : Real) : Complex) - (sigma : Complex)) = 0) := by
      intro hEq
      have hRe := congrArg Complex.re hEq
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hRe
      linarith [hu.1]
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
    have htHalf : (1 / 2 : Real) < t := by
      dsimp [t]
      linarith [hu.1]
    have hFactor : Not (quadraticDedekindZetaPoleFactor D (t : Complex) = 0) := by
      by_cases htOneLe : 1 <= t
      next =>
        exact quadraticDedekindZetaPoleFactor_ne_zero_of_one_le_re D
          (by simpa using htOneLe)
      next =>
        have htOne : t < 1 := lt_of_not_ge htOneLe
        have hZeta := hNoReal t htHalf htOne
        have htNe : Not ((t : Complex) = 1) := by
          intro hEq
          have hRe := congrArg Complex.re hEq
          simp only [Complex.ofReal_re, Complex.one_re] at hRe
          linarith
        intro hFactorZero
        have hIdentity : quadraticDedekindZetaContinuation D (t : Complex) = 0 := by
          rw [quadraticDedekindZetaContinuation_eq_poleFactor_div D htNe,
            hFactorZero, zero_div]
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

theorem quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_pos_real
    (D : NumberField.OddFundamentalDiscriminant)
    (hNoReal : QuadraticDedekindNoRealOffCriticalZero D)
    {sigma : Real} (hSigmaPos : 0 < sigma)
    (hSigmaHalf : sigma < 1 / 2) :
    AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledCompact D)
      (sigma : Complex) := by
  choose R hRPos hGood using
    exists_quadraticDedekindPositiveCompactTubeRadius
      D hNoReal hSigmaPos hSigmaHalf
  exact quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_of_tube
    D hRPos hGood

theorem exists_quadraticDedekindPositiveLargeGeometry
    {sigma : Real} (hSigmaPos : 0 < sigma)
    (hSigmaHalf : sigma < 1 / 2) :
    Exists fun d : Real => Exists fun R : Real =>
      And (0 < d) (And (0 < R)
        (forall z : Complex,
          Membership.mem (Metric.ball (sigma : Complex) R) z ->
            And (z.re <= (3 / 4 : Real)) (d <= norm z))) := by
  let center : Complex := (sigma : Complex)
  have hCenterNe : Not (center = 0) := by
    dsimp [center]
    exact Complex.ofReal_ne_zero.mpr hSigmaPos.ne'
  have hCenterNorm : 0 < norm center := norm_pos_iff.mpr hCenterNe
  have hCenterRe : center.re = sigma := by simp [center]
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

theorem quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_pos_real
    (D : NumberField.OddFundamentalDiscriminant)
    {sigma : Real} (hSigmaPos : 0 < sigma)
    (hSigmaHalf : sigma < 1 / 2) :
    AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledLarge D)
      (sigma : Complex) := by
  choose d R hd hRPos hGeometry using
    exists_quadraticDedekindPositiveLargeGeometry hSigmaPos hSigmaHalf
  exact quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    D hRPos hd hGeometry

theorem quadraticDedekindJShiftedComplexContinuationFilledSplit_analyticAt_pos_real
    (D : NumberField.OddFundamentalDiscriminant)
    (hNoReal : QuadraticDedekindNoRealOffCriticalZero D)
    {sigma : Real} (hSigmaPos : 0 < sigma)
    (hSigmaHalf : sigma < 1 / 2) :
    AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledSplit D)
      (sigma : Complex) := by
  unfold quadraticDedekindJShiftedComplexContinuationFilledSplit
  exact
    (quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_pos_real
      D hNoReal hSigmaPos hSigmaHalf).add
      (quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_pos_real
        D hSigmaPos hSigmaHalf)


end

end RobinBV.NumberField
