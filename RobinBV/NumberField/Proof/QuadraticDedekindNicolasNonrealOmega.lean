import RobinBV.NumberField.Proof.QuadraticDedekindNicolasNonrealRay

/-!
# Nonreal quadratic Dedekind Omega-minus theorem

Focused infrastructure for the quadratic Dedekind Nicolas-Landau Omega theorem.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section
theorem quadraticDedekindJRightmostRayTranslatedScaledKernelFilled_intervalIntegrable
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps r : Real} (hEps : 0 < eps) (hEpsR : eps < r)
    (hWidth : r - eps <= 1) :
    IntervalIntegrable
      (quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
        D rho eps) volume eps r := by
  have hzZero : Not (quadraticDedekindRightmostRayPoint rho eps = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    unfold quadraticDedekindRightmostRayPoint at hEqIm
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.zero_im] at hEqIm
    apply hIm
    linarith
  apply ContinuousOn.intervalIntegrable
  intro v hv
  have hvIcc : Membership.mem (Icc eps r) v := by
    simpa [uIcc, min_eq_left hEpsR.le, max_eq_right hEpsR.le] using hv
  have hU : 0 <= v - eps := by linarith [hvIcc.1]
  have hULe : v - eps <= 1 := by linarith [hvIcc.2]
  let s : Complex := rho + (v : Complex)
  have hsIm : s.im = rho.im := by
    dsimp [s]
    simp
  have hsZero : Not (s = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.zero_im] at hEqIm
    exact hIm hEqIm
  have hsOne : Not (s = 1) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.one_im] at hEqIm
    exact hIm hEqIm
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
          quadraticDedekindRightmostRayPoint rho eps)) = s := by
    dsimp [s, quadraticDedekindRightmostRayPoint]
    push_cast
    ring
  have hShiftZero : Not
      ((((v - eps + 1 : Real) : Complex) -
          quadraticDedekindRightmostRayPoint rho eps) = 0) := by
    rw [hShift]
    exact hsZero
  have hShiftFactor : Not
      (quadraticDedekindZetaPoleFactor D
        (((v - eps + 1 : Real) : Complex) -
          quadraticDedekindRightmostRayPoint rho eps) = 0) := by
    rw [hShift]
    exact hFactor
  have hJoint :=
    quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne D
      (u := v - eps) (z := quadraticDedekindRightmostRayPoint rho eps)
      hU hzZero hShiftZero hShiftFactor
  have hEmbed : ContinuousAt (fun w : Real =>
      (w - eps, quadraticDedekindRightmostRayPoint rho eps)) v := by
    fun_prop
  have hTail : ContinuousAt (fun w : Real =>
      quadraticDedekindJMellinShiftIntegrandFilled D
        (quadraticDedekindRightmostRayPoint rho eps) (w - eps)) v := by
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    simpa [Function.comp_def] using hComp
  have hCast : ContinuousAt (fun w : Real => (w : Complex)) v := by
    fun_prop
  unfold quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
  exact (hCast.mul hTail).continuousWithinAt

theorem exists_quadraticDedekindRightmostRayScaledKernel_log_interval_estimate
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps : Real, 0 < eps -> eps < r ->
            norm (intervalIntegral (fun v : Real =>
                HSMul.hSMul (Inv.inv v)
                  (quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
                    D rho eps v)) eps r volume -
              HSMul.hSMul (Real.log (r / eps)) d) <=
                (norm d / 4) * abs (Real.log (r / eps))))) := by
  choose d r hd hrPos hrHalf hUniform using
    exists_quadraticDedekindRightmostRayScaledKernelFilled_uniform
      D hZero hIm hHalf hOneRe hRay
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps hEps hEpsR
  have hInt :=
    quadraticDedekindJRightmostRayTranslatedScaledKernelFilled_intervalIntegrable
      D hIm hRay hEps hEpsR (by linarith)
  apply Robin1984.norm_intervalIntegral_inv_smul_sub_le_of_intervalIntegrable
    hInt hEps hrPos (by positivity)
  intro v hv
  have hvIoc : Membership.mem (Ioc eps r) v := by
    simpa [uIoc, min_eq_left hEpsR.le, max_eq_right hEpsR.le] using hv
  exact hUniform eps v hEps hvIoc.1 hvIoc.2

theorem quadraticDedekindRightmostRay_weighted_scaledKernelFilled_interval_eq
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} {eps r : Real} (hEps : 0 < eps) (hEpsR : eps < r) :
    intervalIntegral (fun v : Real =>
        HSMul.hSMul (Inv.inv v)
          (quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
            D rho eps v)) eps r volume =
      intervalIntegral
        (quadraticDedekindJMellinShiftIntegrandFilled D
          (quadraticDedekindRightmostRayPoint rho eps))
        0 (r - eps) volume := by
  calc
    intervalIntegral (fun v : Real =>
        HSMul.hSMul (Inv.inv v)
          (quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
            D rho eps v)) eps r volume =
        intervalIntegral (fun v : Real =>
          quadraticDedekindJMellinShiftIntegrandFilled D
            (quadraticDedekindRightmostRayPoint rho eps) (v - eps))
          eps r volume := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hvIcc : Membership.mem (Icc eps r) v := by
        simpa [uIcc, min_eq_left hEpsR.le,
          max_eq_right hEpsR.le] using hv
      have hvPos : 0 < v := hEps.trans_le hvIcc.1
      unfold quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
      change ((Inv.inv v : Real) : Complex) *
          ((v : Complex) *
            quadraticDedekindJMellinShiftIntegrandFilled D
              (quadraticDedekindRightmostRayPoint rho eps) (v - eps)) =
        quadraticDedekindJMellinShiftIntegrandFilled D
          (quadraticDedekindRightmostRayPoint rho eps) (v - eps)
      rw [Complex.ofReal_inv]
      field_simp [Complex.ofReal_ne_zero.mpr hvPos.ne']
    _ = intervalIntegral
        (quadraticDedekindJMellinShiftIntegrandFilled D
          (quadraticDedekindRightmostRayPoint rho eps))
        (eps - eps) (r - eps) volume := by
      exact intervalIntegral.integral_comp_sub_right
        (quadraticDedekindJMellinShiftIntegrandFilled D
          (quadraticDedekindRightmostRayPoint rho eps)) eps
    _ = intervalIntegral
        (quadraticDedekindJMellinShiftIntegrandFilled D
          (quadraticDedekindRightmostRayPoint rho eps))
        0 (r - eps) volume := by ring_nf

theorem exists_quadraticDedekindRightmostRayCompactSingularIntegral_lowerBound
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps : Real, 0 < eps -> eps < r ->
            (3 / 4 : Real) * norm d * Real.log (r / eps) <=
              norm (intervalIntegral
                (quadraticDedekindJMellinShiftIntegrandFilled D
                  (quadraticDedekindRightmostRayPoint rho eps))
                0 (r - eps) volume)))) := by
  choose d r hd hrPos hrHalf hEstimate using
    exists_quadraticDedekindRightmostRayScaledKernel_log_interval_estimate
      D hZero hIm hHalf hOneRe hRay
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps hEps hEpsR
  let I : Complex := intervalIntegral (fun v : Real =>
      HSMul.hSMul (Inv.inv v)
        (quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
          D rho eps v)) eps r volume
  let A : Complex := HSMul.hSMul (Real.log (r / eps)) d
  have hRatio : 1 < r / eps := (one_lt_div hEps).mpr hEpsR
  have hLogPos : 0 < Real.log (r / eps) := Real.log_pos hRatio
  have hErr : norm (I - A) <=
      (norm d / 4) * Real.log (r / eps) := by
    dsimp [I, A]
    simpa [abs_of_pos hLogPos] using hEstimate eps hEps hEpsR
  have hReverse : norm A - norm I <= norm (I - A) := by
    have hBasic := (le_abs_self (norm A - norm I)).trans
      (abs_norm_sub_norm_le A I)
    simpa [norm_sub_rev] using hBasic
  have hANorm : norm A = Real.log (r / eps) * norm d := by
    dsimp [A]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hLogPos]
  have hLowerI : (3 / 4 : Real) * norm d * Real.log (r / eps) <=
      norm I := by
    rw [hANorm] at hReverse
    have hdNorm : 0 <= norm d := norm_nonneg d
    nlinarith [hReverse.trans hErr]
  dsimp [I] at hLowerI
  have hIntegralEq :
      intervalIntegral (fun v : Real =>
          ((Inv.inv v : Real) : Complex) *
            quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
              D rho eps v) eps r volume =
        intervalIntegral
          (quadraticDedekindJMellinShiftIntegrandFilled D
            (quadraticDedekindRightmostRayPoint rho eps))
          0 (r - eps) volume := by
    simpa [smul_eq_mul] using
      (quadraticDedekindRightmostRay_weighted_scaledKernelFilled_interval_eq
        D (rho := rho) hEps hEpsR)
  rw [hIntegralEq] at hLowerI
  exact hLowerI

theorem exists_quadraticDedekindRightmostRayCompactAwayKernel_bound
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {r : Real} (hrPos : 0 < r) (hrHalf : r < 1 / 2) :
    Exists fun M : Real => And (0 <= M)
      (forall eps u : Real,
        Membership.mem (Icc (0 : Real) (r / 2)) eps ->
        Membership.mem (Icc (r / 2) (1 : Real)) u ->
        norm (quadraticDedekindJMellinShiftIntegrandFilled D
          (quadraticDedekindRightmostRayPoint rho eps) u) <= M) := by
  let K : Set (Prod Real Real) := fun p =>
    And (Membership.mem (Icc (0 : Real) (r / 2)) p.1)
      (Membership.mem (Icc (r / 2) (1 : Real)) p.2)
  let F : Prod Real Real -> Complex := fun p =>
    quadraticDedekindJMellinShiftIntegrandFilled D
      (quadraticDedekindRightmostRayPoint rho p.1) p.2
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
        (quadraticDedekindRightmostRayPoint rho p.1 = 0) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      unfold quadraticDedekindRightmostRayPoint at hEqIm
      simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
        Complex.zero_im] at hEqIm
      apply hIm
      linarith
    let s : Complex := rho + ((p.1 + p.2 : Real) : Complex)
    have hsIm : s.im = rho.im := by
      dsimp [s]
      simp
    have hsZero : Not (s = 0) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      rw [hsIm, Complex.zero_im] at hEqIm
      exact hIm hEqIm
    have hsOne : Not (s = 1) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      rw [hsIm, Complex.one_im] at hEqIm
      exact hIm hEqIm
    have hSumPos : 0 < p.1 + p.2 := by
      linarith [hp.1.1, hp.2.1, hrPos]
    have hZeta : Not (quadraticDedekindZetaContinuation D s = 0) := by
      dsimp [s]
      exact hRay (p.1 + p.2) hSumPos
    have hFactor : Not (quadraticDedekindZetaPoleFactor D s = 0) := by
      intro hFactorZero
      have hIdentity :=
        quadraticDedekindZetaContinuation_eq_poleFactor_div D hsOne
      rw [hFactorZero, zero_div] at hIdentity
      exact hZeta hIdentity
    have hShift :
        ((((p.2 + 1 : Real) : Complex) -
            quadraticDedekindRightmostRayPoint rho p.1)) = s := by
      dsimp [s, quadraticDedekindRightmostRayPoint]
      push_cast
      ring
    have hShiftZero : Not
        ((((p.2 + 1 : Real) : Complex) -
            quadraticDedekindRightmostRayPoint rho p.1) = 0) := by
      rw [hShift]
      exact hsZero
    have hShiftFactor : Not
        (quadraticDedekindZetaPoleFactor D
          (((p.2 + 1 : Real) : Complex) -
            quadraticDedekindRightmostRayPoint rho p.1) = 0) := by
      rw [hShift]
      exact hFactor
    have hJoint :=
      quadraticDedekindJMellinShiftIntegrandFilled_joint_continuousAt_of_ne D
        (u := p.2) (z := quadraticDedekindRightmostRayPoint rho p.1)
        (by linarith [hp.2.1, hrPos]) hzZero hShiftZero hShiftFactor
    have hEmbed : ContinuousAt (fun q : Prod Real Real =>
        (q.2, quadraticDedekindRightmostRayPoint rho q.1)) p := by
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

theorem exists_quadraticDedekindRightmostRayCompactAwayIntegral_bound
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {r : Real} (hrPos : 0 < r) (hrHalf : r < 1 / 2) :
    Exists fun M : Real => And (0 <= M)
      (forall eps : Real, 0 <= eps -> eps <= r / 2 ->
        norm (intervalIntegral
          (quadraticDedekindJMellinShiftIntegrandFilled D
            (quadraticDedekindRightmostRayPoint rho eps))
          (r - eps) 1 volume) <= M) := by
  choose M hMNonneg hKernel using
    exists_quadraticDedekindRightmostRayCompactAwayKernel_bound
      D hIm hRay hrPos hrHalf
  refine Exists.intro M (And.intro hMNonneg ?_)
  intro eps hEps hEpsLe
  have hLowerNonneg : 0 <= r - eps := by linarith
  have hLowerOne : r - eps <= 1 := by linarith
  have hPointwise : forall u : Real,
      Membership.mem (uIoc (r - eps) (1 : Real)) u ->
      norm (quadraticDedekindJMellinShiftIntegrandFilled D
        (quadraticDedekindRightmostRayPoint rho eps) u) <= M := by
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

theorem exists_quadraticDedekindRightmostRayCompactIntegral_log_lowerBound
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real => Exists fun M : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2) (And (0 <= M)
          (forall eps : Real, 0 < eps -> eps <= r / 2 ->
            (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
              norm (intervalIntegral
                (quadraticDedekindJMellinShiftIntegrandFilled D
                  (quadraticDedekindRightmostRayPoint rho eps))
                0 1 volume))))) := by
  choose d r hd hrPos hrHalf hSingular using
    exists_quadraticDedekindRightmostRayCompactSingularIntegral_lowerBound
      D hZero hIm hHalf hOneRe hRay
  choose M hMNonneg hAway using
    exists_quadraticDedekindRightmostRayCompactAwayIntegral_bound
      D hIm hRay hrPos hrHalf
  refine Exists.intro d (Exists.intro r (Exists.intro M
    (And.intro hd (And.intro hrPos (And.intro hrHalf
      (And.intro hMNonneg ?_))))))
  intro eps hEps hEpsLe
  have hEpsR : eps < r := by linarith [hrPos]
  have hLowerNonneg : 0 <= r - eps := by linarith [hEpsLe, hrPos]
  have hLowerOne : r - eps <= 1 := by linarith [hrHalf]
  let f : Real -> Complex :=
    quadraticDedekindJMellinShiftIntegrandFilled D
      (quadraticDedekindRightmostRayPoint rho eps)
  have hIntegrableOn : IntegrableOn f (Ioc (0 : Real) 1) := by
    have hEventually :=
      eventually_quadraticDedekindJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
        D hIm hRay hEps
    have hAt := hEventually.self_of_nhds
    simpa [f, quadraticDedekindRightmostRayPoint] using hAt
  have hFullIntegrable : IntervalIntegrable f volume 0 1 := by
    rw [intervalIntegrable_iff]
    simpa [uIoc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using hIntegrableOn
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
  have hTriangle : norm L <= norm T + norm R := by
    calc
      norm L = norm ((L + R) - R) := by ring_nf
      _ <= norm (L + R) + norm R := norm_sub_le _ _
      _ = norm T + norm R := by rw [hDecomp]
  have hSing : (3 / 4 : Real) * norm d * Real.log (r / eps) <=
      norm L := by
    dsimp [L, f]
    exact hSingular eps hEps hEpsR
  have hAwayBound : norm R <= M := by
    dsimp [R, f]
    exact hAway eps hEps.le hEpsLe
  have hFinal : (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
      norm T := by
    linarith
  simpa [T, f] using hFinal

theorem quadraticDedekindRightmostRayCompactIntegral_norm_tendsto_atTop
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        norm (intervalIntegral
          (quadraticDedekindJMellinShiftIntegrandFilled D
            (quadraticDedekindRightmostRayPoint rho eps))
          0 1 volume))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  choose d r M hd hrPos hrHalf hMNonneg hLower using
    exists_quadraticDedekindRightmostRayCompactIntegral_log_lowerBound
      D hZero hIm hHalf hOneRe hRay
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
  have hCoefficient : 0 < (3 / 4 : Real) * norm d :=
    mul_pos (by norm_num) (norm_pos_iff.mpr hd)
  have hScaled : Tendsto (fun eps : Real =>
      ((3 / 4 : Real) * norm d) * Real.log (r / eps))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop :=
    Tendsto.const_mul_atTop hCoefficient hLog
  have hLowerTendsto : Tendsto (fun eps : Real =>
      (3 / 4 : Real) * norm d * Real.log (r / eps) - M)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    simpa [mul_assoc, sub_eq_add_neg] using
      (tendsto_atTop_add_const_right
        (nhdsWithin 0 (Ioi (0 : Real))) (-M) hScaled)
  have hSmall : Filter.Eventually (fun eps : Real => eps <= r / 2)
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    have hNhd : Membership.mem (nhds (0 : Real)) (Iio (r / 2)) :=
      Iio_mem_nhds (by positivity)
    have hNhdWithin : Filter.Eventually (fun eps : Real => eps < r / 2)
        (nhdsWithin 0 (Ioi (0 : Real))) :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hNhd
    filter_upwards [hNhdWithin] with eps hEps
    exact hEps.le
  have hEventualLower : Filter.Eventually (fun eps : Real =>
      (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
        norm (intervalIntegral
          (quadraticDedekindJMellinShiftIntegrandFilled D
            (quadraticDedekindRightmostRayPoint rho eps))
          0 1 volume))
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    filter_upwards [self_mem_nhdsWithin, hSmall] with eps hEps hEpsLe
    exact hLower eps (mem_Ioi.mp hEps) hEpsLe
  exact tendsto_atTop_mono'
    (nhdsWithin 0 (Ioi (0 : Real))) hEventualLower hLowerTendsto

theorem quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRayEndpoint
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re) :
    AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledLarge D)
      (quadraticDedekindRightmostRayPoint rho 0) := by
  let center : Complex := quadraticDedekindRightmostRayPoint rho 0
  have hCenterIm : center.im = -rho.im := by
    dsimp [center, quadraticDedekindRightmostRayPoint]
    simp
  have hCenterNe : Not (center = 0) := by
    intro hEq
    have hZeroIm : center.im = 0 := by rw [hEq]; simp
    apply hIm
    linarith [hCenterIm, hZeroIm]
  have hCenterNorm : 0 < norm center := norm_pos_iff.mpr hCenterNe
  have hCenterRe : center.re = 1 - rho.re := by
    dsimp [center, quadraticDedekindRightmostRayPoint]
    simp
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
  apply quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    D hRPos hd
  intro z hz
  exact hGeometry z (by simpa [center] using hz)

theorem quadraticDedekindJShiftedComplexContinuationFilledLarge_rightmostRay_tendsto
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re) :
    Tendsto (fun eps : Real =>
        quadraticDedekindJShiftedComplexContinuationFilledLarge D
          (quadraticDedekindRightmostRayPoint rho eps))
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhds (quadraticDedekindJShiftedComplexContinuationFilledLarge D
        (quadraticDedekindRightmostRayPoint rho 0))) := by
  have hOuter :=
    (quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRayEndpoint
      D hIm hHalf).continuousAt.tendsto
  have hInner : Tendsto (quadraticDedekindRightmostRayPoint rho)
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhds (quadraticDedekindRightmostRayPoint rho 0)) := by
    have hContinuous : ContinuousAt
        (quadraticDedekindRightmostRayPoint rho) 0 := by
      unfold quadraticDedekindRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  exact hOuter.comp hInner

theorem quadraticDedekindJShiftedComplexContinuationFilledSplit_rightmostRay_norm_tendsto_atTop
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        norm (quadraticDedekindJShiftedComplexContinuationFilledSplit D
          (quadraticDedekindRightmostRayPoint rho eps)))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let C : Real -> Complex := fun eps =>
    quadraticDedekindJShiftedComplexContinuationFilledCompact D
      (quadraticDedekindRightmostRayPoint rho eps)
  let G : Real -> Complex := fun eps =>
    quadraticDedekindJShiftedComplexContinuationFilledLarge D
      (quadraticDedekindRightmostRayPoint rho eps)
  let H : Real -> Complex := fun eps =>
    quadraticDedekindJShiftedComplexContinuationFilledSplit D
      (quadraticDedekindRightmostRayPoint rho eps)
  have hCompact : Tendsto (fun eps : Real => norm (C eps)) l atTop := by
    have hBase :=
      quadraticDedekindRightmostRayCompactIntegral_norm_tendsto_atTop
        D hZero hIm hHalf hOneRe hRay
    simpa [l, C,
      quadraticDedekindJShiftedComplexContinuationFilledCompact,
      intervalIntegral.integral_of_le zero_le_one] using hBase
  let G0 : Complex :=
    quadraticDedekindJShiftedComplexContinuationFilledLarge D
      (quadraticDedekindRightmostRayPoint rho 0)
  have hLarge : Tendsto G l (nhds G0) := by
    simpa [l, G, G0] using
      quadraticDedekindJShiftedComplexContinuationFilledLarge_rightmostRay_tendsto
        D hIm hHalf
  have hLargeBound : Filter.Eventually (fun eps : Real =>
      norm (G eps) <= norm G0 + 1) l := by
    have hBall := hLarge.eventually
      (Metric.ball_mem_nhds G0 (by norm_num : (0 : Real) < 1))
    filter_upwards [hBall] with eps hEps
    have hDist : norm (G eps - G0) < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hEps
    calc
      norm (G eps) = norm ((G eps - G0) + G0) := by ring_nf
      _ <= norm (G eps - G0) + norm G0 := norm_add_le _ _
      _ <= norm G0 + 1 := by linarith
  have hEq : forall eps : Real, H eps = C eps + G eps := by
    intro eps
    rfl
  have hLowerTendsto : Tendsto (fun eps : Real =>
      norm (C eps) - (norm G0 + 1)) l atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right l (-(norm G0 + 1)) hCompact)
  have hEventualLower : Filter.Eventually (fun eps : Real =>
      norm (C eps) - (norm G0 + 1) <= norm (H eps)) l := by
    filter_upwards [hLargeBound] with eps hGBound
    have hTriangle : norm (C eps) <= norm (H eps) + norm (G eps) := by
      calc
        norm (C eps) = norm ((C eps + G eps) - G eps) := by ring_nf
        _ = norm (H eps - G eps) := by rw [hEq]
        _ <= norm (H eps) + norm (G eps) := norm_sub_le _ _
    linarith
  exact tendsto_atTop_mono' l hEventualLower hLowerTendsto

theorem quadraticDedekindLandauPositiveComplexContinuationFilledSplit_rightmostRay_norm_tendsto_atTop
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        norm (quadraticDedekindLandauPositiveComplexContinuationFilledSplit
          D X b (quadraticDedekindRightmostRayPoint rho eps)))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let J : Real -> Complex := fun eps =>
    quadraticDedekindJShiftedComplexContinuationFilledSplit D
      (quadraticDedekindRightmostRayPoint rho eps)
  let correction : Real -> Complex := fun eps =>
    -quadraticDedekindJComplexMellinStartup D X
        (quadraticDedekindRightmostRayPoint rho eps) +
      Robin1984.nicolasLandauRpowComplexContinuation X b
        (quadraticDedekindRightmostRayPoint rho eps)
  let P : Real -> Complex := fun eps =>
    quadraticDedekindLandauPositiveComplexContinuationFilledSplit
      D X b (quadraticDedekindRightmostRayPoint rho eps)
  have hJ : Tendsto (fun eps : Real => norm (J eps)) l atTop := by
    simpa [l, J] using
      quadraticDedekindJShiftedComplexContinuationFilledSplit_rightmostRay_norm_tendsto_atTop
        D hZero hIm hHalf hOneRe hRay
  have hPointNeB : Not
      (quadraticDedekindRightmostRayPoint rho 0 = (b : Complex)) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    unfold quadraticDedekindRightmostRayPoint at hEqIm
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im] at hEqIm
    apply hIm
    linarith
  have hCorrectionAnalytic : AnalyticAt Complex (fun z : Complex =>
      -quadraticDedekindJComplexMellinStartup D X z +
        Robin1984.nicolasLandauRpowComplexContinuation X b z)
      (quadraticDedekindRightmostRayPoint rho 0) := by
    exact (quadraticDedekindJComplexMellinStartup_analyticAt D hX _).neg.add
      (Robin1984.nicolasLandauRpowComplexContinuation_analyticAt
        (lt_of_lt_of_le (by norm_num) hX) hPointNeB)
  let correction0 : Complex :=
    -quadraticDedekindJComplexMellinStartup D X
        (quadraticDedekindRightmostRayPoint rho 0) +
      Robin1984.nicolasLandauRpowComplexContinuation X b
        (quadraticDedekindRightmostRayPoint rho 0)
  have hInner : Tendsto (quadraticDedekindRightmostRayPoint rho) l
      (nhds (quadraticDedekindRightmostRayPoint rho 0)) := by
    have hContinuous : ContinuousAt
        (quadraticDedekindRightmostRayPoint rho) 0 := by
      unfold quadraticDedekindRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hCorrection : Tendsto correction l (nhds correction0) := by
    have hComp := hCorrectionAnalytic.continuousAt.tendsto.comp hInner
    simpa [correction, correction0, Function.comp_def] using hComp
  have hCorrectionBound : Filter.Eventually (fun eps : Real =>
      norm (correction eps) <= norm correction0 + 1) l := by
    have hBall := hCorrection.eventually
      (Metric.ball_mem_nhds correction0 (by norm_num : (0 : Real) < 1))
    filter_upwards [hBall] with eps hEps
    have hDist : norm (correction eps - correction0) < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hEps
    calc
      norm (correction eps) =
          norm ((correction eps - correction0) + correction0) := by ring_nf
      _ <= norm (correction eps - correction0) + norm correction0 :=
        norm_add_le _ _
      _ <= norm correction0 + 1 := by linarith
  have hEq : forall eps : Real, P eps = J eps + correction eps := by
    intro eps
    unfold P J correction
      quadraticDedekindLandauPositiveComplexContinuationFilledSplit
    ring
  have hLowerTendsto : Tendsto (fun eps : Real =>
      norm (J eps) - (norm correction0 + 1)) l atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right l (-(norm correction0 + 1)) hJ)
  have hEventualLower : Filter.Eventually (fun eps : Real =>
      norm (J eps) - (norm correction0 + 1) <= norm (P eps)) l := by
    filter_upwards [hCorrectionBound] with eps hBound
    have hTriangle : norm (J eps) <=
        norm (P eps) + norm (correction eps) := by
      calc
        norm (J eps) =
            norm ((J eps + correction eps) - correction eps) := by ring_nf
        _ = norm (P eps - correction eps) := by rw [hEq]
        _ <= norm (P eps) + norm (correction eps) := norm_sub_le _ _
    linarith
  exact tendsto_atTop_mono' l hEventualLower hLowerTendsto

theorem exists_quadraticDedekindNicolasJ_omegaMinus_of_nonreal_rightmost_zero_of_noReal
    (D : NumberField.OddFundamentalDiscriminant)
    (hNoReal : QuadraticDedekindNoRealOffCriticalZero D)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0)) :
    Exists fun b : Real => And (0 < b) (And (b < 1 / 2)
      (Robin1984.AtTopOmegaMinus (quadraticDedekindNicolasJ D)
        (fun x : Real => x ^ (-b)))) := by
  let b : Real := ((1 - rho.re) + 1 / 2) / 2
  have hbPos : 0 < b := by
    dsimp [b]
    linarith
  have hbLower : 1 - rho.re < b := by
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
  let MGF : Real -> Complex := fun eps =>
    complexMGF (fun x : Real => Real.log x)
      (quadraticDedekindLandauPositiveMeasure D X b)
      (quadraticDedekindRightmostRayPoint rho eps)
  let P : Real -> Complex := fun eps =>
    quadraticDedekindLandauPositiveComplexContinuationFilledSplit
      D X b (quadraticDedekindRightmostRayPoint rho eps)
  have hPointRe : (quadraticDedekindRightmostRayPoint rho 0).re =
      1 - rho.re := by
    unfold quadraticDedekindRightmostRayPoint
    simp
  have hMGFAnalytic : AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b))
      (quadraticDedekindRightmostRayPoint rho 0) := by
    apply quadraticDedekindLandauComplexMGF_analyticAt_of_noReal
      D hNoReal hX hbPos hbHalf.le hPos
    rw [hPointRe]
    exact hbLower
  let MGF0 : Complex := complexMGF (fun x : Real => Real.log x)
    (quadraticDedekindLandauPositiveMeasure D X b)
    (quadraticDedekindRightmostRayPoint rho 0)
  have hInner : Tendsto (quadraticDedekindRightmostRayPoint rho) l
      (nhds (quadraticDedekindRightmostRayPoint rho 0)) := by
    have hContinuous : ContinuousAt
        (quadraticDedekindRightmostRayPoint rho) 0 := by
      unfold quadraticDedekindRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hMGF : Tendsto MGF l (nhds MGF0) := by
    have hComp := hMGFAnalytic.continuousAt.tendsto.comp hInner
    simpa [MGF, MGF0, Function.comp_def] using hComp
  have hEq : Filter.Eventually (fun eps : Real => MGF eps = P eps) l := by
    filter_upwards [self_mem_nhdsWithin] with eps hEps
    dsimp [MGF, P]
    exact
      quadraticDedekindLandauComplexMGF_eq_continuationFilledSplit_rightmostRay_of_noReal
        D hNoReal hX hbPos hbHalf.le hPos hIm hHalf hbLower hRay
        (mem_Ioi.mp hEps)
  have hPNormFinite : Tendsto (fun eps : Real => norm (P eps)) l
      (nhds (norm MGF0)) := by
    have hMGFNorm := hMGF.norm
    apply hMGFNorm.congr'
    filter_upwards [hEq] with eps hAt
    rw [hAt]
  have hPNormTop : Tendsto (fun eps : Real => norm (P eps)) l atTop := by
    simpa [l, P] using
      quadraticDedekindLandauPositiveComplexContinuationFilledSplit_rightmostRay_norm_tendsto_atTop
        D hX hZero hIm hHalf hOneRe hRay
  exact not_tendsto_nhds_of_tendsto_atTop
    hPNormTop (norm MGF0) hPNormFinite

theorem exists_quadraticDedekindNicolasJ_omegaMinus_of_not_ERH_of_noReal
    (D : NumberField.OddFundamentalDiscriminant)
    (hNoReal : QuadraticDedekindNoRealOffCriticalZero D)
    (hNotERH : Not (QuadraticDedekindZetaERH D)) :
    Exists fun b : Real => And (0 < b) (And (b < 1 / 2)
      (Robin1984.AtTopOmegaMinus (quadraticDedekindNicolasJ D)
        (fun x : Real => x ^ (-b)))) := by
  choose rho hZero hHalf hOneRe hRay c hc hPole using
    exists_rightmost_quadraticDedekindPsiMellinTail_pole_of_not_ERH
      D hNotERH
  have hIm : Not (rho.im = 0) := by
    intro hRhoIm
    have hEq : rho = (rho.re : Complex) := by
      apply Complex.ext
      next => simp
      next => simpa using hRhoIm
    rw [hEq] at hZero
    exact hNoReal rho.re hHalf hOneRe hZero
  exact
    exists_quadraticDedekindNicolasJ_omegaMinus_of_nonreal_rightmost_zero_of_noReal
      D hNoReal hZero hIm hHalf hOneRe hRay


end

end RobinBV.NumberField
