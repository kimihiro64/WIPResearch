import PrimeNumberTheoremAnd.RectangleArgumentPrinciple
import RobinBV.NumberField.Proof.QuadraticDedekindNicolasNonrealOmega

/-!
# Signed real-zero residue

Focused infrastructure for the quadratic Dedekind Nicolas-Landau Omega theorem.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section
theorem tendsto_mul_self_of_sub_principal_isBigO_one_quadraticDedekind
    {f : Complex -> Complex} {p c : Complex}
    (h : (f - fun z : Complex => c / (z - p)) =O[
      nhdsWithin p (Set.compl {p})] (1 : Complex -> Complex)) :
    Tendsto (fun z : Complex => (z - p) * f z)
      (nhdsWithin p (Set.compl {p})) (nhds c) := by
  have hpTendsto : Tendsto (fun z : Complex => z - p)
      (nhdsWithin p (Set.compl {p})) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr
      (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hpSmall :
      (fun z : Complex => z - p) =o[nhdsWithin p (Set.compl {p})]
        (1 : Complex -> Complex) :=
    (Asymptotics.isLittleO_one_iff Complex).2 hpTendsto
  have hRemainder : Tendsto
      (fun z : Complex =>
        (z - p) * ((f - fun w : Complex => c / (w - p)) z))
      (nhdsWithin p (Set.compl {p})) (nhds 0) := by
    simpa using hpSmall.mul_isBigO h
  have hPrincipalEq :
      Filter.EventuallyEq (nhdsWithin p (Set.compl {p}))
        (fun z : Complex => (z - p) * (c / (z - p)))
        (fun _ : Complex => c) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    field_simp [sub_ne_zero.mpr hz]
  have hPrincipal : Tendsto
      (fun z : Complex => (z - p) * (c / (z - p)))
      (nhdsWithin p (Set.compl {p})) (nhds c) := by
    exact tendsto_const_nhds.congr' hPrincipalEq.symm
  have hSum : Tendsto
      (fun z : Complex =>
        (z - p) * (c / (z - p)) +
          (z - p) * ((f - fun w : Complex => c / (w - p)) z))
      (nhdsWithin p (Set.compl {p})) (nhds (c + 0)) :=
    hPrincipal.add hRemainder
  have hEq :
      (fun z : Complex => (z - p) * f z) =
        fun z : Complex =>
          (z - p) * (c / (z - p)) +
            (z - p) * ((f - fun w : Complex => c / (w - p)) z) := by
    funext z
    simp only [Pi.sub_apply]
    ring
  have hEqEventually : Filter.EventuallyEq
      (nhdsWithin p (Set.compl {p}))
      (fun z : Complex => (z - p) * f z)
      (fun z : Complex =>
        (z - p) * (c / (z - p)) +
          (z - p) * ((f - fun w : Complex => c / (w - p)) z)) :=
    Eventually.of_forall (fun z => congrFun hEq z)
  simpa using hSum.congr' hEqEventually.symm

theorem quadraticDedekindZeta_analyticOrderAt_ne_top
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hOne : Not (rho = 1)) :
    Not (analyticOrderAt (quadraticDedekindZetaContinuation D) rho =
      (Top.top : ENat)) := by
  have hAnalyticOn := quadraticDedekindZetaContinuation_analyticOn_compl_one D
  have hAnalyticRho : AnalyticAt Complex
      (quadraticDedekindZetaContinuation D) rho :=
    hAnalyticOn rho (Set.mem_compl_singleton_iff.mpr hOne)
  have hAnalyticTwo : AnalyticAt Complex
      (quadraticDedekindZetaContinuation D) 2 :=
    hAnalyticOn 2 (Set.mem_compl_singleton_iff.mpr (by norm_num))
  have hMeromorphicTwo : MeromorphicAt
      (quadraticDedekindZetaContinuation D) 2 :=
    hAnalyticTwo.meromorphicAt
  have hValueTwo : Not
      (quadraticDedekindZetaContinuation D 2 = 0) := by
    unfold quadraticDedekindZetaContinuation
    apply mul_ne_zero
    next => exact riemannZeta_ne_zero_of_one_le_re (by norm_num)
    next =>
      exact D.character.LFunction_ne_zero_of_one_le_re
        (Or.inl (quadraticCharacter_ne_one D)) (by norm_num)
  have hTendstoTwo : Tendsto (quadraticDedekindZetaContinuation D)
      (nhdsWithin (2 : Complex) (Set.compl {(2 : Complex)}))
      (nhds (quadraticDedekindZetaContinuation D 2)) :=
    hAnalyticTwo.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hOrderTwo :
      meromorphicOrderAt (quadraticDedekindZetaContinuation D) 2 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hMeromorphicTwo).1
      (Exists.intro (quadraticDedekindZetaContinuation D 2)
        (And.intro hValueTwo hTendstoTwo))
  have hMeromorphicOn : MeromorphicOn
      (quadraticDedekindZetaContinuation D) (Set.compl {(1 : Complex)}) :=
    hAnalyticOn.meromorphicOn
  have hMeromorphicOrderNeTop : Not
      (meromorphicOrderAt (quadraticDedekindZetaContinuation D) rho =
        (Top.top : WithTop Int)) := by
    apply hMeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (x := (2 : Complex))
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    next => exact Set.mem_compl_singleton_iff.mpr (by norm_num)
    next => exact Set.mem_compl_singleton_iff.mpr hOne
    next =>
      rw [hOrderTwo]
      simp
  intro hTop
  apply hMeromorphicOrderNeTop
  rw [hAnalyticRho.meromorphicOrderAt_eq, hTop]
  simp

def quadraticDedekindZetaZeroMultiplicity
    (D : NumberField.OddFundamentalDiscriminant)
    (rho : Complex) : Nat :=
  analyticOrderNatAt (quadraticDedekindZetaContinuation D) rho

theorem quadraticDedekindZetaZeroMultiplicity_pos
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hOne : Not (rho = 1)) :
    0 < quadraticDedekindZetaZeroMultiplicity D rho := by
  have hFinite := quadraticDedekindZeta_analyticOrderAt_ne_top D hOne
  have hAnalytic :=
    quadraticDedekindZetaContinuation_analyticOn_compl_one D rho
      (Set.mem_compl_singleton_iff.mpr hOne)
  apply Nat.pos_of_ne_zero
  intro hMultiplicityZero
  change analyticOrderNatAt
    (quadraticDedekindZetaContinuation D) rho = 0 at hMultiplicityZero
  have hOrderZero :
      analyticOrderAt (quadraticDedekindZetaContinuation D) rho = 0 := by
    rw [<- Nat.cast_analyticOrderNatAt hFinite]
    simp [hMultiplicityZero]
  exact ((hAnalytic.analyticOrderAt_eq_zero).1 hOrderZero) hZero

theorem quadraticDedekindZetaLogDeriv_scaled_tendsto_multiplicity
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hOne : Not (rho = 1)) :
    Tendsto (fun s : Complex =>
        (s - rho) * logDeriv (quadraticDedekindZetaContinuation D) s)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (quadraticDedekindZetaZeroMultiplicity D rho : Complex)) := by
  have hAnalytic :=
    quadraticDedekindZetaContinuation_analyticOn_compl_one D rho
      (Set.mem_compl_singleton_iff.mpr hOne)
  have hFinite := quadraticDedekindZeta_analyticOrderAt_ne_top D hOne
  let n : Int := quadraticDedekindZetaZeroMultiplicity D rho
  have hOrder : meromorphicOrderAt
      (quadraticDedekindZetaContinuation D) rho =
        (n : WithTop Int) := by
    rw [hAnalytic.meromorphicOrderAt_eq]
    rw [<- Nat.cast_analyticOrderNatAt hFinite]
    simp [n, quadraticDedekindZetaZeroMultiplicity]
  have hPrincipal :=
    logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
      hAnalytic.meromorphicAt hOrder
  have hLimit :=
    tendsto_mul_self_of_sub_principal_isBigO_one_quadraticDedekind
      hPrincipal
  simpa [n, quadraticDedekindZetaZeroMultiplicity] using hLimit

theorem quadraticDedekindZetaLogDeriv_realZero_scaled_tendsto_multiplicity
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real} (hOne : Not ((beta : Complex) = 1)) :
    Tendsto (fun u : Real => (u : Complex) *
        logDeriv (quadraticDedekindZetaContinuation D)
          ((beta : Complex) + (u : Complex)))
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhds (quadraticDedekindZetaZeroMultiplicity D (beta : Complex) :
        Complex)) := by
  have hRay : Tendsto (fun u : Real =>
      (beta : Complex) + (u : Complex))
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhdsWithin (beta : Complex) (Set.compl {(beta : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    next =>
      have hContinuous : ContinuousAt (fun u : Real =>
          (beta : Complex) + (u : Complex)) 0 := by
        fun_prop
      simpa using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
    next =>
      filter_upwards [self_mem_nhdsWithin] with u hu
      apply Set.mem_compl_singleton_iff.mpr
      intro hEq
      have huZero : ((u : Real) : Complex) = 0 := by
        apply add_left_cancel (a := (beta : Complex))
        simpa using hEq
      exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hu)) huZero
  have hLimit :=
    (quadraticDedekindZetaLogDeriv_scaled_tendsto_multiplicity
      D hOne).comp hRay
  simpa [Function.comp_def] using hLimit

theorem quadraticDedekindPsiMellinContinuation_realZero_scaled_tendsto
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real} (hBetaPos : 0 < beta)
    (hOne : Not ((beta : Complex) = 1)) :
    Tendsto (fun u : Real => (u : Complex) *
        quadraticDedekindPsiMellinContinuation D
          ((beta : Complex) + (u : Complex)))
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhds ((-(quadraticDedekindZetaZeroMultiplicity D
        (beta : Complex) : Real) / beta : Real) : Complex)) := by
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  have hU : Tendsto (fun u : Real => (u : Complex)) l (nhds 0) := by
    have hContinuous : ContinuousAt (fun u : Real => (u : Complex)) 0 := by
      fun_prop
    simpa [l] using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hShift : Tendsto (fun u : Real =>
      (beta : Complex) + (u : Complex)) l (nhds (beta : Complex)) := by
    simpa using tendsto_const_nhds.add hU
  have hInvAt : ContinuousAt (fun z : Complex => Inv.inv z)
      (beta : Complex) := by
    have hBetaComplexNe : Not ((beta : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr hBetaPos.ne'
    fun_prop
  have hInvShift : Tendsto
      (fun u : Real => Inv.inv ((beta : Complex) + (u : Complex))) l
      (nhds (Inv.inv (beta : Complex))) := by
    exact hInvAt.tendsto.comp hShift
  have hInvDenAt : ContinuousAt
      (fun z : Complex => Inv.inv (z - 1)) (beta : Complex) := by
    have hDen : Not ((beta : Complex) - 1 = 0) := sub_ne_zero.mpr hOne
    fun_prop
  have hInvDen : Tendsto
      (fun u : Real => Inv.inv ((beta : Complex) + (u : Complex) - 1)) l
      (nhds (Inv.inv ((beta : Complex) - 1))) := by
    exact hInvDenAt.tendsto.comp hShift
  have hLog :=
    quadraticDedekindZetaLogDeriv_realZero_scaled_tendsto_multiplicity
      D hOne
  have hMain : Tendsto (fun u : Real =>
      (-(u : Complex) *
        logDeriv (quadraticDedekindZetaContinuation D)
          ((beta : Complex) + (u : Complex))) *
        Inv.inv ((beta : Complex) + (u : Complex))) l
      (nhds ((-(quadraticDedekindZetaZeroMultiplicity D
          (beta : Complex) : Complex)) * Inv.inv (beta : Complex))) := by
    have hLogNeg := hLog.neg
    simpa [l, neg_mul] using hLogNeg.mul hInvShift
  have hCorrection : Tendsto (fun u : Real =>
      (u : Complex) * Inv.inv ((beta : Complex) + (u : Complex) - 1)) l
      (nhds 0) := by
    simpa using hU.mul hInvDen
  have hTotal : Tendsto (fun u : Real =>
      ((-(u : Complex) *
        logDeriv (quadraticDedekindZetaContinuation D)
          ((beta : Complex) + (u : Complex))) *
          Inv.inv ((beta : Complex) + (u : Complex))) -
        (u : Complex) *
          Inv.inv ((beta : Complex) + (u : Complex) - 1)) l
      (nhds ((-(quadraticDedekindZetaZeroMultiplicity D
        (beta : Complex) : Complex)) * Inv.inv (beta : Complex))) := by
    simpa using hMain.sub hCorrection
  convert hTotal using 1
  next =>
    funext u
    unfold quadraticDedekindPsiMellinContinuation
    ring
  next =>
    push_cast
    simp only [div_eq_mul_inv]

theorem quadraticDedekindPsiMellinTailContinuation_realZero_scaled_tendsto
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real} (hBetaPos : 0 < beta)
    (hOne : Not ((beta : Complex) = 1)) :
    Tendsto (fun u : Real => (u : Complex) *
        quadraticDedekindPsiMellinTailContinuation D 3
          ((beta : Complex) + (u : Complex)))
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhds ((-(quadraticDedekindZetaZeroMultiplicity D
        (beta : Complex) : Real) / beta : Real) : Complex)) := by
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  have hU : Tendsto (fun u : Real => (u : Complex)) l (nhds 0) := by
    have hContinuous : ContinuousAt (fun u : Real => (u : Complex)) 0 := by
      fun_prop
    simpa [l] using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hShift : Tendsto (fun u : Real =>
      (beta : Complex) + (u : Complex)) l (nhds (beta : Complex)) := by
    simpa using tendsto_const_nhds.add hU
  have hStartup : Tendsto
      (fun u : Real => quadraticDedekindPsiMellinStartup D 3
        ((beta : Complex) + (u : Complex))) l
      (nhds (quadraticDedekindPsiMellinStartup D 3 (beta : Complex))) :=
    (quadraticDedekindPsiMellinStartup_three_continuousAt
      D (beta : Complex)).tendsto.comp hShift
  have hStartupScaled : Tendsto (fun u : Real =>
      (u : Complex) * quadraticDedekindPsiMellinStartup D 3
        ((beta : Complex) + (u : Complex))) l (nhds 0) := by
    simpa using hU.mul hStartup
  have hFull :=
    quadraticDedekindPsiMellinContinuation_realZero_scaled_tendsto
      D hBetaPos hOne
  have hTail := hFull.sub hStartupScaled
  simpa only [quadraticDedekindPsiMellinTailContinuation,
    mul_sub, sub_zero] using hTail

theorem quadraticDedekindPsiMellinTailContinuation_realZero_coefficient_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real} (hZero :
      quadraticDedekindZetaContinuation D (beta : Complex) = 0)
    (hBetaPos : 0 < beta) (hBetaOne : beta < 1) :
    let c : Real :=
      -(quadraticDedekindZetaZeroMultiplicity D (beta : Complex) : Real) /
        beta
    And (c < 0)
      (Tendsto (fun u : Real => (u : Complex) *
          quadraticDedekindPsiMellinTailContinuation D 3
            ((beta : Complex) + (u : Complex)))
        (nhdsWithin 0 (Ioi (0 : Real))) (nhds (c : Complex))) := by
  dsimp
  constructor
  next =>
    have hMultiplicity :=
      quadraticDedekindZetaZeroMultiplicity_pos D hZero (by
        exact_mod_cast ne_of_lt hBetaOne)
    have hMultiplicityReal :
        0 < (quadraticDedekindZetaZeroMultiplicity D
          (beta : Complex) : Real) := by exact_mod_cast hMultiplicity
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hMultiplicityReal) hBetaPos
  next =>
    exact quadraticDedekindPsiMellinTailContinuation_realZero_scaled_tendsto
      D hBetaPos (by exact_mod_cast ne_of_lt hBetaOne)

theorem quadraticDedekindJRightmostRayTranslatedScaledKernel_tendsto_of_tail_pole
    (D : NumberField.OddFundamentalDiscriminant)
    {rho c : Complex} (hRhoOne : Not (rho = 1))
    (hPole : Tendsto (fun u : Real => (u : Complex) *
        quadraticDedekindPsiMellinTailContinuation D 3
          (rho + (u : Complex)))
      (nhdsWithin 0 (Ioi (0 : Real))) (nhds c)) :
    Tendsto (fun p : Prod Real Real =>
        quadraticDedekindJRightmostRayTranslatedScaledKernel
          D rho p.1 p.2)
      (nhdsWithin ((0 : Real), (0 : Real))
        {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)})
      (nhds (c / (1 - rho))) := by
  let domain : Set (Prod Real Real) :=
    {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)}
  let l : Filter (Prod Real Real) :=
    nhdsWithin ((0 : Real), (0 : Real)) domain
  let u : Prod Real Real -> Real := fun p => p.2 - p.1
  let z : Prod Real Real -> Complex := fun p =>
    quadraticDedekindRightmostRayPoint rho p.1
  let z0 : Complex := 1 - rho
  have hFst : Tendsto (fun p : Prod Real Real => p.1) l (nhds 0) := by
    exact continuousAt_fst.tendsto.mono_left nhdsWithin_le_nhds
  have hSnd : Tendsto (fun p : Prod Real Real => p.2) l (nhds 0) := by
    exact continuousAt_snd.tendsto.mono_left nhdsWithin_le_nhds
  have hU : Tendsto u l (nhds 0) := by
    dsimp [u]
    simpa using hSnd.sub hFst
  have hSndPos : Filter.Eventually
      (fun p : Prod Real Real => 0 < p.2) l := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.1.trans hp.2
  have hUPos : Filter.Eventually (fun p : Prod Real Real => 0 < u p) l := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    dsimp [u]
    linarith [hp.2]
  have hSndWithin : Tendsto (fun p : Prod Real Real => p.2) l
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro hSnd hSndPos
  have hPoleComp : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) *
        quadraticDedekindPsiMellinTailContinuation D 3
          (rho + (p.2 : Complex))) l (nhds c) :=
    hPole.comp hSndWithin
  have hBaseArg : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex))) l
      (nhdsWithin 1 (Set.compl {(1 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    next =>
      have hCast : Tendsto (fun p : Prod Real Real => (u p : Complex))
          l (nhds 0) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hU
      simpa using hCast.add tendsto_const_nhds
    next =>
      filter_upwards [hUPos] with p hp
      apply Set.mem_compl_singleton_iff.mpr
      intro hEq
      have hRe := congrArg Complex.re hEq
      simp only [Complex.ofReal_re, Complex.one_re] at hRe
      linarith
  have hBaseTail : Tendsto (fun p : Prod Real Real =>
      quadraticDedekindPsiMellinTailContinuation D 3
        (((u p + 1 : Real) : Complex))) l
      (nhds (quadraticDedekindPsiMellinTailContinuationFilled D 1)) :=
    (quadraticDedekindPsiMellinTailContinuation_tendsto_one D).comp hBaseArg
  have hSndCast : Tendsto (fun p : Prod Real Real => (p.2 : Complex))
      l (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hSnd
  have hScaledBase : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) * quadraticDedekindPsiMellinTailContinuation D 3
        (((u p + 1 : Real) : Complex))) l (nhds 0) := by
    simpa using hSndCast.mul hBaseTail
  have hZ : Tendsto z l (nhds z0) := by
    have hFstCast : Tendsto (fun p : Prod Real Real => (p.1 : Complex))
        l (nhds 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hFst
    dsimp [z, z0, quadraticDedekindRightmostRayPoint]
    simpa using (tendsto_const_nhds.sub hFstCast)
  have hz0Ne : Not (z0 = 0) := by
    dsimp [z0]
    exact sub_ne_zero.mpr (Ne.symm hRhoOne)
  have hNumerator : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex))) l (nhds 1) := by
    have hCast : Tendsto (fun p : Prod Real Real => (u p : Complex))
        l (nhds 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hU
    simpa using hCast.add tendsto_const_nhds
  have hPrefactor : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex)) / z p) l (nhds (1 / z0)) :=
    hNumerator.div hZ hz0Ne
  have hPowerAt : Tendsto (fun p : Prod Real Real =>
      (3 : Complex) ^ (z p)) l (nhds ((3 : Complex) ^ z0)) := by
    have hContinuous : ContinuousAt (fun w : Complex =>
        (3 : Complex) ^ w) z0 := by
      fun_prop
    exact hContinuous.tendsto.comp hZ
  have hDifference : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) *
          quadraticDedekindPsiMellinTailContinuation D 3
            (rho + (p.2 : Complex)) -
        (3 : Complex) ^ (z p) *
          ((p.2 : Complex) *
            quadraticDedekindPsiMellinTailContinuation D 3
              (((u p + 1 : Real) : Complex)))) l (nhds c) := by
    simpa using hPoleComp.sub (hPowerAt.mul hScaledBase)
  have hProduct := hPrefactor.mul hDifference
  convert hProduct using 1
  next =>
    funext p
    have hShift :
        ((((p.2 - p.1 + 1 : Real) : Complex) -
            quadraticDedekindRightmostRayPoint rho p.1)) =
          rho + (p.2 : Complex) := by
      unfold quadraticDedekindRightmostRayPoint
      push_cast
      ring
    unfold quadraticDedekindJRightmostRayTranslatedScaledKernel
      quadraticDedekindJMellinShiftIntegrand
    rw [hShift]
    dsimp [u, z, quadraticDedekindRightmostRayPoint]
    ring
  next =>
    dsimp [z0]
    ring

theorem exists_quadraticDedekindRealRightmostRayScaledKernel_uniform_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {beta : Real}
    (hZero : quadraticDedekindZetaContinuation D (beta : Complex) = 0)
    (hBetaPos : 0 < beta) (hBetaOne : beta < 1) :
    Exists fun d : Real => Exists fun r : Real =>
      And (d < 0) (And (0 < r) (And (r < 1 / 2)
        (forall eps v : Real, 0 < eps -> eps < v -> v <= r ->
          norm
            (quadraticDedekindJRightmostRayTranslatedScaledKernel
              D (beta : Complex) eps v - (d : Complex)) <= (-d) / 4))) := by
  let c : Real :=
    -(quadraticDedekindZetaZeroMultiplicity D (beta : Complex) : Real) /
      beta
  have hcData :=
    quadraticDedekindPsiMellinTailContinuation_realZero_coefficient_neg
      D hZero hBetaPos hBetaOne
  have hcNeg : c < 0 := by simpa [c] using hcData.1
  have hPole : Tendsto (fun u : Real => (u : Complex) *
      quadraticDedekindPsiMellinTailContinuation D 3
        ((beta : Complex) + (u : Complex)))
      (nhdsWithin 0 (Ioi (0 : Real))) (nhds (c : Complex)) := by
    simpa [c] using hcData.2
  let d : Real := c / (1 - beta)
  have hDenPos : 0 < 1 - beta := by linarith
  have hdNeg : d < 0 := div_neg_of_neg_of_pos hcNeg hDenPos
  have hLimit : Tendsto (fun p : Prod Real Real =>
      quadraticDedekindJRightmostRayTranslatedScaledKernel
        D (beta : Complex) p.1 p.2)
      (nhdsWithin ((0 : Real), (0 : Real))
        {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)})
      (nhds (d : Complex)) := by
    have hRaw :=
      quadraticDedekindJRightmostRayTranslatedScaledKernel_tendsto_of_tail_pole
        D (rho := (beta : Complex))
          (by exact_mod_cast ne_of_lt hBetaOne) hPole
    convert hRaw using 1
    push_cast
    simp [d, div_eq_mul_inv]
  have hRadius : 0 < (-d) / 4 :=
    div_pos (neg_pos.mpr hdNeg) (by norm_num)
  have hClose : Filter.Eventually
      (fun p : Prod Real Real =>
        norm (quadraticDedekindJRightmostRayTranslatedScaledKernel
          D (beta : Complex) p.1 p.2 - (d : Complex)) < (-d) / 4)
      (nhdsWithin ((0 : Real), (0 : Real))
        {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)}) := by
    have hBall := hLimit.eventually
      (Metric.ball_mem_nhds (d : Complex) hRadius)
    simpa [Metric.mem_ball, dist_eq_norm] using hBall
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hClose
  choose eta hEta hCloseEta using hClose
  let r : Real := min (eta / 2) (1 / 4)
  have hrPos : 0 < r := by
    dsimp [r]
    exact lt_min (by positivity) (by norm_num)
  have hrHalf : r < 1 / 2 := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrEta : r < eta := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine Exists.intro d (Exists.intro r
    (And.intro hdNeg (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps v hEps hEpsV hVr
  have hVPos : 0 < v := hEps.trans hEpsV
  have hDist : dist (eps, v) ((0 : Real), (0 : Real)) < eta := by
    change max (dist eps 0) (dist v 0) < eta
    rw [max_lt_iff]
    constructor
    next =>
      rw [Real.dist_eq, sub_zero, abs_of_pos hEps]
      exact hEpsV.trans_le hVr |>.trans hrEta
    next =>
      rw [Real.dist_eq, sub_zero, abs_of_pos hVPos]
      exact hVr.trans_lt hrEta
  exact (hCloseEta hDist (And.intro hEps hEpsV)).le


end

end RobinBV.NumberField
