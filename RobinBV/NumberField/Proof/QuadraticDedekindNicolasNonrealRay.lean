import RobinBV.NumberField.Proof.QuadraticDedekindNicolasPositive

/-!
# Nonreal quadratic Dedekind rightmost ray

Focused infrastructure for the quadratic Dedekind Nicolas-Landau Omega theorem.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section
def quadraticDedekindLandauPositiveRealContinuationFilledSplit
    (D : NumberField.OddFundamentalDiscriminant)
    (X b a : Real) : Real :=
  (quadraticDedekindLandauPositiveComplexContinuationFilledSplit
    D X b (a : Complex)).re

theorem quadraticDedekindLandauPositiveRealContinuationFilledSplit_eq_mgf_of_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    {a : Real} (ha : a < 0) :
    quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b a =
      mgf (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b) a := by
  have hComplex :=
    quadraticDedekindLandauComplexMGF_eq_continuationFilledSplit_of_re_neg
      D hX hb hPos (z := (a : Complex)) (by simpa using ha)
  have hRe := congrArg Complex.re hComplex
  simpa [quadraticDedekindLandauPositiveRealContinuationFilledSplit,
    re_complexMGF_ofReal] using hRe.symm

theorem quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_zero
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) :
    AnalyticAt Real
      (quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b) 0 := by
  have hShift :=
    quadraticDedekindJShiftedComplexContinuationFilledSplit_analyticAt_zero D
  have hStartup := quadraticDedekindJComplexMellinStartup_analyticAt D hX 0
  have hRpow := Robin1984.nicolasLandauRpowComplexContinuation_analyticAt
    (X := X) (b := b) (z := (0 : Complex))
    (lt_of_lt_of_le (by norm_num) hX) (by
      intro hEq
      have hRe := congrArg Complex.re hEq
      simp only [Complex.zero_re, Complex.ofReal_re] at hRe
      linarith)
  have hComplex : AnalyticAt Complex
      (quadraticDedekindLandauPositiveComplexContinuationFilledSplit D X b)
      0 := by
    unfold quadraticDedekindLandauPositiveComplexContinuationFilledSplit
    exact (hShift.sub hStartup).add hRpow
  unfold quadraticDedekindLandauPositiveRealContinuationFilledSplit
  exact Robin1984.realAnalyticAt_re_comp_of_complexAnalyticAt hComplex

theorem quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_pos
    (D : NumberField.OddFundamentalDiscriminant)
    (hNoReal : QuadraticDedekindNoRealOffCriticalZero D)
    {X b sigma : Real} (hX : 3 <= X)
    (hSigmaPos : 0 < sigma) (hSigmaHalf : sigma < 1 / 2)
    (hSigmaB : sigma < b) :
    AnalyticAt Real
      (quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b)
      sigma := by
  have hShift :=
    quadraticDedekindJShiftedComplexContinuationFilledSplit_analyticAt_pos_real
      D hNoReal hSigmaPos hSigmaHalf
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

theorem quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {X b sigma : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    (hSigma : sigma < 0) :
    AnalyticAt Real
      (quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b)
      sigma := by
  have hInterior : Membership.mem
      (interior (integrableExpSet (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b))) sigma :=
    Iio_zero_subset_interior_integrableExpSet_quadraticDedekindLandau
      D hX hb hPos hSigma
  have hMgf : AnalyticAt Real
      (mgf (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b)) sigma :=
    analyticAt_mgf hInterior
  have hEq : Filter.EventuallyEq (nhds sigma)
      (mgf (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b))
      (quadraticDedekindLandauPositiveRealContinuationFilledSplit D X b) := by
    filter_upwards [Iio_mem_nhds hSigma] with a ha
    exact
      (quadraticDedekindLandauPositiveRealContinuationFilledSplit_eq_mgf_of_neg
        D hX hb hPos ha).symm
  exact (analyticAt_congr hEq).mp hMgf

theorem quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_lt
    (D : NumberField.OddFundamentalDiscriminant)
    (hNoReal : QuadraticDedekindNoRealOffCriticalZero D)
    {X b sigma : Real} (hX : 3 <= X) (hb : 0 < b)
    (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    (hSigma : sigma < b) :
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
      quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_pos
        D hNoReal hX hPosSigma (lt_of_lt_of_le hSigma hbHalf) hSigma

theorem Iio_subset_interior_integrableExpSet_quadraticDedekindLandau_of_noReal
    (D : NumberField.OddFundamentalDiscriminant)
    (hNoReal : QuadraticDedekindNoRealOffCriticalZero D)
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x) :
    Iio b <= interior
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
      quadraticDedekindLandauPositiveRealContinuationFilledSplit_analyticAt_lt
        D hNoReal hX hb hbHalf hPos hSigma
  next =>
    intro a ha
    exact
      (quadraticDedekindLandauPositiveRealContinuationFilledSplit_eq_mgf_of_neg
        D hX hb hPos ha).symm

theorem quadraticDedekindLandauComplexMGF_analyticAt_of_noReal
    (D : NumberField.OddFundamentalDiscriminant)
    (hNoReal : QuadraticDedekindNoRealOffCriticalZero D)
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    {z : Complex} (hz : z.re < b) :
    AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b)) z := by
  apply analyticAt_complexMGF
  exact Iio_subset_interior_integrableExpSet_quadraticDedekindLandau_of_noReal
    D hNoReal hX hb hbHalf hPos hz

theorem quadraticDedekindJShiftedComplexContinuationFilledSplit_analyticAt_rightmostRay
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex
      (quadraticDedekindJShiftedComplexContinuationFilledSplit D)
      ((1 - rho) - (eps : Complex)) := by
  unfold quadraticDedekindJShiftedComplexContinuationFilledSplit
  exact
    (quadraticDedekindJShiftedComplexContinuationFilledCompact_analyticAt_rightmostRay
      D hIm hRay hEps).add
      (quadraticDedekindJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRay
        D hIm hHalf hEps)

theorem quadraticDedekindLandauPositiveComplexContinuationFilledSplit_analyticAt_rightmostRay
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex
      (quadraticDedekindLandauPositiveComplexContinuationFilledSplit D X b)
      ((1 - rho) - (eps : Complex)) := by
  have hShift :=
    quadraticDedekindJShiftedComplexContinuationFilledSplit_analyticAt_rightmostRay
      D hIm hHalf hRay hEps
  have hStartup := quadraticDedekindJComplexMellinStartup_analyticAt
    D hX ((1 - rho) - (eps : Complex))
  have hPointIm : (((1 - rho) - (eps : Complex))).im = -rho.im := by
    simp
  have hPointNe : Not (((1 - rho) - (eps : Complex)) = (b : Complex)) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hPointIm, Complex.ofReal_im] at hEqIm
    exact hIm (neg_eq_zero.mp hEqIm)
  have hRpow := Robin1984.nicolasLandauRpowComplexContinuation_analyticAt
    (X := X) (b := b) (z := ((1 - rho) - (eps : Complex)))
    (lt_of_lt_of_le (by norm_num) hX) hPointNe
  unfold quadraticDedekindLandauPositiveComplexContinuationFilledSplit
  exact (hShift.sub hStartup).add hRpow

theorem quadraticDedekindLandauComplexMGF_rightmostRay_analyticAt_real_of_noReal
    (D : NumberField.OddFundamentalDiscriminant)
    (hNoReal : QuadraticDedekindNoRealOffCriticalZero D)
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    {rho : Complex} (hHalf : (1 / 2 : Real) < rho.re)
    (hLower : 1 - rho.re < b)
    {eps : Real} (hEps : 0 <= eps) :
    AnalyticAt Real (fun e : Real =>
      complexMGF (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b)
        ((1 - rho) - (e : Complex))) eps := by
  have hOuterComplex := quadraticDedekindLandauComplexMGF_analyticAt_of_noReal
    D hNoReal hX hb hbHalf hPos (z := ((1 - rho) - (eps : Complex))) (by
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith)
  have hOuterReal : AnalyticAt Real
      (complexMGF (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b))
      ((1 - rho) - (eps : Complex)) := hOuterComplex.restrictScalars
  have hInner : AnalyticAt Real (fun e : Real =>
      (1 - rho) - (e : Complex)) eps := by
    exact analyticAt_const.sub (Complex.ofRealCLM.analyticAt eps)
  exact hOuterReal.comp_of_eq hInner rfl

theorem quadraticDedekindLandauPositiveComplexContinuationFilledSplit_rightmostRay_analyticAt_real
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Real (fun e : Real =>
      quadraticDedekindLandauPositiveComplexContinuationFilledSplit D X b
        ((1 - rho) - (e : Complex))) eps := by
  have hOuterComplex :=
    quadraticDedekindLandauPositiveComplexContinuationFilledSplit_analyticAt_rightmostRay
      D (b := b) hX hIm hHalf hRay hEps
  have hOuterReal : AnalyticAt Real
      (quadraticDedekindLandauPositiveComplexContinuationFilledSplit D X b)
      ((1 - rho) - (eps : Complex)) := hOuterComplex.restrictScalars
  have hInner : AnalyticAt Real (fun e : Real =>
      (1 - rho) - (e : Complex)) eps := by
    exact analyticAt_const.sub (Complex.ofRealCLM.analyticAt eps)
  exact hOuterReal.comp_of_eq hInner rfl

theorem quadraticDedekindLandauComplexMGF_eq_continuationFilledSplit_rightmostRay_of_noReal
    (D : NumberField.OddFundamentalDiscriminant)
    (hNoReal : QuadraticDedekindNoRealOffCriticalZero D)
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hHalf : (1 / 2 : Real) < rho.re)
    (hLower : 1 - rho.re < b)
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    complexMGF (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b)
        ((1 - rho) - (eps : Complex)) =
      quadraticDedekindLandauPositiveComplexContinuationFilledSplit D X b
        ((1 - rho) - (eps : Complex)) := by
  let F : Real -> Complex := fun e : Real =>
    complexMGF (fun x : Real => Real.log x)
      (quadraticDedekindLandauPositiveMeasure D X b)
      ((1 - rho) - (e : Complex))
  let G : Real -> Complex := fun e : Real =>
    quadraticDedekindLandauPositiveComplexContinuationFilledSplit D X b
      ((1 - rho) - (e : Complex))
  have hF : AnalyticOnNhd Real F (Ioi (0 : Real)) := by
    intro e he
    dsimp [F]
    exact
      quadraticDedekindLandauComplexMGF_rightmostRay_analyticAt_real_of_noReal
        D hNoReal hX hb hbHalf hPos hHalf hLower (mem_Ioi.mp he).le
  have hG : AnalyticOnNhd Real G (Ioi (0 : Real)) := by
    intro e he
    dsimp [G]
    exact
      quadraticDedekindLandauPositiveComplexContinuationFilledSplit_rightmostRay_analyticAt_real
        D hX hIm hHalf hRay (mem_Ioi.mp he)
  have hEqNhd : Filter.EventuallyEq (nhds (2 : Real)) F G := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (1 : Real) < 2)] with e he
    dsimp [F, G]
    apply quadraticDedekindLandauComplexMGF_eq_continuationFilledSplit_of_re_neg
      D hX hb hPos
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith [mem_Ioi.mp he]
  have hEqOn : EqOn F G (Ioi (0 : Real)) :=
    hF.eqOn_of_preconnected_of_eventuallyEq hG
      (convex_Ioi (0 : Real)).isPreconnected (by norm_num) hEqNhd
  exact hEqOn hEps

def quadraticDedekindRightmostRayPoint
    (rho : Complex) (eps : Real) : Complex :=
  (1 - rho) - (eps : Complex)

def quadraticDedekindJRightmostRayTranslatedScaledKernel
    (D : NumberField.OddFundamentalDiscriminant)
    (rho : Complex) (eps v : Real) : Complex :=
  (v : Complex) * quadraticDedekindJMellinShiftIntegrand D
    (quadraticDedekindRightmostRayPoint rho eps) (v - eps)

theorem quadraticDedekindJMellinShiftIntegrandFilled_eq_raw_rightmostRay
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps u : Real} (hEps : 0 < eps) (hU : 0 < u) :
    quadraticDedekindJMellinShiftIntegrandFilled D
        (quadraticDedekindRightmostRayPoint rho eps) u =
      quadraticDedekindJMellinShiftIntegrand D
        (quadraticDedekindRightmostRayPoint rho eps) u := by
  have hzZero : Not (quadraticDedekindRightmostRayPoint rho eps = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    unfold quadraticDedekindRightmostRayPoint at hEqIm
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.zero_im] at hEqIm
    apply hIm
    linarith
  let s : Complex := rho + ((eps + u : Real) : Complex)
  have hShift :
      (((u + 1 : Real) : Complex) -
          quadraticDedekindRightmostRayPoint rho eps) = s := by
    dsimp [s, quadraticDedekindRightmostRayPoint]
    push_cast
    ring
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
      (Inv.inv (quadraticDedekindRightmostRayPoint rho eps - 0) *
        (quadraticDedekindJShiftNumeratorFilled D
            (quadraticDedekindRightmostRayPoint rho eps) u -
          quadraticDedekindJShiftNumeratorFilled D 0 u)) =
    quadraticDedekindJMellinShiftIntegrand D
      (quadraticDedekindRightmostRayPoint rho eps) u
  rw [quadraticDedekindJShiftNumeratorFilled_zero]
  simp only [smul_eq_mul, vsub_eq_sub, sub_zero, inv_mul_eq_div]
  unfold quadraticDedekindJShiftNumeratorFilled
    quadraticDedekindJMellinShiftIntegrand
  rw [hShift]
  change ((u + 1 : Real) : Complex) *
      ((quadraticDedekindPsiMellinTailContinuationFilled D s -
        (3 : Complex) ^ (quadraticDedekindRightmostRayPoint rho eps) *
          quadraticDedekindPsiMellinTailContinuationFilled D base) /
        quadraticDedekindRightmostRayPoint rho eps) =
    ((u + 1 : Real) : Complex) *
      ((quadraticDedekindPsiMellinTailContinuation D 3 s -
        (3 : Complex) ^ (quadraticDedekindRightmostRayPoint rho eps) *
          quadraticDedekindPsiMellinTailContinuation D 3 base) /
        quadraticDedekindRightmostRayPoint rho eps)
  rw [<- hShiftEq, <- hBaseEq]

def quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
    (D : NumberField.OddFundamentalDiscriminant)
    (rho : Complex) (eps v : Real) : Complex :=
  (v : Complex) * quadraticDedekindJMellinShiftIntegrandFilled D
    (quadraticDedekindRightmostRayPoint rho eps) (v - eps)

theorem quadraticDedekindJRightmostRayTranslatedScaledKernelFilled_eq_raw
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex} (hIm : Not (rho.im = 0))
    (hRay : forall v : Real, 0 < v ->
      Not (quadraticDedekindZetaContinuation D
        (rho + (v : Complex)) = 0))
    {eps v : Real} (hEps : 0 < eps) (hEpsV : eps < v) :
    quadraticDedekindJRightmostRayTranslatedScaledKernelFilled D rho eps v =
      quadraticDedekindJRightmostRayTranslatedScaledKernel D rho eps v := by
  unfold quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
    quadraticDedekindJRightmostRayTranslatedScaledKernel
  rw [quadraticDedekindJMellinShiftIntegrandFilled_eq_raw_rightmostRay
    D hIm hRay hEps (by linarith)]

theorem quadraticDedekindJRightmostRayTranslatedScaledKernel_tendsto
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Exists fun d : Complex => And (Not (d = 0))
      (Tendsto (fun p : Prod Real Real =>
          quadraticDedekindJRightmostRayTranslatedScaledKernel
            D rho p.1 p.2)
        (nhdsWithin ((0 : Real), (0 : Real))
          {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)})
        (nhds d)) := by
  have hRhoZero : Not (rho = 0) := by
    intro hEq
    rw [hEq] at hHalf
    norm_num at hHalf
  have hRhoOne : Not (rho = 1) := by
    intro hEq
    rw [hEq] at hOneRe
    norm_num at hOneRe
  choose c hc hPole using
    quadraticDedekindPsiMellinTailContinuation_three_simplePoleLimit_Ioi
      D hZero hRhoZero hRhoOne
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
  have hUWithin : Tendsto u l (nhdsWithin 0 (Ioi (0 : Real))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro hU hUPos
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
  let d : Complex := c / z0
  have hd : Not (d = 0) := div_ne_zero hc hz0Ne
  refine Exists.intro d (And.intro hd ?_)
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
    dsimp [d]
    ring

theorem exists_quadraticDedekindRightmostRayScaledKernel_uniform
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps v : Real, 0 < eps -> eps < v -> v <= r ->
            norm
              (quadraticDedekindJRightmostRayTranslatedScaledKernel
                D rho eps v - d) <= norm d / 4))) := by
  choose d hd hLimit using
    quadraticDedekindJRightmostRayTranslatedScaledKernel_tendsto
      D hZero hHalf hOneRe
  have hdNorm : 0 < norm d := norm_pos_iff.mpr hd
  have hClose : Filter.Eventually
      (fun p : Prod Real Real =>
        norm
          (quadraticDedekindJRightmostRayTranslatedScaledKernel
            D rho p.1 p.2 - d) < norm d / 4)
      (nhdsWithin ((0 : Real), (0 : Real))
        {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)}) := by
    have hBall := hLimit.eventually
      (Metric.ball_mem_nhds d (by positivity : 0 < norm d / 4))
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
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
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

theorem exists_quadraticDedekindRightmostRayScaledKernelFilled_uniform
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
          (forall eps v : Real, 0 < eps -> eps < v -> v <= r ->
            norm
              (quadraticDedekindJRightmostRayTranslatedScaledKernelFilled
                D rho eps v - d) <= norm d / 4))) := by
  choose d r hd hrPos hrHalf hUniform using
    exists_quadraticDedekindRightmostRayScaledKernel_uniform
      D hZero hHalf hOneRe
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps v hEps hEpsV hVr
  rw [quadraticDedekindJRightmostRayTranslatedScaledKernelFilled_eq_raw
    D hIm hRay hEps hEpsV]
  exact hUniform eps v hEps hEpsV hVr


end

end RobinBV.NumberField
