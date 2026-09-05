import Robin1984.NicolasLandau.NicolasLandauRightmostRay
import RobinBV.NumberField.Proof.QuadraticDedekindJMellin

/-!
# Quadratic Dedekind Nicolas continuations

Focused infrastructure for the quadratic Dedekind Nicolas-Landau Omega theorem.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section
def quadraticDedekindJMellinShiftIntegrand
    (D : NumberField.OddFundamentalDiscriminant)
    (z : Complex) (u : Real) : Complex :=
  ((u + 1 : Real) : Complex) *
    ((quadraticDedekindPsiMellinTailContinuation D 3
        (((u + 1 : Real) : Complex) - z) -
      (3 : Complex) ^ z *
        quadraticDedekindPsiMellinTailContinuation D 3
          ((u + 1 : Real) : Complex)) / z)

def quadraticDedekindJShiftedComplexContinuation
    (D : NumberField.OddFundamentalDiscriminant)
    (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (0 : Real)))
    (quadraticDedekindJMellinShiftIntegrand D z)

def quadraticDedekindJComplexMellinStartup
    (D : NumberField.OddFundamentalDiscriminant)
    (X : Real) (z : Complex) : Complex :=
  integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
    (x : Complex) ^ (z - 1) * (quadraticDedekindNicolasJ D x : Complex))

def quadraticDedekindLandauPositiveComplexContinuation
    (D : NumberField.OddFundamentalDiscriminant)
    (X b : Real) (z : Complex) : Complex :=
  quadraticDedekindJShiftedComplexContinuation D z -
    quadraticDedekindJComplexMellinStartup D X z +
      Robin1984.nicolasLandauRpowComplexContinuation X b z

def quadraticDedekindLandauPositiveComplexMellin
    (D : NumberField.OddFundamentalDiscriminant)
    (X b : Real) (z : Complex) : Complex :=
  integral (volume.restrict (Ioi X)) (fun x : Real =>
    (x : Complex) ^ (z - 1) *
      (quadraticDedekindLandauPositiveTail D b x : Complex))

theorem quadraticDedekindJShiftedComplexContinuation_eq_mellin_of_re_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} (hz : z.re < 0) :
    quadraticDedekindJShiftedComplexContinuation D z =
      quadraticDedekindJMellin D z := by
  unfold quadraticDedekindJShiftedComplexContinuation
    quadraticDedekindJMellinShiftIntegrand
  exact (quadraticDedekindJMellin_eq_integral_shift D hz).symm

theorem quadraticDedekindJ_complexMellin_integrableOn_Ioi_three
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} (hz : z.re < 0) :
    IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) *
        (quadraticDedekindNicolasJ D x : Complex))
      (Ioi (3 : Real)) := by
  have hTriple := quadraticDedekindJMellinTriple_integrable D hz
  have hOuter := hTriple.integral_prod_left
  apply hOuter.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact quadraticDedekindJMellinTriple_inner_eq D hx.le

theorem quadraticDedekindJMellin_eq_startup_add_tail_of_re_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {X : Real} (hX : 3 <= X) {z : Complex} (hz : z.re < 0) :
    quadraticDedekindJMellin D z =
      quadraticDedekindJComplexMellinStartup D X z +
        integral (volume.restrict (Ioi X)) (fun x : Real =>
          (x : Complex) ^ (z - 1) *
            (quadraticDedekindNicolasJ D x : Complex)) := by
  have hJThree :=
    quadraticDedekindJ_complexMellin_integrableOn_Ioi_three D hz
  have hJX : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) *
        (quadraticDedekindNicolasJ D x : Complex)) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hJStartup : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) *
        (quadraticDedekindNicolasJ D x : Complex)) (Ioc 3 X) :=
    hJThree.mono_set Ioc_subset_Ioi_self
  unfold quadraticDedekindJMellin quadraticDedekindJComplexMellinStartup
  rw [<- Ioc_union_Ioi_eq_Ioi hX,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  next => exact hJStartup
  next => exact hJX

theorem quadraticDedekindLandauPositiveComplexMellin_eq_continuation_of_re_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    {z : Complex} (hz : z.re < 0) :
    quadraticDedekindLandauPositiveComplexMellin D X b z =
      quadraticDedekindLandauPositiveComplexContinuation D X b z := by
  have hJThree :=
    quadraticDedekindJ_complexMellin_integrableOn_Ioi_three D hz
  have hJX : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) *
        (quadraticDedekindNicolasJ D x : Complex)) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hzB : z.re < b := lt_trans hz hb
  have hRpow :=
    Robin1984.nicolasLandauRpowComplexTailMellin_integrableOn hXPos hzB
  have hDecomp : (fun x : Real =>
      (x : Complex) ^ (z - 1) *
        (quadraticDedekindLandauPositiveTail D b x : Complex)) =
      (fun x : Real =>
        (x : Complex) ^ (z - 1) *
          (quadraticDedekindNicolasJ D x : Complex)) +
      (fun x : Real =>
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) := by
    funext x
    unfold quadraticDedekindLandauPositiveTail
    push_cast
    simp only [Pi.add_apply]
    ring
  unfold quadraticDedekindLandauPositiveComplexMellin
    quadraticDedekindLandauPositiveComplexContinuation
  rw [hDecomp]
  change integral (volume.restrict (Ioi X)) (fun x : Real =>
      (x : Complex) ^ (z - 1) *
          (quadraticDedekindNicolasJ D x : Complex) +
        (x : Complex) ^ (z - 1) *
          ((x ^ (-b) : Real) : Complex)) = _
  rw [integral_add hJX hRpow]
  rw [Robin1984.nicolasLandauRpowComplexTailMellin_eq_continuation
    hXPos hzB]
  have hSplit :=
    quadraticDedekindJMellin_eq_startup_add_tail_of_re_neg D hX hz
  rw [<- quadraticDedekindJShiftedComplexContinuation_eq_mellin_of_re_neg
      D hz] at hSplit
  rw [hSplit]
  ring

theorem complexMGF_log_quadraticDedekindLandauPositiveMeasure_eq_complexMellin
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    {z : Complex} :
    complexMGF (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b) z =
      quadraticDedekindLandauPositiveComplexMellin D X b z := by
  have hDensity :=
    quadraticDedekindLandauPositiveDensity_aemeasurable
      D (X := X) (b := b) hX
  let measurableDensity : Real -> ENNReal :=
    hDensity.mk (quadraticDedekindLandauPositiveDensity D b)
  have hDensityEq : Filter.Eventually
      (fun x : Real => quadraticDedekindLandauPositiveDensity D b x =
        measurableDensity x)
      (ae (volume.restrict (Ioi X))) := hDensity.ae_eq_mk
  have hDensityTop : Filter.Eventually
      (fun x : Real => measurableDensity x < Top.top)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [hDensityEq] with x hx
    rw [<- hx]
    exact ENNReal.ofReal_lt_top
  have hMeasureEq :
      (volume.restrict (Ioi X)).withDensity
          (quadraticDedekindLandauPositiveDensity D b) =
        (volume.restrict (Ioi X)).withDensity measurableDensity :=
    withDensity_congr_ae hDensityEq
  unfold complexMGF quadraticDedekindLandauPositiveMeasure
  rw [hMeasureEq, integral_withDensity_eq_integral_toReal_smul
    hDensity.measurable_mk hDensityTop]
  unfold quadraticDedekindLandauPositiveComplexMellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hxNe : Not ((x : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hxPos.ne'
  have hTail : 0 <= quadraticDedekindLandauPositiveTail D b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      quadraticDedekindLandauPositiveTail D b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  have hExp : Complex.exp (z * (Real.log x : Complex)) =
      (x : Complex) ^ z := by
    rw [Complex.cpow_def_of_ne_zero hxNe, <- Complex.ofReal_log hxPos.le]
    congr 1
    ring
  change SMul.smul (measurableDensity x).toReal
      (Complex.exp (z * (Real.log x : Complex))) =
    (x : Complex) ^ (z - 1) *
      (quadraticDedekindLandauPositiveTail D b x : Complex)
  rw [<- hdx]
  unfold quadraticDedekindLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  change ((x ^ (-1 : Real) *
      quadraticDedekindLandauPositiveTail D b x : Real) : Complex) *
      Complex.exp (z * (Real.log x : Complex)) =
    (x : Complex) ^ (z - 1) *
      (quadraticDedekindLandauPositiveTail D b x : Complex)
  rw [hExp]
  push_cast
  calc
    ((x ^ (-1 : Real) : Real) : Complex) *
          (quadraticDedekindLandauPositiveTail D b x : Complex) *
          (x : Complex) ^ z =
        (((x ^ (-1 : Real) : Real) : Complex) *
          (x : Complex) ^ z) *
          (quadraticDedekindLandauPositiveTail D b x : Complex) := by ring
    _ = ((x : Complex) ^ ((-1 : Real) : Complex) *
          (x : Complex) ^ z) *
          (quadraticDedekindLandauPositiveTail D b x : Complex) := by
      rw [Complex.ofReal_cpow hxPos.le]
    _ = (x : Complex) ^ (((-1 : Real) : Complex) + z) *
          (quadraticDedekindLandauPositiveTail D b x : Complex) := by
      rw [Complex.cpow_add _ _ hxNe]
    _ = (x : Complex) ^ (z - 1) *
          (quadraticDedekindLandauPositiveTail D b x : Complex) := by
      congr 2
      norm_num [sub_eq_add_neg, add_comm]

theorem quadraticDedekindLandauComplexMGF_eq_continuation_of_re_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    {z : Complex} (hz : z.re < 0) :
    complexMGF (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b) z =
      quadraticDedekindLandauPositiveComplexContinuation D X b z := by
  rw [complexMGF_log_quadraticDedekindLandauPositiveMeasure_eq_complexMellin
    D hX hPos]
  exact quadraticDedekindLandauPositiveComplexMellin_eq_continuation_of_re_neg
    D hX hb hz

def quadraticDedekindZetaPoleFactor
    (D : NumberField.OddFundamentalDiscriminant)
    (s : Complex) : Complex :=
  Robin1984.nicolasZetaPoleFactor s * D.character.LFunction s

theorem quadraticDedekindZetaPoleFactor_differentiable
    (D : NumberField.OddFundamentalDiscriminant) :
    Differentiable Complex (quadraticDedekindZetaPoleFactor D) := by
  unfold quadraticDedekindZetaPoleFactor
  exact Robin1984.nicolasZetaPoleFactor_differentiable.mul
    (D.character.differentiable_LFunction (quadraticCharacter_ne_one D))

theorem quadraticDedekindZetaPoleFactor_one_ne_zero
    (D : NumberField.OddFundamentalDiscriminant) :
    Not (quadraticDedekindZetaPoleFactor D 1 = 0) := by
  unfold quadraticDedekindZetaPoleFactor
  apply mul_ne_zero
  next => simp
  next =>
    exact D.character.LFunction_ne_zero_of_one_le_re
      (Or.inl (quadraticCharacter_ne_one D)) (by norm_num)

theorem quadraticDedekindZetaContinuation_eq_poleFactor_div
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : Not (s = 1)) :
    quadraticDedekindZetaContinuation D s =
      quadraticDedekindZetaPoleFactor D s / (s - 1) := by
  unfold quadraticDedekindZetaContinuation
    quadraticDedekindZetaPoleFactor
  rw [Robin1984.riemannZeta_eq_nicolasZetaPoleFactor_div hs]
  ring

theorem logDeriv_quadraticDedekindZeta_eq_poleFactor_sub
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : Not (s = 1))
    (hZeta : Not (quadraticDedekindZetaContinuation D s = 0)) :
    logDeriv (quadraticDedekindZetaContinuation D) s =
      logDeriv (quadraticDedekindZetaPoleFactor D) s -
        1 / (s - 1) := by
  have hLocal : Filter.EventuallyEq (nhds s)
      (quadraticDedekindZetaContinuation D)
      (fun w : Complex => quadraticDedekindZetaPoleFactor D w / (w - 1)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    exact quadraticDedekindZetaContinuation_eq_poleFactor_div D
      (Set.mem_compl_singleton_iff.mp hw)
  have hLogAt :
      logDeriv (quadraticDedekindZetaContinuation D) s =
        logDeriv (fun w : Complex =>
          quadraticDedekindZetaPoleFactor D w / (w - 1)) s :=
    (logDeriv_congr_nhds hLocal).self_of_nhds
  have hFactor : Not (quadraticDedekindZetaPoleFactor D s = 0) := by
    intro hFactorZero
    have hIdentity :=
      quadraticDedekindZetaContinuation_eq_poleFactor_div D hs
    rw [hFactorZero, zero_div] at hIdentity
    exact hZeta hIdentity
  calc
    logDeriv (quadraticDedekindZetaContinuation D) s =
        logDeriv (fun w : Complex =>
          quadraticDedekindZetaPoleFactor D w / (w - 1)) s := hLogAt
    _ = logDeriv (quadraticDedekindZetaPoleFactor D) s -
        logDeriv (fun w : Complex => w - 1) s :=
      logDeriv_div s hFactor (sub_ne_zero.mpr hs)
        (quadraticDedekindZetaPoleFactor_differentiable D s) (by fun_prop)
    _ = logDeriv (quadraticDedekindZetaPoleFactor D) s -
        1 / (s - 1) := by
      congr 1
      simp [logDeriv_apply]

def quadraticDedekindPsiMellinContinuationFilled
    (D : NumberField.OddFundamentalDiscriminant)
    (s : Complex) : Complex :=
  -(logDeriv (quadraticDedekindZetaPoleFactor D) s + 1) / s

theorem quadraticDedekindPsiMellinContinuation_eq_filled
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hsZero : Not (s = 0)) (hsOne : Not (s = 1))
    (hZeta : Not (quadraticDedekindZetaContinuation D s = 0)) :
    quadraticDedekindPsiMellinContinuation D s =
      quadraticDedekindPsiMellinContinuationFilled D s := by
  unfold quadraticDedekindPsiMellinContinuation
    quadraticDedekindPsiMellinContinuationFilled
  have hLog :=
    logDeriv_quadraticDedekindZeta_eq_poleFactor_sub D hsOne hZeta
  rw [hLog]
  field_simp [hsZero, sub_ne_zero.mpr hsOne]
  ring

theorem quadraticDedekindPsiMellinContinuationFilled_analyticAt
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hsZero : Not (s = 0))
    (hFactor : Not (quadraticDedekindZetaPoleFactor D s = 0)) :
    AnalyticAt Complex (quadraticDedekindPsiMellinContinuationFilled D) s := by
  have hFactorAnalytic :
      AnalyticAt Complex (quadraticDedekindZetaPoleFactor D) s :=
    (quadraticDedekindZetaPoleFactor_differentiable D).analyticAt s
  have hDerivAnalytic : AnalyticAt Complex
      (deriv (quadraticDedekindZetaPoleFactor D)) s :=
    (quadraticDedekindZetaPoleFactor_differentiable D).deriv.analyticAt s
  have hLogDeriv : AnalyticAt Complex
      (logDeriv (quadraticDedekindZetaPoleFactor D)) s := by
    unfold logDeriv
    exact hDerivAnalytic.div hFactorAnalytic hFactor
  unfold quadraticDedekindPsiMellinContinuationFilled
  exact (hLogDeriv.add analyticAt_const).neg.div analyticAt_id hsZero

theorem quadraticDedekindPsiMellinContinuation_tendsto_one
    (D : NumberField.OddFundamentalDiscriminant) :
    Tendsto (quadraticDedekindPsiMellinContinuation D)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (quadraticDedekindPsiMellinContinuationFilled D 1)) := by
  have hFilledAnalytic :=
    quadraticDedekindPsiMellinContinuationFilled_analyticAt D
      (by norm_num) (quadraticDedekindZetaPoleFactor_one_ne_zero D)
  have hRegular :
      Tendsto (quadraticDedekindPsiMellinContinuationFilled D)
        (nhdsWithin 1 (Set.compl {(1 : Complex)}))
        (nhds (quadraticDedekindPsiMellinContinuationFilled D 1)) :=
    hFilledAnalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hLNe : Not (D.character.LFunction 1 = 0) :=
    D.character.LFunction_ne_zero_of_one_le_re
      (Or.inl (quadraticCharacter_ne_one D)) (by norm_num)
  have hLContinuous : ContinuousAt D.character.LFunction 1 :=
    (D.character.differentiable_LFunction
      (quadraticCharacter_ne_one D) 1).continuousAt
  have hZetaEventually : Filter.Eventually
      (fun s : Complex => Not (quadraticDedekindZetaContinuation D s = 0))
      (nhds (1 : Complex)) := by
    filter_upwards [riemannZeta_eventually_ne_zero_nhds_one,
      hLContinuous.eventually_ne hLNe] with s hRiemann hL
    unfold quadraticDedekindZetaContinuation
    exact mul_ne_zero hRiemann hL
  have hZeroNeighborhood :
      Membership.mem (nhds (1 : Complex)) (Set.compl {(0 : Complex)}) :=
    isOpen_compl_singleton.mem_nhds
      (Set.mem_compl_singleton_iff.mpr (by norm_num))
  apply hRegular.congr'
  filter_upwards
      [hZetaEventually.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds hZeroNeighborhood,
      self_mem_nhdsWithin] with s hZeta hsZeroMem hsOneMem
  have hsOne : Not (s = 1) :=
    Set.mem_compl_singleton_iff.mp hsOneMem
  have hsZero : Not (s = 0) :=
    Set.mem_compl_singleton_iff.mp hsZeroMem
  exact (quadraticDedekindPsiMellinContinuation_eq_filled
    D hsZero hsOne hZeta).symm

def quadraticDedekindPsiMellinTailContinuationFilled
    (D : NumberField.OddFundamentalDiscriminant)
    (s : Complex) : Complex :=
  quadraticDedekindPsiMellinContinuationFilled D s -
    quadraticDedekindPsiMellinStartup D 3 s

theorem quadraticDedekindPsiMellinTailContinuation_tendsto_one
    (D : NumberField.OddFundamentalDiscriminant) :
    Tendsto (quadraticDedekindPsiMellinTailContinuation D 3)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (quadraticDedekindPsiMellinTailContinuationFilled D 1)) := by
  have hStartup : Tendsto (quadraticDedekindPsiMellinStartup D 3)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (quadraticDedekindPsiMellinStartup D 3 1)) :=
    (quadraticDedekindPsiMellinStartup_three_continuousAt D 1).tendsto.mono_left
      nhdsWithin_le_nhds
  have hDifference :=
    (quadraticDedekindPsiMellinContinuation_tendsto_one D).sub hStartup
  change Tendsto
    (fun s : Complex =>
      quadraticDedekindPsiMellinContinuation D s -
        quadraticDedekindPsiMellinStartup D 3 s)
    (nhdsWithin 1 (Set.compl {(1 : Complex)}))
    (nhds (quadraticDedekindPsiMellinContinuationFilled D 1 -
      quadraticDedekindPsiMellinStartup D 3 1))
  exact hDifference

theorem quadraticDedekindPsiMellinTailContinuation_eq_filled
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hsZero : Not (s = 0)) (hsOne : Not (s = 1))
    (hZeta : Not (quadraticDedekindZetaContinuation D s = 0)) :
    quadraticDedekindPsiMellinTailContinuation D 3 s =
      quadraticDedekindPsiMellinTailContinuationFilled D s := by
  unfold quadraticDedekindPsiMellinTailContinuation
    quadraticDedekindPsiMellinTailContinuationFilled
  rw [quadraticDedekindPsiMellinContinuation_eq_filled
    D hsZero hsOne hZeta]

theorem quadraticDedekindPsiMellinStartup_three_differentiableAt
    (D : NumberField.OddFundamentalDiscriminant)
    (s0 : Complex) :
    DifferentiableAt Complex (quadraticDedekindPsiMellinStartup D 3) s0 := by
  letI : AddCommGroup Complex := Complex.addCommGroup
  letI : Module Complex Complex := Semiring.toModule
  let F : Complex -> Real -> Complex := fun s t =>
    (quadraticDedekindPsiError D t : Complex) *
      (t : Complex) ^ (-(s + 1))
  let F' : Complex -> Real -> Complex := fun s t =>
    -((Real.log t : Real) : Complex) * F s t
  let base : Real -> Complex := fun t =>
    (quadraticDedekindPsiError D t : Complex) *
      (t : Complex) ^ (-3 : Complex)
  let ratio : Complex -> Real -> Complex := fun s t =>
    (t : Complex) ^ ((2 : Complex) - s)
  let majorant : Real -> Real := fun t =>
    norm (base t) * (3 : Real) ^ (abs s0.re + 4)
  have hBaseIntegrable : Integrable base
      (volume.restrict (Ioc (1 : Real) 3)) := by
    dsimp [base]
    change IntegrableOn
      (fun t : Real => (quadraticDedekindPsiError D t : Complex) *
        (t : Complex) ^ (-3 : Complex)) (Ioc (1 : Real) 3)
    have h :=
      (quadraticDedekindPsiErrorMellin_integrable
        D (s := (2 : Complex)) (by norm_num)).mono_set
        (show Ioc (1 : Real) 3 <= Ioi 1 from Ioc_subset_Ioi_self)
    apply h.congr_fun
    next =>
      intro t ht
      congr 2
      norm_num
    next => exact measurableSet_Ioc
  have hMajorantIntegrable : Integrable majorant
      (volume.restrict (Ioc (1 : Real) 3)) := by
    have h := hBaseIntegrable.norm.const_mul
      ((3 : Real) ^ (abs s0.re + 4))
    simpa [majorant, mul_comm] using h
  have hMeasurable : forall s : Complex, AEStronglyMeasurable (F s)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    intro s
    have hRatioContinuous : ContinuousOn (ratio s) (Ioc (1 : Real) 3) := by
      apply continuousOn_of_forall_continuousAt
      intro t ht
      dsimp [ratio]
      have htPos : 0 < t := lt_trans zero_lt_one ht.1
      exact (continuousAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 htPos)).comp
          Complex.continuous_ofReal.continuousAt
    have hProduct := hBaseIntegrable.aestronglyMeasurable.mul
      (hRatioContinuous.aestronglyMeasurable measurableSet_Ioc)
    apply hProduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_trans zero_lt_one ht.1))
    dsimp [F, base, ratio]
    rw [mul_assoc, <- Complex.cpow_add _ _ htZero]
    congr 2
    ring
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall t : Real, 1 < t -> t <= 3 ->
        norm (F s t) <= majorant t := by
    intro s hs t htOneStrict htThree
    have hDist : norm (s - s0) < 1 := by
      simpa [dist_eq_norm] using hs
    have hReAbs : abs (s.re - s0.re) <= norm (s - s0) := by
      simpa using Complex.abs_re_le_norm (s - s0)
    have hReLower : s0.re - 1 < s.re := by
      have hAbsLt : abs (s.re - s0.re) < 1 :=
        lt_of_le_of_lt hReAbs hDist
      linarith [(abs_lt.mp hAbsLt).1]
    have htPos : 0 < t := lt_trans zero_lt_one htOneStrict
    have htOne : 1 <= t := le_of_lt htOneStrict
    have hExponent : 2 - s.re <= abs s0.re + 4 := by
      have hNeg : -s0.re <= abs s0.re := neg_le_abs s0.re
      linarith
    have hExponentNonneg : 0 <= abs s0.re + 4 := by positivity
    have hRatioBound : norm (ratio s t) <=
        (3 : Real) ^ (abs s0.re + 4) := by
      dsimp [ratio]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htPos]
      calc
        t ^ (2 - s.re) <= t ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow_of_exponent_le htOne hExponent
        _ <= (3 : Real) ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow (le_of_lt htPos) htThree hExponentNonneg
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt htPos)
    dsimp [F]
    rw [show -(s + 1) = (-3 : Complex) + ((2 : Complex) - s) by ring,
      Complex.cpow_add _ _ htZero, norm_mul]
    dsimp [majorant, base]
    simp only [norm_mul]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hRatioBound
        (mul_nonneg
          (norm_nonneg ((quadraticDedekindPsiError D t : Complex)))
          (norm_nonneg ((t : Complex) ^ (-3 : Complex)))))
  have hFIntegrable : Integrable (F s0)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    apply Integrable.mono hMajorantIntegrable (hMeasurable s0)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hMajorantNonneg : 0 <= majorant t := by
      dsimp [majorant]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hMajorantNonneg]
    exact hBound s0 (by simp [dist_self]) t ht.1 ht.2
  have hDerivativeMeasurable : AEStronglyMeasurable (F' s0)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    have hRealLogOn : ContinuousOn (fun t : Real => Real.log t)
        (Ioc (1 : Real) 3) := by
      apply Real.continuousOn_log.mono
      intro t ht
      exact Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (lt_trans zero_lt_one ht.1))
    have hRealLog : AEStronglyMeasurable (fun t : Real => Real.log t)
        (volume.restrict (Ioc (1 : Real) 3)) :=
      hRealLogOn.aestronglyMeasurable measurableSet_Ioc
    have hLog : AEStronglyMeasurable
        (fun t : Real => ((Real.log t : Real) : Complex))
        (volume.restrict (Ioc (1 : Real) 3)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hRealLog
    exact hLog.neg.mul (hMeasurable s0)
  have hDerivativeBound : Filter.Eventually
      (fun t : Real => forall s : Complex,
        Membership.mem (Metric.ball s0 1) s ->
          norm (F' s t) <= 3 * majorant t)
      (ae (volume.restrict (Ioc (1 : Real) 3))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    have htPos : 0 < t := lt_trans zero_lt_one ht.1
    have hLogNonneg : 0 <= Real.log t := Real.log_nonneg ht.1.le
    have hLogBound : Real.log t <= 3 := by
      have hLogSub := Real.log_le_sub_one_of_pos htPos
      linarith [ht.2]
    have hFBound : norm (F s t) <= majorant t :=
      hBound s (by simpa [Metric.mem_ball] using hs) t ht.1 ht.2
    dsimp [F']
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hLogNonneg]
    exact mul_le_mul hLogBound hFBound (norm_nonneg _) (by norm_num)
  have hDerivativeIntegrable : Integrable
      (fun t : Real => 3 * majorant t)
      (volume.restrict (Ioc (1 : Real) 3)) :=
    hMajorantIntegrable.const_mul 3
  have hDerivative : Filter.Eventually
      (fun t : Real => forall s : Complex,
        Membership.mem (Metric.ball s0 1) s ->
          HasDerivAt (fun z : Complex => F z t) (F' s t) s)
      (ae (volume.restrict (Ioc (1 : Real) 3))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    have htPos : 0 < t := lt_trans zero_lt_one ht.1
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt htPos)
    have hExponent : HasDerivAt (fun z : Complex => -(z + 1)) (-1) s := by
      have hRaw := ((hasDerivAt_id' s).add_const 1).neg
      exact hRaw.congr_of_eventuallyEq
        (Eventually.of_forall (fun _ => rfl))
    have hPower := hExponent.const_cpow (Or.inl htZero)
    have hProduct :=
      hPower.const_smul (quadraticDedekindPsiError D t : Complex)
    have hProduct' : HasDerivAt
        (fun z : Complex => (quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-(z + 1)))
        ((quadraticDedekindPsiError D t : Complex) *
          ((t : Complex) ^ (-(s + 1)) *
            Complex.log (t : Complex) * -1)) s := by
      convert hProduct using 1 <;> try rfl
    dsimp [F, F']
    apply hProduct'.congr_deriv
    rw [Complex.ofReal_log htPos.le]
    ring
  unfold quadraticDedekindPsiMellinStartup
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s0 zero_lt_one)
    (Eventually.of_forall hMeasurable) hFIntegrable
    hDerivativeMeasurable hDerivativeBound hDerivativeIntegrable hDerivative
  exact hMain.2.differentiableAt

theorem quadraticDedekindPsiMellinStartup_three_differentiable
    (D : NumberField.OddFundamentalDiscriminant) :
    Differentiable Complex (quadraticDedekindPsiMellinStartup D 3) :=
  quadraticDedekindPsiMellinStartup_three_differentiableAt D

theorem quadraticDedekindPsiMellinStartup_three_analyticAt
    (D : NumberField.OddFundamentalDiscriminant)
    (s0 : Complex) :
    AnalyticAt Complex (quadraticDedekindPsiMellinStartup D 3) s0 :=
  (quadraticDedekindPsiMellinStartup_three_differentiable D).analyticAt s0

theorem quadraticDedekindPsiMellinTailContinuationFilled_analyticAt
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hsZero : Not (s = 0))
    (hFactor : Not (quadraticDedekindZetaPoleFactor D s = 0)) :
    AnalyticAt Complex
      (quadraticDedekindPsiMellinTailContinuationFilled D) s := by
  unfold quadraticDedekindPsiMellinTailContinuationFilled
  exact
    (quadraticDedekindPsiMellinContinuationFilled_analyticAt
      D hsZero hFactor).sub
        (quadraticDedekindPsiMellinStartup_three_analyticAt D s)

def quadraticDedekindJShiftNumeratorFilled
    (D : NumberField.OddFundamentalDiscriminant)
    (z : Complex) (u : Real) : Complex :=
  quadraticDedekindPsiMellinTailContinuationFilled D
      (((u + 1 : Real) : Complex) - z) -
    (3 : Complex) ^ z *
      quadraticDedekindPsiMellinTailContinuationFilled D
        ((u + 1 : Real) : Complex)

theorem quadraticDedekindJShiftNumeratorFilled_zero
    (D : NumberField.OddFundamentalDiscriminant) (u : Real) :
    quadraticDedekindJShiftNumeratorFilled D 0 u = 0 := by
  unfold quadraticDedekindJShiftNumeratorFilled
  simp

def quadraticDedekindJMellinShiftIntegrandFilled
    (D : NumberField.OddFundamentalDiscriminant)
    (z : Complex) (u : Real) : Complex :=
  ((u + 1 : Real) : Complex) *
    dslope (fun w : Complex => quadraticDedekindJShiftNumeratorFilled D w u)
      0 z

def quadraticDedekindJShiftedComplexContinuationFilled
    (D : NumberField.OddFundamentalDiscriminant)
    (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (0 : Real)))
    (quadraticDedekindJMellinShiftIntegrandFilled D z)

def quadraticDedekindLandauPositiveComplexContinuationFilled
    (D : NumberField.OddFundamentalDiscriminant)
    (X b : Real) (z : Complex) : Complex :=
  quadraticDedekindJShiftedComplexContinuationFilled D z -
    quadraticDedekindJComplexMellinStartup D X z +
      Robin1984.nicolasLandauRpowComplexContinuation X b z

theorem quadraticDedekindJMellinShiftIntegrandFilled_eq_raw_of_re_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} (hz : z.re < 0)
    {u : Real} (hu : 0 < u) :
    quadraticDedekindJMellinShiftIntegrandFilled D z u =
      quadraticDedekindJMellinShiftIntegrand D z u := by
  let s1 : Complex := ((u + 1 : Real) : Complex) - z
  let s2 : Complex := ((u + 1 : Real) : Complex)
  have hs1 : 1 < s1.re := by
    dsimp [s1]
    linarith
  have hs2 : 1 < s2.re := by
    dsimp [s2]
    linarith
  have hs1Zero : Not (s1 = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.zero_re] at hRe
    linarith
  have hs2Zero : Not (s2 = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.zero_re] at hRe
    linarith
  have hs1One : Not (s1 = 1) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.one_re] at hRe
    linarith
  have hs2One : Not (s2 = 1) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.one_re] at hRe
    linarith
  have hZeta1 : Not (quadraticDedekindZetaContinuation D s1 = 0) := by
    unfold quadraticDedekindZetaContinuation
    exact mul_ne_zero
      (riemannZeta_ne_zero_of_one_le_re hs1.le)
      (D.character.LFunction_ne_zero_of_one_le_re
        (Or.inl (quadraticCharacter_ne_one D)) hs1.le)
  have hZeta2 : Not (quadraticDedekindZetaContinuation D s2 = 0) := by
    unfold quadraticDedekindZetaContinuation
    exact mul_ne_zero
      (riemannZeta_ne_zero_of_one_le_re hs2.le)
      (D.character.LFunction_ne_zero_of_one_le_re
        (Or.inl (quadraticCharacter_ne_one D)) hs2.le)
  have hOne :=
    quadraticDedekindPsiMellinTailContinuation_eq_filled
      D hs1Zero hs1One hZeta1
  have hTwo :=
    quadraticDedekindPsiMellinTailContinuation_eq_filled
      D hs2Zero hs2One hZeta2
  have hzZero : Not (z = 0) := by
    intro hEq
    subst z
    norm_num at hz
  unfold quadraticDedekindJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzZero]
  unfold slope
  change ((u + 1 : Real) : Complex) *
      (Inv.inv (z - 0) *
        (quadraticDedekindJShiftNumeratorFilled D z u -
          quadraticDedekindJShiftNumeratorFilled D 0 u)) =
    quadraticDedekindJMellinShiftIntegrand D z u
  rw [quadraticDedekindJShiftNumeratorFilled_zero]
  simp only [smul_eq_mul, vsub_eq_sub, sub_zero, inv_mul_eq_div]
  unfold quadraticDedekindJShiftNumeratorFilled
    quadraticDedekindJMellinShiftIntegrand
  change ((u + 1 : Real) : Complex) *
      ((quadraticDedekindPsiMellinTailContinuationFilled D s1 -
        (3 : Complex) ^ z *
          quadraticDedekindPsiMellinTailContinuationFilled D s2) / z) =
    ((u + 1 : Real) : Complex) *
      ((quadraticDedekindPsiMellinTailContinuation D 3 s1 -
        (3 : Complex) ^ z *
          quadraticDedekindPsiMellinTailContinuation D 3 s2) / z)
  rw [<- hOne, <- hTwo]

theorem quadraticDedekindJShiftedComplexContinuationFilled_eq_mellin_of_re_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} (hz : z.re < 0) :
    quadraticDedekindJShiftedComplexContinuationFilled D z =
      quadraticDedekindJMellin D z := by
  unfold quadraticDedekindJShiftedComplexContinuationFilled
  calc
    integral (volume.restrict (Ioi (0 : Real)))
        (quadraticDedekindJMellinShiftIntegrandFilled D z) =
      integral (volume.restrict (Ioi (0 : Real)))
        (quadraticDedekindJMellinShiftIntegrand D z) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact
        quadraticDedekindJMellinShiftIntegrandFilled_eq_raw_of_re_neg
          D hz hu
    _ = quadraticDedekindJMellin D z :=
      quadraticDedekindJShiftedComplexContinuation_eq_mellin_of_re_neg D hz

theorem quadraticDedekindLandauComplexMGF_eq_continuationFilled_of_re_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    {z : Complex} (hz : z.re < 0) :
    complexMGF (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b) z =
      quadraticDedekindLandauPositiveComplexContinuationFilled D X b z := by
  rw [complexMGF_log_quadraticDedekindLandauPositiveMeasure_eq_complexMellin
    D hX hPos]
  have hSplit :=
    quadraticDedekindJMellin_eq_startup_add_tail_of_re_neg D hX hz
  rw [<- quadraticDedekindJShiftedComplexContinuationFilled_eq_mellin_of_re_neg
      D hz] at hSplit
  unfold quadraticDedekindLandauPositiveComplexMellin
    quadraticDedekindLandauPositiveComplexContinuationFilled
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hzB : z.re < b := lt_trans hz hb
  have hJThree :=
    quadraticDedekindJ_complexMellin_integrableOn_Ioi_three D hz
  have hJX : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) *
        (quadraticDedekindNicolasJ D x : Complex)) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hRpow :=
    Robin1984.nicolasLandauRpowComplexTailMellin_integrableOn hXPos hzB
  have hDecomp : (fun x : Real =>
      (x : Complex) ^ (z - 1) *
        (quadraticDedekindLandauPositiveTail D b x : Complex)) =
      (fun x : Real =>
        (x : Complex) ^ (z - 1) *
          (quadraticDedekindNicolasJ D x : Complex)) +
      (fun x : Real =>
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) := by
    funext x
    unfold quadraticDedekindLandauPositiveTail
    push_cast
    simp only [Pi.add_apply]
    ring
  rw [hDecomp]
  change integral (volume.restrict (Ioi X)) (fun x : Real =>
      (x : Complex) ^ (z - 1) *
          (quadraticDedekindNicolasJ D x : Complex) +
        (x : Complex) ^ (z - 1) *
          ((x ^ (-b) : Real) : Complex)) = _
  rw [integral_add hJX hRpow]
  rw [Robin1984.nicolasLandauRpowComplexTailMellin_eq_continuation
    hXPos hzB]
  rw [hSplit]
  ring

end

end RobinBV.NumberField
