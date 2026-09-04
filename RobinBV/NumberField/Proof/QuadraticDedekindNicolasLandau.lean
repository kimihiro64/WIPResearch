import Robin1984.NicolasLandau.NicolasLandauPositiveTail
import Robin1984.NicolasLandau.NicolasOscillation
import RobinBV.NumberField.Proof.QuadraticCharacterEndpoint
import RobinBV.NumberField.Proof.QuadraticDedekindMellinTailPole
import RobinBV.NumberField.Proof.QuadraticRationalEndpoint

/-!
# Quadratic Dedekind Nicolas-Landau base

This module proves endpoint integrability and measurability for the quadratic
Dedekind Nicolas tail, constructs its positive Landau measure, identifies
the moment-generating function with the Mellin transform, and establishes
the complete negative half-line of exponential moments.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

theorem integrableOn_quadraticDedekindNicolasKernel_three
    (D : NumberField.OddFundamentalDiscriminant) :
    IntegrableOn (fun t : Real =>
      quadraticDedekindPsiError D t *
        quadraticDedekindNicolasTailKernel t) (Ioi 3) := by
  have hRational :=
    integrableOn_quadraticRationalWeightedError_one
      (x := (3 : Real)) (by norm_num)
  have hCharacter :=
    integrableOn_quadraticCharacterChebyshevStep_mul_weight_one D
  have hSum := hRational.add hCharacter
  apply hSum.congr_fun
  next =>
    intro t ht
    have htOne : 1 < t := lt_trans (by norm_num : (1 : Real) < 3) ht
    change
      (Chebyshev.psi t - t) * Robin1984.robinRealWeight 1 t +
          quadraticCharacterChebyshevStep D t *
            Robin1984.robinRealWeight 1 t =
        quadraticDedekindPsiError D t *
          quadraticDedekindNicolasTailKernel t
    rw [quadraticDedekindPsiError_eq,
      quadraticDedekindChebyshevStep_eq,
      <- quadraticDedekindRealWeight_one_eq_nicolasTailKernel htOne]
    ring
  next => exact measurableSet_Ioi

theorem quadraticDedekindNicolasJ_aemeasurable_restrict_Ioi
    (D : NumberField.OddFundamentalDiscriminant)
    {X : Real} (hX : 3 <= X) :
    AEMeasurable (quadraticDedekindNicolasJ D)
      (volume.restrict (Ioi X)) := by
  let q : Real -> Real := fun t : Real =>
    quadraticDedekindPsiError D t *
      quadraticDedekindNicolasTailKernel t
  have hq : IntegrableOn q (Ioi (3 : Real)) := by
    simpa [q] using integrableOn_quadraticDedekindNicolasKernel_three D
  let q0 : Real -> Real := (Ioi (3 : Real)).indicator q
  have hq0 : Integrable q0 volume := by
    dsimp [q0]
    exact hq.integrable_indicator measurableSet_Ioi
  let tailPrimitive : Real -> Real := fun x : Real =>
    integral (volume.restrict (Ioi (3 : Real))) q -
      intervalIntegral q0 3 x volume
  have hContinuous : Continuous tailPrimitive := by
    dsimp [tailPrimitive]
    exact continuous_const.sub (hq0.continuous_primitive 3)
  have hEq : Filter.Eventually
      (fun x : Real => quadraticDedekindNicolasJ D x = tailPrimitive x)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxThree : 3 <= x := hX.trans hx.le
    have hqx : IntegrableOn q (Ioi x) :=
      hq.mono_set (Ioi_subset_Ioi hxThree)
    have hSplit := intervalIntegral.integral_interval_add_Ioi hq hqx
    have hInterval : intervalIntegral q0 3 x volume =
        intervalIntegral q 3 x volume := by
      apply intervalIntegral.integral_congr_Ioo_of_le hxThree
      intro t ht
      simpa [q, ht.1]
    unfold quadraticDedekindNicolasJ
    dsimp [tailPrimitive, q]
    rw [hInterval]
    linarith
  have hEqSymm : Filter.Eventually
      (fun x : Real => tailPrimitive x = quadraticDedekindNicolasJ D x)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [hEq] with x hx
    exact hx.symm
  exact hContinuous.aemeasurable.congr hEqSymm

theorem quadraticDedekindNicolasJ_realMellin_integrableOn_Ioi_three
    (D : NumberField.OddFundamentalDiscriminant)
    {a : Real} (ha : a < 0) :
    IntegrableOn (fun x : Real =>
      x ^ (a - 1) * quadraticDedekindNicolasJ D x) (Ioi 3) := by
  let q : Real -> Real := fun t : Real =>
    quadraticDedekindPsiError D t *
      quadraticDedekindNicolasTailKernel t
  have hq : IntegrableOn q (Ioi (3 : Real)) := by
    simpa [q] using integrableOn_quadraticDedekindNicolasKernel_three D
  let C : Real := integral (volume.restrict (Ioi (3 : Real)))
    (fun t : Real => norm (q t))
  have hCNonneg : 0 <= C := by
    dsimp [C]
    exact integral_nonneg (fun _ => abs_nonneg _)
  have hJBound : forall x : Real, 3 <= x ->
      norm (quadraticDedekindNicolasJ D x) <= C := by
    intro x hx
    have hSubset : Ioi x <= Ioi (3 : Real) := Ioi_subset_Ioi hx
    have hMono :
        integral (volume.restrict (Ioi x)) (fun t : Real => norm (q t)) <=
          integral (volume.restrict (Ioi (3 : Real)))
            (fun t : Real => norm (q t)) := by
      apply MeasureTheory.setIntegral_mono_set hq.norm
      next => exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
      next =>
        exact Filter.Eventually.of_forall (fun t ht => hSubset ht)
    unfold quadraticDedekindNicolasJ
    dsimp [C, q]
    exact (MeasureTheory.norm_integral_le_integral_norm _).trans hMono
  have hPower : IntegrableOn (fun x : Real => x ^ (a - 1)) (Ioi 3) := by
    rw [integrableOn_Ioi_rpow_iff (by norm_num : (0 : Real) < 3)]
    linarith
  have hMajor : IntegrableOn
      (fun x : Real => C * x ^ (a - 1)) (Ioi 3) :=
    hPower.const_mul C
  apply hMajor.mono'
  next =>
    have hPowerMeasurable : AEMeasurable (fun x : Real => x ^ (a - 1))
        (volume.restrict (Ioi 3)) :=
      measurable_id.aemeasurable.pow aemeasurable_const
    exact hPowerMeasurable.mul
      (quadraticDedekindNicolasJ_aemeasurable_restrict_Ioi D le_rfl)
      |>.aestronglyMeasurable
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num : (0 : Real) < 3) hx
    have hPowerPos : 0 < x ^ (a - 1) := Real.rpow_pos_of_pos hxPos _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hPowerPos]
    calc
      x ^ (a - 1) * abs (quadraticDedekindNicolasJ D x) =
          x ^ (a - 1) * norm (quadraticDedekindNicolasJ D x) := by
            rw [Real.norm_eq_abs]
      _ <= x ^ (a - 1) * C :=
        mul_le_mul_of_nonneg_left (hJBound x hx.le) hPowerPos.le
      _ = C * x ^ (a - 1) := by ring

def quadraticDedekindLandauPositiveTail
    (D : NumberField.OddFundamentalDiscriminant)
    (b x : Real) : Real :=
  quadraticDedekindNicolasJ D x + x ^ (-b)

def quadraticDedekindLandauPositiveDensity
    (D : NumberField.OddFundamentalDiscriminant)
    (b x : Real) : ENNReal :=
  ENNReal.ofReal
    (x ^ (-1 : Real) * quadraticDedekindLandauPositiveTail D b x)

def quadraticDedekindLandauPositiveMeasure
    (D : NumberField.OddFundamentalDiscriminant)
    (X b : Real) : Measure Real :=
  (volume.restrict (Ioi X)).withDensity
    (quadraticDedekindLandauPositiveDensity D b)

def quadraticDedekindLandauPositiveMellin
    (D : NumberField.OddFundamentalDiscriminant)
    (X b a : Real) : Real :=
  integral (volume.restrict (Ioi X)) (fun x : Real =>
    x ^ (a - 1) * quadraticDedekindLandauPositiveTail D b x)

theorem eventually_quadraticDedekindNicolasJ_add_rpow_pos_of_not_omegaMinus
    (D : NumberField.OddFundamentalDiscriminant)
    {b : Real}
    (hNot : Not (Robin1984.AtTopOmegaMinus
      (quadraticDedekindNicolasJ D) (fun x : Real => x ^ (-b)))) :
    Filter.Eventually
      (fun x : Real => 0 < quadraticDedekindLandauPositiveTail D b x)
      atTop := by
  unfold Robin1984.AtTopOmegaMinus Asymptotics.AtTopOmegaMinus at hNot
  unfold Asymptotics.AtTopOmegaPlus at hNot
  push Not at hNot
  specialize hNot 1 zero_lt_one
  choose X hX using hNot
  filter_upwards [eventually_ge_atTop X] with x hx
  have hStrict := hX x hx
  unfold quadraticDedekindLandauPositiveTail
  linarith

theorem exists_quadraticDedekindLandauPositiveTail_start
    (D : NumberField.OddFundamentalDiscriminant)
    {b : Real}
    (hNot : Not (Robin1984.AtTopOmegaMinus
      (quadraticDedekindNicolasJ D) (fun x : Real => x ^ (-b)))) :
    Exists fun X : Real => And (3 <= X)
      (forall x : Real, X < x ->
        0 <= quadraticDedekindLandauPositiveTail D b x) := by
  have hEventually :=
    eventually_quadraticDedekindNicolasJ_add_rpow_pos_of_not_omegaMinus
      D hNot
  choose X hX using eventually_atTop.1 hEventually
  refine Exists.intro (max 3 X) (And.intro (le_max_left 3 X) ?_)
  intro x hx
  exact (hX x ((le_max_right 3 X).trans hx.le)).le

theorem quadraticDedekindLandauPositiveDensity_aemeasurable
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X) :
    AEMeasurable (quadraticDedekindLandauPositiveDensity D b)
      (volume.restrict (Ioi X)) := by
  have hJ := quadraticDedekindNicolasJ_aemeasurable_restrict_Ioi D hX
  have hInv : AEMeasurable (fun x : Real => x ^ (-1 : Real))
      (volume.restrict (Ioi X)) :=
    measurable_id.aemeasurable.pow aemeasurable_const
  have hPower : AEMeasurable (fun x : Real => x ^ (-b))
      (volume.restrict (Ioi X)) :=
    measurable_id.aemeasurable.pow aemeasurable_const
  change AEMeasurable (fun x : Real =>
    ENNReal.ofReal (x ^ (-1 : Real) *
      (quadraticDedekindNicolasJ D x + x ^ (-b))))
      (volume.restrict (Ioi X))
  exact (hInv.mul (hJ.add hPower)).ennreal_ofReal

theorem ae_log_nonneg_quadraticDedekindLandauPositiveMeasure
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X) :
    Filter.Eventually (fun x : Real => 0 <= Real.log x)
      (ae (quadraticDedekindLandauPositiveMeasure D X b)) := by
  have hBase : Filter.Eventually (fun x : Real => 0 <= Real.log x)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.log_nonneg (le_trans (by norm_num) (hX.trans hx.le))
  exact (withDensity_absolutelyContinuous
    (volume.restrict (Ioi X))
    (quadraticDedekindLandauPositiveDensity D b)).ae_le hBase

theorem mgf_log_quadraticDedekindLandauPositiveMeasure_eq_mellin
    (D : NumberField.OddFundamentalDiscriminant)
    {X b a : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x) :
    mgf (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b) a =
      quadraticDedekindLandauPositiveMellin D X b a := by
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
  unfold mgf quadraticDedekindLandauPositiveMeasure
  rw [hMeasureEq, integral_withDensity_eq_integral_toReal_smul
    hDensity.measurable_mk hDensityTop]
  unfold quadraticDedekindLandauPositiveMellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hTail : 0 <= quadraticDedekindLandauPositiveTail D b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      quadraticDedekindLandauPositiveTail D b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  change (measurableDensity x).toReal * Real.exp (a * Real.log x) =
    x ^ (a - 1) * quadraticDedekindLandauPositiveTail D b x
  rw [<- hdx]
  unfold quadraticDedekindLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  rw [Real.rpow_def_of_pos hxPos, Real.rpow_def_of_pos hxPos]
  calc
    Real.exp (Real.log x * -1) *
        quadraticDedekindLandauPositiveTail D b x *
        Real.exp (a * Real.log x) =
        (Real.exp (Real.log x * -1) *
          Real.exp (a * Real.log x)) *
            quadraticDedekindLandauPositiveTail D b x := by ring
    _ = Real.exp (Real.log x * -1 + a * Real.log x) *
        quadraticDedekindLandauPositiveTail D b x := by rw [Real.exp_add]
    _ = Real.exp (Real.log x * (a - 1)) *
        quadraticDedekindLandauPositiveTail D b x := by
      congr 2
      ring

theorem mem_integrableExpSet_log_quadraticDedekindLandau_iff
    (D : NumberField.OddFundamentalDiscriminant)
    {X b a : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x) :
    Membership.mem
        (integrableExpSet (fun x : Real => Real.log x)
          (quadraticDedekindLandauPositiveMeasure D X b)) a <->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * quadraticDedekindLandauPositiveTail D b x)
        (Ioi X) := by
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
  change Integrable (fun x : Real => Real.exp (a * Real.log x))
      (quadraticDedekindLandauPositiveMeasure D X b) <->
    Integrable (fun x : Real =>
      x ^ (a - 1) * quadraticDedekindLandauPositiveTail D b x)
      (volume.restrict (Ioi X))
  unfold quadraticDedekindLandauPositiveMeasure
  rw [hMeasureEq, integrable_withDensity_iff
    hDensity.measurable_mk hDensityTop]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hTail : 0 <= quadraticDedekindLandauPositiveTail D b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      quadraticDedekindLandauPositiveTail D b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  change Real.exp (a * Real.log x) * (measurableDensity x).toReal =
    x ^ (a - 1) * quadraticDedekindLandauPositiveTail D b x
  rw [<- hdx]
  unfold quadraticDedekindLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  rw [Real.rpow_def_of_pos hxPos, Real.rpow_def_of_pos hxPos]
  calc
    Real.exp (a * Real.log x) *
        (Real.exp (Real.log x * -1) *
          quadraticDedekindLandauPositiveTail D b x) =
        (Real.exp (a * Real.log x) *
          Real.exp (Real.log x * -1)) *
            quadraticDedekindLandauPositiveTail D b x := by ring
    _ = Real.exp (a * Real.log x + Real.log x * -1) *
        quadraticDedekindLandauPositiveTail D b x := by rw [Real.exp_add]
    _ = Real.exp (Real.log x * (a - 1)) *
        quadraticDedekindLandauPositiveTail D b x := by
      congr 2
      ring

theorem quadraticDedekindLandauPositiveTail_integrableOn_of_neg
    (D : NumberField.OddFundamentalDiscriminant)
    {X b a : Real} (hX : 3 <= X) (hb : 0 < b) (ha : a < 0) :
    IntegrableOn (fun x : Real =>
      x ^ (a - 1) * quadraticDedekindLandauPositiveTail D b x)
      (Ioi X) := by
  have hJ : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * quadraticDedekindNicolasJ D x) (Ioi X) :=
    (quadraticDedekindNicolasJ_realMellin_integrableOn_Ioi_three D ha).mono_set
      (Ioi_subset_Ioi hX)
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hPowerBase : IntegrableOn (fun x : Real =>
      x ^ (a - b - 1)) (Ioi X) := by
    rw [integrableOn_Ioi_rpow_iff hXPos]
    linarith
  have hRpow : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * x ^ (-b)) (Ioi X) := by
    apply hPowerBase.congr_fun
    next =>
      intro x hx
      have hxPos : 0 < x := hXPos.trans hx
      change x ^ (a - b - 1) = x ^ (a - 1) * x ^ (-b)
      rw [<- Real.rpow_add hxPos]
      congr 1
      ring
    next => exact measurableSet_Ioi
  apply (hJ.add hRpow).congr_fun
  next =>
    intro x hx
    unfold quadraticDedekindLandauPositiveTail
    change x ^ (a - 1) * quadraticDedekindNicolasJ D x +
        x ^ (a - 1) * x ^ (-b) =
      x ^ (a - 1) *
        (quadraticDedekindNicolasJ D x + x ^ (-b))
    ring
  next => exact measurableSet_Ioi

theorem interior_integrableExpSet_log_quadraticDedekindLandau_of_below
    (D : NumberField.OddFundamentalDiscriminant)
    {X b sigma : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x)
    (hBelow : forall a : Real, a < sigma ->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * quadraticDedekindLandauPositiveTail D b x)
        (Ioi X)) :
    forall a : Real, a < sigma ->
      Membership.mem
        (interior (integrableExpSet (fun x : Real => Real.log x)
          (quadraticDedekindLandauPositiveMeasure D X b))) a := by
  intro a ha
  rw [mem_interior_iff_mem_nhds]
  let eps : Real := (sigma - a) / 2
  have hEps : 0 < eps := by
    dsimp [eps]
    linarith
  apply mem_of_superset (Metric.ball_mem_nhds a hEps)
  intro y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hySigma : y < sigma := by
    have hAbs := (abs_lt.mp hy).2
    dsimp [eps] at hAbs
    linarith
  exact
    (mem_integrableExpSet_log_quadraticDedekindLandau_iff
      D hX hPos).2 (hBelow y hySigma)

theorem Iio_zero_subset_interior_integrableExpSet_quadraticDedekindLandau
    (D : NumberField.OddFundamentalDiscriminant)
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x ->
      0 <= quadraticDedekindLandauPositiveTail D b x) :
    Iio (0 : Real) <=
      interior (integrableExpSet (fun x : Real => Real.log x)
        (quadraticDedekindLandauPositiveMeasure D X b)) := by
  apply interior_integrableExpSet_log_quadraticDedekindLandau_of_below
    D hX hPos
  intro a ha
  exact quadraticDedekindLandauPositiveTail_integrableOn_of_neg
    D hX hb ha

end

end RobinBV.NumberField
