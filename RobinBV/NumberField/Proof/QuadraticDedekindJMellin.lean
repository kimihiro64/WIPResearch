import RobinBV.NumberField.Proof.QuadraticDedekindNicolasLandau

/-!
# Mellin transform of the quadratic Dedekind Nicolas tail

This module represents the Nicolas tail by the complete Frullani mixture,
proves absolute integrability of the resulting three-variable carrier, and
identifies the negative-half-plane Mellin transform with the shifted
quadratic Dedekind Chebyshev-error continuation.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set

noncomputable section

theorem quadraticDedekindNicolasJ_eq_frullaniDouble
    (D : NumberField.OddFundamentalDiscriminant)
    {x : Real} (hx : 1 <= x) :
    quadraticDedekindNicolasJ D x =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
          quadraticDedekindPsiError D t * (u + 1) *
            t ^ (-(u + 2)))) := by
  unfold quadraticDedekindNicolasJ
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have htOne : 1 < t := lt_of_le_of_lt hx ht
  change quadraticDedekindPsiError D t *
      quadraticDedekindNicolasTailKernel t =
    integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
      quadraticDedekindPsiError D t * (u + 1) * t ^ (-(u + 2)))
  change quadraticDedekindPsiError D t * Robin1984.nicolasTailKernel t =
    integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
      quadraticDedekindPsiError D t * (u + 1) * t ^ (-(u + 2)))
  rw [Robin1984.nicolasTailKernel_eq_frullani htOne]
  rw [<- integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  ring

theorem quadraticDedekindFrullaniDouble_integrable
    (D : NumberField.OddFundamentalDiscriminant)
    {x : Real} (hx : 3 <= x) :
    Integrable
      (fun p : Prod Real Real =>
        quadraticDedekindPsiError D p.1 * (p.2 + 1) *
          p.1 ^ (-(p.2 + 2)))
      ((volume.restrict (Ioi x)).prod
        (volume.restrict (Ioi (0 : Real)))) := by
  let f : Prod Real Real -> Real := fun p =>
    quadraticDedekindPsiError D p.1 * (p.2 + 1) *
      p.1 ^ (-(p.2 + 2))
  have hMeas : AEStronglyMeasurable f
      ((volume.restrict (Ioi x)).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    apply AEMeasurable.aestronglyMeasurable
    have hFst : AEMeasurable (fun p : Prod Real Real => p.1)
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      measurable_fst.aemeasurable
    have hSnd : AEMeasurable (fun p : Prod Real Real => p.2)
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      measurable_snd.aemeasurable
    have hStep : Measurable (quadraticDedekindMellinStep D) := by
      unfold quadraticDedekindMellinStep
      exact (measurable_of_countable (fun k : Nat =>
        (quadraticDedekindChebyshevSum D k).re)).comp Nat.measurable_floor
    have hPsi : AEMeasurable
        (fun p : Prod Real Real => quadraticDedekindPsiError D p.1)
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) := by
      unfold quadraticDedekindPsiError
      exact (hStep.comp_aemeasurable hFst).sub hFst
    have hExponent : AEMeasurable
        (fun p : Prod Real Real => -(p.2 + 2))
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      (hSnd.add_const 2).neg
    have hPower : AEMeasurable
        (fun p : Prod Real Real => p.1 ^ (-(p.2 + 2)))
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      hFst.pow hExponent
    exact (hPsi.mul (hSnd.add_const 1)).mul hPower
  change Integrable f
    ((volume.restrict (Ioi x)).prod
      (volume.restrict (Ioi (0 : Real))))
  apply (integrable_prod_iff hMeas).2
  constructor
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t :=
      lt_trans (by norm_num) (lt_of_le_of_lt hx ht)
    have hKernel := Robin1984.nicolasFrullaniKernel_integrable htOne
    have hScaled := hKernel.const_mul (quadraticDedekindPsiError D t)
    change Integrable (fun u : Real => f (t, u))
      (volume.restrict (Ioi (0 : Real)))
    apply hScaled.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    dsimp [f]
    ring
  next =>
    have hTail :=
      (integrableOn_quadraticDedekindNicolasKernel_three D).mono_set
        (Ioi_subset_Ioi hx)
    have hTailNorm := hTail.norm
    change Integrable
      (fun t : Real => integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => norm (f (t, u))))
      (volume.restrict (Ioi x))
    apply hTailNorm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t :=
      lt_trans (by norm_num) (lt_of_le_of_lt hx ht)
    have hKernelNonneg : 0 <= quadraticDedekindNicolasTailKernel t := by
      change 0 <= Robin1984.nicolasTailKernel t
      exact Robin1984.nicolasTailKernel_nonneg htOne.le
    change norm (quadraticDedekindPsiError D t *
        quadraticDedekindNicolasTailKernel t) =
      integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => norm (f (t, u)))
    calc
      norm (quadraticDedekindPsiError D t *
          quadraticDedekindNicolasTailKernel t) =
          abs (quadraticDedekindPsiError D t) *
            quadraticDedekindNicolasTailKernel t := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hKernelNonneg]
      _ = abs (quadraticDedekindPsiError D t) *
          integral (volume.restrict (Ioi (0 : Real)))
            (fun u : Real => (u + 1) * t ^ (-(u + 2))) := by
        change abs (quadraticDedekindPsiError D t) *
            Robin1984.nicolasTailKernel t = _
        rw [Robin1984.nicolasTailKernel_eq_frullani htOne]
      _ = integral (volume.restrict (Ioi (0 : Real)))
          (fun u : Real => abs (quadraticDedekindPsiError D t) *
            ((u + 1) * t ^ (-(u + 2)))) := by
        rw [integral_const_mul]
      _ = integral (volume.restrict (Ioi (0 : Real)))
          (fun u : Real => norm (f (t, u))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        have huPos : 0 < u := hu
        have huNonneg : 0 <= u + 1 := by linarith
        have htPos : 0 < t := lt_trans (by norm_num) htOne
        have hPowerNonneg : 0 <= t ^ (-(u + 2)) :=
          Real.rpow_nonneg htPos.le _
        dsimp [f]
        rw [abs_mul, abs_mul,
          abs_of_nonneg huNonneg, abs_of_nonneg hPowerNonneg]
        ring

theorem quadraticDedekindPsiErrorMellinCell_eq_shift
    (D : NumberField.OddFundamentalDiscriminant)
    {a : Real} {s z : Complex} (ha : 1 <= a) (hs : 1 < s.re)
    (hzRe : z.re < 0) :
    integral (volume.restrict (Ioi a)) (fun t : Real =>
        ((quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-(s + 1))) *
          (((t : Complex) ^ z - (a : Complex) ^ z) / z)) =
      (quadraticDedekindPsiMellinTailContinuation D a (s - z) -
        (a : Complex) ^ z *
          quadraticDedekindPsiMellinTailContinuation D a s) / z := by
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hzZero : Not (z = 0) := by
    intro hz
    subst z
    norm_num at hzRe
  have hsShift : 1 < (s - z).re := by
    simp only [Complex.sub_re]
    linarith
  let hfun : Real -> Complex := fun t =>
    (quadraticDedekindPsiError D t : Complex) *
      (t : Complex) ^ (-(s + 1))
  let hShift : Real -> Complex := fun t =>
    (quadraticDedekindPsiError D t : Complex) *
      (t : Complex) ^ (-((s - z) + 1))
  have hH : Integrable hfun (volume.restrict (Ioi a)) := by
    dsimp [hfun]
    exact (quadraticDedekindPsiErrorMellin_integrable D hs).mono_set
      (Ioi_subset_Ioi ha)
  have hHShift : Integrable hShift (volume.restrict (Ioi a)) := by
    dsimp [hShift]
    exact (quadraticDedekindPsiErrorMellin_integrable D hsShift).mono_set
      (Ioi_subset_Ioi ha)
  have hPowerShift : forall t : Real, a < t ->
      hfun t * (t : Complex) ^ z = hShift t := by
    intro t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans haPos ht))
    dsimp [hfun, hShift]
    calc
      ((quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-(s + 1))) * (t : Complex) ^ z =
          (quadraticDedekindPsiError D t : Complex) *
            ((t : Complex) ^ (-(s + 1)) * (t : Complex) ^ z) := by ring
      _ = (quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-(s + 1) + z) := by
        rw [Complex.cpow_add _ _ htZero]
      _ = (quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-((s - z) + 1)) := by
        congr 2
        ring
  change integral (volume.restrict (Ioi a)) (fun t : Real =>
      hfun t * (((t : Complex) ^ z - (a : Complex) ^ z) / z)) = _
  calc
    integral (volume.restrict (Ioi a)) (fun t : Real =>
        hfun t * (((t : Complex) ^ z - (a : Complex) ^ z) / z)) =
        integral (volume.restrict (Ioi a)) (fun t : Real =>
          (hShift t - (a : Complex) ^ z * hfun t) / z) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      calc
        hfun t * (((t : Complex) ^ z - (a : Complex) ^ z) / z) =
            (hfun t * (t : Complex) ^ z -
              (a : Complex) ^ z * hfun t) / z := by ring
        _ = (hShift t - (a : Complex) ^ z * hfun t) / z := by
          rw [hPowerShift t ht]
    _ = (integral (volume.restrict (Ioi a)) hShift -
        (a : Complex) ^ z *
          integral (volume.restrict (Ioi a)) hfun) / z := by
      rw [integral_div]
      rw [integral_sub hHShift (hH.const_mul ((a : Complex) ^ z))]
      rw [integral_const_mul]
    _ = (quadraticDedekindPsiMellinTailContinuation D a (s - z) -
        (a : Complex) ^ z *
          quadraticDedekindPsiMellinTailContinuation D a s) / z := by
      dsimp [hShift, hfun]
      rw [quadraticDedekindPsiErrorTailMellin_eq_continuation
          D ha hsShift,
        quadraticDedekindPsiErrorTailMellin_eq_continuation D ha hs]

def quadraticDedekindJMellin
    (D : NumberField.OddFundamentalDiscriminant)
    (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
    (x : Complex) ^ (z - 1) * (quadraticDedekindNicolasJ D x : Complex))

theorem quadraticDedekindJMellinTriple_integrable
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} (hzRe : z.re < 0) :
    Integrable
      ({p : Prod Real (Prod Real Real) | p.1 < p.2.1}.indicator
        (fun p : Prod Real (Prod Real Real) =>
          (p.1 : Complex) ^ (z - 1) *
            ((quadraticDedekindPsiError D p.2.1 * (p.2.2 + 1) *
              p.2.1 ^ (-(p.2.2 + 2)) : Real) : Complex)))
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))) := by
  have hG : Integrable
      (fun x : Real => (x : Complex) ^ (z - 1))
      (volume.restrict (Ioi (3 : Real))) := by
    exact integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (by norm_num)
  have hBaseReal : Integrable
      (fun p : Prod Real Real =>
        quadraticDedekindPsiError D p.1 * (p.2 + 1) *
          p.1 ^ (-(p.2 + 2)))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) :=
    quadraticDedekindFrullaniDouble_integrable D (by norm_num)
  have hBaseComplex : Integrable
      (fun p : Prod Real Real =>
        ((quadraticDedekindPsiError D p.1 * (p.2 + 1) *
          p.1 ^ (-(p.2 + 2)) : Real) : Complex))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    exact Complex.ofRealCLM.integrable_comp hBaseReal
  have hProduct := hG.mul_prod hBaseComplex
  have hDomain : MeasurableSet
      {p : Prod Real (Prod Real Real) | p.1 < p.2.1} :=
    measurableSet_lt measurable_fst (measurable_fst.comp measurable_snd)
  exact hProduct.indicator hDomain

theorem quadraticDedekindJMellinTriple_inner_eq
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} {x : Real} (hx : 3 <= x) :
    integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
            (fun q : Prod Real (Prod Real Real) =>
              (q.1 : Complex) ^ (z - 1) *
                ((quadraticDedekindPsiError D q.2.1 * (q.2.2 + 1) *
                  q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
            (x, p)) =
      (x : Complex) ^ (z - 1) *
        (quadraticDedekindNicolasJ D x : Complex) := by
  let g : Complex := (x : Complex) ^ (z - 1)
  let baseReal : Prod Real Real -> Real := fun p =>
    quadraticDedekindPsiError D p.1 * (p.2 + 1) *
      p.1 ^ (-(p.2 + 2))
  let baseComplex : Prod Real Real -> Complex := fun p =>
    (baseReal p : Complex)
  let dx : Set (Prod Real Real) := {p | x < p.1}
  have hBaseReal : Integrable baseReal
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    dsimp [baseReal]
    exact quadraticDedekindFrullaniDouble_integrable D (by norm_num)
  have hBaseComplex : Integrable baseComplex
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    dsimp [baseComplex]
    exact Complex.ofRealCLM.integrable_comp hBaseReal
  have hdx : MeasurableSet dx := by
    dsimp [dx]
    exact measurableSet_lt measurable_const measurable_fst
  have hSection : Integrable (dx.indicator (fun p => g * baseComplex p))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) :=
    (hBaseComplex.const_mul g).indicator hdx
  have hCast :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u))) =
        ((integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseReal (t, u))) : Real) : Complex) := by
    calc
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u))) =
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            ((integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
              baseReal (t, u)) : Real) : Complex)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp [baseComplex]
        exact integral_ofReal
      _ = ((integral (volume.restrict (Ioi x)) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseReal (t, u))) : Real) : Complex) := by
        exact integral_ofReal
  change integral
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real))))
      (dx.indicator (fun p => g * baseComplex p)) =
    g * (quadraticDedekindNicolasJ D x : Complex)
  calc
    integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (dx.indicator (fun p => g * baseComplex p)) =
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            dx.indicator (fun p => g * baseComplex p) (t, u))) := by
      exact integral_prod _ hSection
    _ = integral (volume.restrict (Ioi (3 : Real)))
        ((Ioi x).indicator (fun t : Real =>
          g * integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u)))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      by_cases hxt : x < t
      next => simp [dx, Set.indicator, hxt, integral_const_mul]
      next => simp [dx, Set.indicator, hxt]
    _ = integral (volume.restrict (Set.inter (Ioi (3 : Real)) (Ioi x)))
        (fun t : Real =>
          g * integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
            baseComplex (t, u))) := by
      rw [setIntegral_indicator measurableSet_Ioi]
      rfl
    _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
        g * integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
          baseComplex (t, u))) := by
      have hInter : Set.inter (Ioi (3 : Real)) (Ioi x) = Ioi x :=
        inter_eq_right.mpr (Ioi_subset_Ioi hx)
      rw [hInter]
    _ = g * integral (volume.restrict (Ioi x)) (fun t : Real =>
        integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
          baseComplex (t, u))) := by
      rw [integral_const_mul]
    _ = g * (quadraticDedekindNicolasJ D x : Complex) := by
      rw [hCast]
      rw [quadraticDedekindNicolasJ_eq_frullaniDouble D
        (le_trans (by norm_num) hx)]

theorem quadraticDedekindJMellinTriple_x_inner_eq
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} {t u : Real} (hzRe : z.re < 0) (ht : 3 < t) :
    integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
          (fun q : Prod Real (Prod Real Real) =>
            (q.1 : Complex) ^ (z - 1) *
              ((quadraticDedekindPsiError D q.2.1 * (q.2.2 + 1) *
                q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
          (x, (t, u))) =
      ((quadraticDedekindPsiError D t * (u + 1) *
          t ^ (-(u + 2)) : Real) : Complex) *
        (((t : Complex) ^ z - (3 : Complex) ^ z) / z) := by
  let c : Complex :=
    ((quadraticDedekindPsiError D t * (u + 1) *
      t ^ (-(u + 2)) : Real) : Complex)
  let g : Real -> Complex := fun x => (x : Complex) ^ (z - 1)
  let dt : Set Real := Iio t
  change integral (volume.restrict (Ioi (3 : Real)))
      (dt.indicator (fun x : Real => g x * c)) =
    c * (((t : Complex) ^ z - (3 : Complex) ^ z) / z)
  rw [setIntegral_indicator measurableSet_Iio]
  have hInter : Set.inter (Ioi (3 : Real)) (Iio t) = Ioo 3 t := by
    ext x
    simp [Set.inter]
  change integral
      (volume.restrict (Set.inter (Ioi (3 : Real)) (Iio t)))
      (fun x : Real => g x * c) = _
  rw [hInter]
  calc
    integral (volume.restrict (Ioo (3 : Real) t)) (fun x : Real =>
        g x * c) =
        integral (volume.restrict (Ioo (3 : Real) t)) (fun x : Real =>
          c * g x) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      ring
    _ = c * integral (volume.restrict (Ioo (3 : Real) t)) g := by
      rw [integral_const_mul]
    _ = c * integral (volume.restrict (Ioc (3 : Real) t)) g := by
      rw [integral_Ioc_eq_integral_Ioo]
    _ = c * (((t : Complex) ^ z - (3 : Complex) ^ z) / z) := by
      dsimp [g]
      rw [Robin1984.integral_Ioc_cpow_sub_one
        (by norm_num) ht.le (by
          intro hz
          subst z
          norm_num at hzRe)]
      norm_num

theorem quadraticDedekindJMellin_eq_tripleSwapped
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} (hzRe : z.re < 0) :
    quadraticDedekindJMellin D z =
      integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
              (fun q : Prod Real (Prod Real Real) =>
                (q.1 : Complex) ^ (z - 1) *
                  ((quadraticDedekindPsiError D q.2.1 * (q.2.2 + 1) *
                    q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
              (x, p))) := by
  have hUncurried : Integrable
      (Function.uncurry (fun x : Real => fun p : Prod Real Real =>
        {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
          (fun q : Prod Real (Prod Real Real) =>
            (q.1 : Complex) ^ (z - 1) *
              ((quadraticDedekindPsiError D q.2.1 * (q.2.2 + 1) *
                q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
          (x, p)))
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))) := by
    change Integrable
      ({p : Prod Real (Prod Real Real) | p.1 < p.2.1}.indicator
        (fun p : Prod Real (Prod Real Real) =>
          (p.1 : Complex) ^ (z - 1) *
            ((quadraticDedekindPsiError D p.2.1 * (p.2.2 + 1) *
              p.2.1 ^ (-(p.2.2 + 2)) : Real) : Complex)))
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real)))))
    exact quadraticDedekindJMellinTriple_integrable D hzRe
  unfold quadraticDedekindJMellin
  calc
    integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        (x : Complex) ^ (z - 1) *
          (quadraticDedekindNicolasJ D x : Complex)) =
        integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          integral
            ((volume.restrict (Ioi (3 : Real))).prod
              (volume.restrict (Ioi (0 : Real))))
            (fun p : Prod Real Real =>
              {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
                (fun q : Prod Real (Prod Real Real) =>
                  (q.1 : Complex) ^ (z - 1) *
                    ((quadraticDedekindPsiError D q.2.1 *
                      (q.2.2 + 1) *
                      q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
                (x, p))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (quadraticDedekindJMellinTriple_inner_eq D hx.le).symm
    _ = integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            {q : Prod Real (Prod Real Real) | q.1 < q.2.1}.indicator
              (fun q : Prod Real (Prod Real Real) =>
                (q.1 : Complex) ^ (z - 1) *
                  ((quadraticDedekindPsiError D q.2.1 * (q.2.2 + 1) *
                    q.2.1 ^ (-(q.2.2 + 2)) : Real) : Complex))
              (x, p))) := integral_integral_swap hUncurried

theorem quadraticDedekindJMellinTriple_t_inner_eq
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} {u : Real} (hzRe : z.re < 0) (hu : 0 < u) :
    integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        ((quadraticDedekindPsiError D t * (u + 1) *
          t ^ (-(u + 2)) : Real) : Complex) *
          (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) =
      ((u + 1 : Real) : Complex) *
        ((quadraticDedekindPsiMellinTailContinuation D 3
            (((u + 1 : Real) : Complex) - z) -
          (3 : Complex) ^ z *
            quadraticDedekindPsiMellinTailContinuation D 3
              ((u + 1 : Real) : Complex)) / z) := by
  let s : Complex := ((u + 1 : Real) : Complex)
  let c : Complex := ((u + 1 : Real) : Complex)
  have hs : 1 < s.re := by
    dsimp [s]
    linarith
  have hPoint : forall t : Real, 3 < t ->
      ((quadraticDedekindPsiError D t * (u + 1) *
        t ^ (-(u + 2)) : Real) : Complex) *
          (((t : Complex) ^ z - (3 : Complex) ^ z) / z) =
        c * (((quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-(s + 1))) *
            (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) := by
    intro t ht
    have htPos : 0 < t := lt_trans (by norm_num) ht
    have hPower :
        ((t ^ (-(u + 2)) : Real) : Complex) =
          (t : Complex) ^ (-(s + 1)) := by
      rw [Complex.ofReal_cpow htPos.le]
      congr 1
      dsimp [s]
      push_cast
      ring
    dsimp [c]
    push_cast
    rw [hPower]
    ring
  calc
    integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        ((quadraticDedekindPsiError D t * (u + 1) *
          t ^ (-(u + 2)) : Real) : Complex) *
          (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) =
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          c * (((quadraticDedekindPsiError D t : Complex) *
            (t : Complex) ^ (-(s + 1))) *
              (((t : Complex) ^ z - (3 : Complex) ^ z) / z))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hPoint t ht
    _ = c * integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        ((quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-(s + 1))) *
            (((t : Complex) ^ z - (3 : Complex) ^ z) / z)) := by
      rw [integral_const_mul]
    _ = c *
        ((quadraticDedekindPsiMellinTailContinuation D 3 (s - z) -
          (3 : Complex) ^ z *
            quadraticDedekindPsiMellinTailContinuation D 3 s) / z) := by
      congr 1
      simpa using
        (quadraticDedekindPsiErrorMellinCell_eq_shift
          D (a := (3 : Real)) (s := s) (z := z)
            (by norm_num) hs hzRe)
    _ = ((u + 1 : Real) : Complex) *
        ((quadraticDedekindPsiMellinTailContinuation D 3
            (((u + 1 : Real) : Complex) - z) -
          (3 : Complex) ^ z *
            quadraticDedekindPsiMellinTailContinuation D 3
              ((u + 1 : Real) : Complex)) / z) := by
      rfl

theorem quadraticDedekindJMellin_eq_integral_shift
    (D : NumberField.OddFundamentalDiscriminant)
    {z : Complex} (hzRe : z.re < 0) :
    quadraticDedekindJMellin D z =
      integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        ((u + 1 : Real) : Complex) *
          ((quadraticDedekindPsiMellinTailContinuation D 3
              (((u + 1 : Real) : Complex) - z) -
            (3 : Complex) ^ z *
              quadraticDedekindPsiMellinTailContinuation D 3
                ((u + 1 : Real) : Complex)) / z)) := by
  let triple : Prod Real (Prod Real Real) -> Complex := fun q =>
    {p : Prod Real (Prod Real Real) | p.1 < p.2.1}.indicator
      (fun p : Prod Real (Prod Real Real) =>
        (p.1 : Complex) ^ (z - 1) *
          ((quadraticDedekindPsiError D p.2.1 * (p.2.2 + 1) *
            p.2.1 ^ (-(p.2.2 + 2)) : Real) : Complex)) q
  have hTriple : Integrable triple
      ((volume.restrict (Ioi (3 : Real))).prod
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))) := by
    dsimp [triple]
    exact quadraticDedekindJMellinTriple_integrable D hzRe
  have hOuter : Integrable
      (fun p : Prod Real Real =>
        integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          triple (x, p)))
      ((volume.restrict (Ioi (3 : Real))).prod
        (volume.restrict (Ioi (0 : Real)))) :=
    hTriple.integral_prod_right
  calc
    quadraticDedekindJMellin D z = integral
        ((volume.restrict (Ioi (3 : Real))).prod
          (volume.restrict (Ioi (0 : Real))))
        (fun p : Prod Real Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            triple (x, p))) := by
      rw [quadraticDedekindJMellin_eq_tripleSwapped D hzRe]
    _ = integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            triple (x, (t, u))))) := by
      exact integral_prod_symm _ hOuter
    _ = integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          ((quadraticDedekindPsiError D t * (u + 1) *
            t ^ (-(u + 2)) : Real) : Complex) *
            (((t : Complex) ^ z - (3 : Complex) ^ z) / z))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp [triple]
      exact quadraticDedekindJMellinTriple_x_inner_eq D hzRe ht
    _ = integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
        ((u + 1 : Real) : Complex) *
          ((quadraticDedekindPsiMellinTailContinuation D 3
              (((u + 1 : Real) : Complex) - z) -
            (3 : Complex) ^ z *
              quadraticDedekindPsiMellinTailContinuation D 3
                ((u + 1 : Real) : Complex)) / z)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact quadraticDedekindJMellinTriple_t_inner_eq D hzRe hu

end

end RobinBV.NumberField
