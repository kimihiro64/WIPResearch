import Mathlib.Analysis.Meromorphic.Order
import RobinBV.NumberField.Proof.QuadraticDedekindRightmostZero
import RobinBV.NumberField.Proof.QuadraticDedekindZeroSymmetry

/-!
# Quadratic Dedekind logarithmic-derivative poles

Every zero of the continued quadratic Dedekind zeta away from its pole at one
produces a genuine simple pole of its logarithmic derivative. The zero itself
need not be simple: logarithmic differentiation always produces order `-1`.
The final theorem records the nonzero Laurent coefficient along the positive
real ray entering the zero, as required by the Nicolas--Landau argument.
-/

namespace RobinBV.NumberField

open Complex
open Filter

noncomputable section

theorem quadraticDedekindZetaContinuation_analyticOn_compl_one
    (D : NumberField.OddFundamentalDiscriminant) :
    AnalyticOnNhd Complex (quadraticDedekindZetaContinuation D)
      (Set.compl {(1 : Complex)}) := by
  intro s hs
  unfold quadraticDedekindZetaContinuation
  exact (analyticOn_riemannZeta s hs).mul
    ((D.character.differentiable_LFunction
      (quadraticCharacter_ne_one D)).analyticAt s)

theorem quadraticDedekindZetaLogDeriv_order_eq_neg_one
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hOne : Not (rho = 1)) :
    meromorphicOrderAt
      (logDeriv (quadraticDedekindZetaContinuation D)) rho = -1 := by
  have hAnalyticOn :=
    quadraticDedekindZetaContinuation_analyticOn_compl_one D
  have hAnalyticRho :
      AnalyticAt Complex (quadraticDedekindZetaContinuation D) rho :=
    hAnalyticOn rho (Set.mem_compl_singleton_iff.mpr hOne)
  have hMeromorphicRho :
      MeromorphicAt (quadraticDedekindZetaContinuation D) rho :=
    hAnalyticRho.meromorphicAt
  have hTendstoZero : Tendsto (quadraticDedekindZetaContinuation D)
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    have hCont : Tendsto (quadraticDedekindZetaContinuation D)
        (nhdsWithin rho (Set.compl {rho}))
        (nhds (quadraticDedekindZetaContinuation D rho)) :=
      hAnalyticRho.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [hZero] using hCont
  have hOrderPos :
      0 < meromorphicOrderAt (quadraticDedekindZetaContinuation D) rho :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hMeromorphicRho).1 hTendstoZero
  have hAnalyticTwo :
      AnalyticAt Complex (quadraticDedekindZetaContinuation D) 2 :=
    hAnalyticOn 2 (Set.mem_compl_singleton_iff.mpr (by norm_num))
  have hMeromorphicTwo :
      MeromorphicAt (quadraticDedekindZetaContinuation D) 2 :=
    hAnalyticTwo.meromorphicAt
  have hZetaTwo : Not (riemannZeta 2 = 0) :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hLTwo : Not (D.character.LFunction 2 = 0) :=
    D.character.LFunction_ne_zero_of_one_le_re
      (Or.inl (quadraticCharacter_ne_one D)) (by norm_num)
  have hValueTwo :
      Not (quadraticDedekindZetaContinuation D 2 = 0) := by
    unfold quadraticDedekindZetaContinuation
    exact mul_ne_zero hZetaTwo hLTwo
  have hTendstoTwo : Tendsto (quadraticDedekindZetaContinuation D)
      (nhdsWithin (2 : Complex) (Set.compl {(2 : Complex)}))
      (nhds (quadraticDedekindZetaContinuation D 2)) :=
    hAnalyticTwo.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hOrderTwo :
      meromorphicOrderAt (quadraticDedekindZetaContinuation D) 2 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hMeromorphicTwo).1
      (Exists.intro (quadraticDedekindZetaContinuation D 2)
        (And.intro hValueTwo hTendstoTwo))
  have hMeromorphicOn :
      MeromorphicOn (quadraticDedekindZetaContinuation D)
        (Set.compl {(1 : Complex)}) :=
    hAnalyticOn.meromorphicOn
  apply meromorphicOrderAt_logDeriv_eq_neg_one hMeromorphicRho
    (ne_of_gt hOrderPos)
  apply hMeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (x := (2 : Complex))
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  next => exact Set.mem_compl_singleton_iff.mpr (by norm_num)
  next => exact Set.mem_compl_singleton_iff.mpr hOne
  next =>
    rw [hOrderTwo]
    simp

theorem quadraticDedekindZetaLogDeriv_simplePoleLimit
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hOne : Not (rho = 1)) :
    Exists fun c : Complex => And (Not (c = 0))
      (Tendsto
        (fun s : Complex => (s - rho) *
          logDeriv (quadraticDedekindZetaContinuation D) s)
        (nhdsWithin rho (Set.compl {rho})) (nhds c)) := by
  have hOrder : meromorphicOrderAt
      (logDeriv (quadraticDedekindZetaContinuation D)) rho = -1 :=
    quadraticDedekindZetaLogDeriv_order_eq_neg_one D hZero hOne
  have hOrderNeg : meromorphicOrderAt
      (logDeriv (quadraticDedekindZetaContinuation D)) rho < 0 := by
    rw [hOrder]
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  have hMeromorphic : MeromorphicAt
      (logDeriv (quadraticDedekindZetaContinuation D)) rho :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero hOrderNeg.ne
  choose g hgAnalytic hgZero hgFactor using
    (meromorphicOrderAt_eq_int_iff hMeromorphic).1 hOrder
  refine Exists.intro (g rho) (And.intro hgZero ?_)
  apply hgAnalytic.continuousAt.continuousWithinAt.tendsto.congr'
  filter_upwards [hgFactor, self_mem_nhdsWithin] with s hs hsrho
  have hsNe : Not (s - rho = 0) :=
    sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsrho)
  rw [hs]
  simp [hsNe]

theorem quadraticDedekindZetaLogDeriv_simplePoleLimit_Ioi
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hOne : Not (rho = 1)) :
    Exists fun c : Complex => And (Not (c = 0))
      (Tendsto
        (fun u : Real => (u : Complex) *
          logDeriv (quadraticDedekindZetaContinuation D)
            (rho + (u : Complex)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds c)) := by
  choose c hc hLimit using
    quadraticDedekindZetaLogDeriv_simplePoleLimit D hZero hOne
  have hRay : Tendsto (fun u : Real => rho + (u : Complex))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin rho (Set.compl {rho})) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    next =>
      have hContinuous : ContinuousAt
          (fun u : Real => rho + (u : Complex)) 0 := by
        fun_prop
      simpa using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
    next =>
      filter_upwards [self_mem_nhdsWithin] with u hu
      apply Set.mem_compl_singleton_iff.mpr
      intro hEq
      have huZero : ((u : Real) : Complex) = 0 := by
        apply add_left_cancel (a := rho)
        simpa using hEq
      exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hu)) huZero
  refine Exists.intro c (And.intro hc ?_)
  simpa [Function.comp_def] using hLimit.comp hRay

theorem exists_rightmost_quadraticDedekindZeta_logDeriv_pole_of_not_ERH
    (D : NumberField.OddFundamentalDiscriminant)
    (hNotERH : Not (QuadraticDedekindZetaERH D)) :
    Exists fun rhoMax : Complex =>
      And (quadraticDedekindZetaContinuation D rhoMax = 0)
        (And ((1 / 2 : Real) < rhoMax.re)
          (And (rhoMax.re < 1)
            (And
              (forall v : Real, 0 < v ->
                Not (quadraticDedekindZetaContinuation D
                  (rhoMax + (v : Complex)) = 0))
              (Exists fun c : Complex => And (Not (c = 0))
                (Tendsto
                  (fun u : Real => (u : Complex) *
                    logDeriv (quadraticDedekindZetaContinuation D)
                      (rhoMax + (u : Complex)))
                  (nhdsWithin 0 (Set.Ioi 0)) (nhds c)))))) := by
  choose rho hZero hHalf hOne using
    exists_quadraticDedekindZeta_zero_re_gt_half_of_not_ERH D hNotERH
  choose rhoMax hMaxZero hMaxHalf hMaxOne hMaxIm hRight using
    exists_rightmost_horizontal_quadraticDedekindZeta_zero
      D hZero hHalf hOne
  have hMaxNeOne : Not (rhoMax = 1) := by
    intro hEq
    subst rhoMax
    norm_num at hMaxOne
  choose c hc hLimit using
    quadraticDedekindZetaLogDeriv_simplePoleLimit_Ioi
      D hMaxZero hMaxNeOne
  exact Exists.intro rhoMax
    (And.intro hMaxZero
      (And.intro hMaxHalf
        (And.intro hMaxOne
          (And.intro hRight
            (Exists.intro c (And.intro hc hLimit))))))

end

end RobinBV.NumberField
