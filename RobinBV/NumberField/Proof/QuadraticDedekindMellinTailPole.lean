import RobinBV.NumberField.Proof.QuadraticDedekindMellin

/-!
# Survival of the quadratic Dedekind Mellin pole after tail subtraction

The Mellin integral over the fixed startup interval `(1, 3]` is continuous in
the complex parameter. It therefore cannot cancel the nonzero pole coefficient
of the complete quadratic Dedekind Chebyshev-error transform.
-/

namespace RobinBV.NumberField

open Filter MeasureTheory Set

noncomputable section

theorem quadraticDedekindPsiMellinStartup_three_continuousAt
    (D : NumberField.OddFundamentalDiscriminant) (s0 : Complex) :
    ContinuousAt (quadraticDedekindPsiMellinStartup D 3) s0 := by
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
      (quadraticDedekindPsiErrorMellin_integrable D
        (s := (2 : Complex)) (by norm_num)).mono_set
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
  have hMeasurable : forall s : Complex, AEStronglyMeasurable
      (fun t : Real => (quadraticDedekindPsiError D t : Complex) *
        (t : Complex) ^ (-(s + 1)))
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
    dsimp [base, ratio]
    rw [mul_assoc, <- Complex.cpow_add _ _ htZero]
    congr 2
    ring
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall t : Real, 1 < t -> t <= 3 ->
        norm ((quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-(s + 1))) <= majorant t := by
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
    rw [show -(s + 1) = (-3 : Complex) + ((2 : Complex) - s) by ring,
      Complex.cpow_add _ _ htZero, norm_mul]
    dsimp [majorant, base]
    simp only [norm_mul]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hRatioBound
        (mul_nonneg (norm_nonneg
          ((quadraticDedekindPsiError D t : Complex)))
          (norm_nonneg ((t : Complex) ^ (-3 : Complex)))))
  unfold quadraticDedekindPsiMellinStartup
  apply continuousAt_of_dominated
      (F := fun s : Complex => fun t : Real =>
        (quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-(s + 1)))
      (bound := majorant)
  next => exact Eventually.of_forall hMeasurable
  next =>
    filter_upwards [Metric.ball_mem_nhds s0 zero_lt_one] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hBound s (by simpa [Metric.mem_ball] using hs) t ht.1 ht.2
  next => exact hMajorantIntegrable
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_trans zero_lt_one ht.1))
    have hExponent : ContinuousAt (fun s : Complex => -(s + 1)) s0 := by
      fun_prop
    exact continuousAt_const.mul
      ((continuousAt_const_cpow htZero).comp hExponent)

theorem quadraticDedekindPsiMellinTailContinuation_three_simplePoleLimit_Ioi
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hRhoZero : Not (rho = 0))
    (hOne : Not (rho = 1)) :
    Exists fun c : Complex => And (Not (c = 0))
      (Tendsto
        (fun u : Real => (u : Complex) *
          quadraticDedekindPsiMellinTailContinuation D 3
            (rho + (u : Complex)))
        (nhdsWithin 0 (Ioi 0)) (nhds c)) := by
  choose c hc hFull using
    quadraticDedekindPsiMellinContinuation_simplePoleLimit_Ioi
      D hZero hRhoZero hOne
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  have hU : Tendsto (fun u : Real => (u : Complex)) l (nhds 0) := by
    have hContinuous : ContinuousAt (fun u : Real => (u : Complex)) 0 := by
      fun_prop
    simpa [l] using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hShift : Tendsto (fun u : Real => rho + (u : Complex)) l
      (nhds rho) := by
    simpa using tendsto_const_nhds.add hU
  have hStartup : Tendsto
      (fun u : Real => quadraticDedekindPsiMellinStartup D 3
        (rho + (u : Complex))) l
      (nhds (quadraticDedekindPsiMellinStartup D 3 rho)) :=
    (quadraticDedekindPsiMellinStartup_three_continuousAt D rho).tendsto.comp
      hShift
  have hStartupScaled : Tendsto
      (fun u : Real => (u : Complex) *
        quadraticDedekindPsiMellinStartup D 3 (rho + (u : Complex))) l
      (nhds 0) := by
    simpa using hU.mul hStartup
  refine Exists.intro c (And.intro hc ?_)
  have hTail := hFull.sub hStartupScaled
  apply hTail.congr'
  filter_upwards with u
  unfold quadraticDedekindPsiMellinTailContinuation
  ring

theorem exists_rightmost_quadraticDedekindPsiMellinTail_pole_of_not_ERH
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
                    quadraticDedekindPsiMellinTailContinuation D 3
                      (rhoMax + (u : Complex)))
                  (nhdsWithin 0 (Ioi 0)) (nhds c)))))) := by
  choose rhoMax hZero hHalf hOne hRay hComplete using
    exists_rightmost_quadraticDedekindPsiMellin_pole_of_not_ERH D hNotERH
  have hRhoZero : Not (rhoMax = 0) := by
    intro hEq
    subst rhoMax
    norm_num at hHalf
  have hRhoOne : Not (rhoMax = 1) := by
    intro hEq
    subst rhoMax
    norm_num at hOne
  choose c hc hTail using
    quadraticDedekindPsiMellinTailContinuation_three_simplePoleLimit_Ioi
      D hZero hRhoZero hRhoOne
  exact Exists.intro rhoMax
    (And.intro hZero
      (And.intro hHalf
        (And.intro hOne
          (And.intro hRay
            (Exists.intro c (And.intro hc hTail))))))

end

end RobinBV.NumberField
