import RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimePowerRemainder
import RobinBV.NumberField.Proof.CharacterPrimeMoments
import RobinBV.NumberField.Proof.PowerTailAsymptotic

/-!
# Actual root-prime character tails from Siegel-Walfisz

The prime moments are the previously proved consequences of actual SW and
ordinary PNT. Their root-scale weighted tails are absolutely integrable by
the elementary theta majorant. No asymptotic moment is assumed as a source.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- The full root-prime character moment integrated against the actual
Robin endpoint weight, without a finite prime cap. -/
def rootPrimeCharacterTail
    {N : Nat} (chi : DirichletCharacter Complex N) (r x : Real) : Complex :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    chi.primeChebyshevSum (Nat.floor (t ^ r)) * (Robin1984.robinRealWeight 1 t : Complex))

/-- Elementary prime domination proves absolute integrability of the
complete root-prime tail for every subcritical real exponent. -/
theorem integrableOn_rootPrimeCharacterTail
    {N : Nat} (chi : DirichletCharacter Complex N) {r x : Real} (hr : r < 1) (hx : 1 < x) :
    IntegrableOn (fun t : Real => chi.primeChebyshevSum (Nat.floor (t ^ r)) *
      (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
  have hPower := Robin1984.integrableOn_rpow_mul_robinRealWeight (n := 1) hx
    (by simpa only [Nat.cast_one] using hr)
  have hStepMeas : Measurable (fun t : Real => chi.primeChebyshevSum (Nat.floor (t ^ r))) :=
    (measurable_of_countable chi.primeChebyshevSum).comp
      (Nat.measurable_floor.comp (by fun_prop))
  have hWeightMeas : Measurable (fun t : Real => (Robin1984.robinRealWeight 1 t : Complex)) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  apply (hPower.const_mul (Real.log 4 + 4)).mono'
    (hStepMeas.mul hWeightMeas).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htOne : 1 < t := hx.trans ht
  have htPos : 0 < t := lt_trans Real.zero_lt_one htOne
  have hWeight := Robin1984.robinRealWeight_nonneg (n := 1) htOne
  have hPrime : norm (chi.primeChebyshevSum (Nat.floor (t ^ r))) <=
      (Real.log 4 + 4) * t ^ r := by
    calc
      _ <= Chebyshev.theta (Nat.floor (t ^ r) : Real) := chi.norm_primeChebyshevSum_le_theta _
      _ = Chebyshev.theta (t ^ r) := (Chebyshev.theta_eq_theta_coe_floor _).symm
      _ <= Chebyshev.psi (t ^ r) := Chebyshev.theta_le_psi _
      _ <= _ := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg htPos.le _)
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeight]
  calc
    _ <= ((Real.log 4 + 4) * t ^ r) * Robin1984.robinRealWeight 1 t :=
      mul_le_mul_of_nonneg_right hPrime hWeight
    _ = _ := by ring

private theorem primeChebyshevStep_div_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    Tendsto (fun t : Real => chi.primeChebyshevSum (Nat.floor t) / (t : Complex))
      atTop (nhds (if chi = 1 then (1 : Complex) else 0)) := by
  have hFloor : Tendsto (fun t : Real => Nat.floor t) atTop atTop := tendsto_nat_floor_atTop
  have hMoment := (primeChebyshevSum_div_tendsto chi).comp hFloor
  have hRatio : Tendsto (fun t : Real => (Nat.floor t : Complex) / (t : Complex))
      atTop (nhds (1 : Complex)) := by
    have hReal : Tendsto (fun t : Real => (Nat.floor t : Real) / t) atTop (nhds (1 : Real)) :=
      tendsto_nat_floor_div_atTop
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_one] using hReal.ofReal
  have h := hMoment.mul hRatio
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [hFloor.eventually (Filter.eventually_gt_atTop (0 : Nat))] with t ht
  have hNe : Not ((Nat.floor t : Complex) = 0) := by exact_mod_cast ht.ne'
  dsimp only [Function.comp_apply]
  field_simp [hNe]

/-- The root-prime ratio has its actual principal indicator as limit,
derived from SW rather than supplied as an analytic hypothesis. -/
theorem rootPrimeCharacter_ratio_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) {r : Real} (hr : 0 < r) :
    Tendsto (fun t : Real => chi.primeChebyshevSum (Nat.floor (t ^ r)) / ((t ^ r : Real) : Complex))
      atTop (nhds (if chi = 1 then (1 : Complex) else 0)) :=
  (primeChebyshevStep_div_tendsto chi).comp (tendsto_rpow_atTop hr)

private theorem rootPrimeCharacterTail_model_error_bound
    {N : Nat} (chi : DirichletCharacter Complex N) {r x : Real} (hr : r < 1) (hx : 1 < x)
    (delta : Complex) {epsilon : Real}
    (hClose : forall t : Real, x < t ->
      norm (chi.primeChebyshevSum (Nat.floor (t ^ r)) / ((t ^ r : Real) : Complex) - delta) <= epsilon) :
    norm (rootPrimeCharacterTail chi r x - delta *
      ((integral (volume.restrict (Ioi x)) (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t) : Real) : Complex)) <=
        epsilon * integral (volume.restrict (Ioi x))
          (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t) := by
  have hPower := Robin1984.integrableOn_rpow_mul_robinRealWeight (n := 1) hx
    (by simpa only [Nat.cast_one] using hr)
  have hPrime := integrableOn_rootPrimeCharacterTail chi hr hx
  have hDelta : IntegrableOn (fun t : Real =>
      delta * ((t ^ r * Robin1984.robinRealWeight 1 t : Real) : Complex)) (Ioi x) :=
    hPower.ofReal.const_mul delta
  have hFunctions : (fun t : Real =>
      (chi.primeChebyshevSum (Nat.floor (t ^ r)) - delta * ((t ^ r : Real) : Complex)) *
        (Robin1984.robinRealWeight 1 t : Complex)) =
      (fun t : Real => chi.primeChebyshevSum (Nat.floor (t ^ r)) *
        (Robin1984.robinRealWeight 1 t : Complex) -
          delta * ((t ^ r * Robin1984.robinRealWeight 1 t : Real) : Complex)) := by
    funext t
    rw [Complex.ofReal_mul]
    ring
  have hIdentity : integral (volume.restrict (Ioi x)) (fun t : Real =>
      (chi.primeChebyshevSum (Nat.floor (t ^ r)) - delta * ((t ^ r : Real) : Complex)) *
        (Robin1984.robinRealWeight 1 t : Complex)) =
      rootPrimeCharacterTail chi r x - delta *
        ((integral (volume.restrict (Ioi x)) (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t) : Real) : Complex) := by
    rw [hFunctions, integral_sub hPrime hDelta, integral_const_mul, integral_complex_ofReal]
    rfl
  have hNorm := norm_integral_le_of_norm_le (hPower.const_mul epsilon)
    (f := fun t : Real =>
      (chi.primeChebyshevSum (Nat.floor (t ^ r)) - delta * ((t ^ r : Real) : Complex)) *
        (Robin1984.robinRealWeight 1 t : Complex)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htOne : 1 < t := hx.trans ht
      have htPos : 0 < t := lt_trans Real.zero_lt_one htOne
      have hPowerPos : 0 < t ^ r := Real.rpow_pos_of_pos htPos _
      have hPowerNe : Not (((t ^ r : Real) : Complex) = 0) := Complex.ofReal_ne_zero.mpr hPowerPos.ne'
      have hWeight := Robin1984.robinRealWeight_nonneg (n := 1) htOne
      have hRewrite : chi.primeChebyshevSum (Nat.floor (t ^ r)) - delta * ((t ^ r : Real) : Complex) =
          (chi.primeChebyshevSum (Nat.floor (t ^ r)) / ((t ^ r : Real) : Complex) - delta) *
            ((t ^ r : Real) : Complex) := by field_simp [hPowerNe]
      rw [hRewrite, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hPowerPos, abs_of_nonneg hWeight]
      calc
        _ <= (epsilon * t ^ r) * Robin1984.robinRealWeight 1 t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hClose t ht) hPowerPos.le) hWeight
        _ = _ := by ring)
  rw [hIdentity, integral_const_mul] at hNorm
  exact hNorm

/-- The normalized full root-prime tail differs negligibly from its
actual principal-indicator model; the entire improper integral is controlled
by an explicit epsilon comparison on every sufficiently late tail. -/
theorem rootPrimeCharacterTail_model_error_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) {r : Real}
    (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun x : Real => ((x ^ (1 - r) * Real.log x : Real) : Complex) *
      (rootPrimeCharacterTail chi r x - (if chi = 1 then (1 : Complex) else 0) *
        ((integral (volume.restrict (Ioi x))
          (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t) : Real) : Complex))) atTop (nhds 0) := by
  let delta : Complex := if chi = 1 then 1 else 0
  have hRatio := rootPrimeCharacter_ratio_tendsto chi hr0
  apply Metric.tendsto_nhds.mpr
  intro epsilon hEpsilon
  let eta : Real := epsilon * (1 - r) / 2
  have hEta : 0 < eta := by dsimp only [eta]; positivity
  have hClose := (Metric.tendsto_nhds.mp hRatio) eta hEta
  rw [Filter.eventually_atTop] at hClose
  let X : Real := hClose.choose
  have hAll : forall t : Real, X <= t ->
      norm (chi.primeChebyshevSum (Nat.floor (t ^ r)) / ((t ^ r : Real) : Complex) - delta) < eta := by
    intro t ht
    simpa only [dist_eq_norm] using hClose.choose_spec t ht
  filter_upwards [Filter.eventually_ge_atTop (max X 2)] with x hx
  have hxTwo : 2 <= x := (le_max_right X 2).trans hx
  have hxOne : 1 < x := by linarith
  have hxPos : 0 < x := by linarith
  have hScale : 0 <= x ^ (1 - r) * Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_pos hxOne).le
  have hBound := rootPrimeCharacterTail_model_error_bound chi hr1 hxOne delta
    (epsilon := eta) (fun t ht => (hAll t (((le_max_left X 2).trans hx).trans ht.le)).le)
  have hModel := (robinPowerTail_normalized_sandwich hr0.le hr1 hxOne).2
  have hEtaEq : eta * (1 / (1 - r)) = epsilon / 2 := by
    dsimp only [eta]
    field_simp [show Not (1 - r = 0) by linarith]
  rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale]
  calc
    _ <= (x ^ (1 - r) * Real.log x) * (eta * integral (volume.restrict (Ioi x))
        (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t)) :=
      mul_le_mul_of_nonneg_left hBound hScale
    _ = eta * ((x ^ (1 - r) * Real.log x) * integral (volume.restrict (Ioi x))
        (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t)) := by ring
    _ <= eta * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hModel hEta.le
    _ = epsilon / 2 := hEtaEq
    _ < epsilon := by linarith

/-- The complete actual root-prime tail has coefficient 1/(1-r) for
principal characters and zero otherwise. Both cases follow from proved SW
prime moments and the full power-tail model, without ERH. -/
theorem rootPrimeCharacterTail_normalized_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) {r : Real}
    (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun x : Real => ((x ^ (1 - r) * Real.log x : Real) : Complex) *
      rootPrimeCharacterTail chi r x) atTop
      (nhds ((if chi = 1 then (1 : Complex) else 0) / ((1 - r : Real) : Complex))) := by
  let delta : Complex := if chi = 1 then 1 else 0
  have hModel : Tendsto (fun x : Real => delta *
      ((((x ^ (1 - r) * Real.log x) * integral (volume.restrict (Ioi x))
        (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t) : Real) : Complex))) atTop
      (nhds (delta / ((1 - r : Real) : Complex))) := by
    have h := (robinPowerTail_normalized_tendsto hr0.le hr1).ofReal.const_mul delta
    simpa only [Complex.ofReal_div, Complex.ofReal_one, mul_one_div] using h
  have h := (rootPrimeCharacterTail_model_error_tendsto chi hr0 hr1).add hModel
  convert h using 1
  next =>
    funext x
    simp only [Complex.ofReal_mul, delta]
    ring
  next =>
    simp [delta]

/-- A finite prime cap is retained inside the exact root-prime integral. -/
def cappedRootPrimeCharacterTail
    {N : Nat} (chi : DirichletCharacter Complex N) (P : Nat) (r x : Real) : Complex :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    chi.primeChebyshevSum (min P (Nat.floor (t ^ r))) * (Robin1984.robinRealWeight 1 t : Complex))

/-- The complete capped root moment is integrable and bounded by its
finite theta mass times the exact integral of the Robin weight. -/
theorem cappedRootPrimeCharacterTail_integral_data
    {N : Nat} (chi : DirichletCharacter Complex N) (P : Nat) (r : Real)
    {x : Real} (hx : 1 < x) :
    And
      (IntegrableOn (fun t : Real => chi.primeChebyshevSum (min P (Nat.floor (t ^ r))) *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x))
      (norm (cappedRootPrimeCharacterTail chi P r x) <= Chebyshev.theta (P : Real) / (x * Real.log x)) := by
  have hWeight := Robin1984.integrableOn_robinRealWeight (n := 1) (by norm_num) hx
  have hStepMeas : Measurable (fun t : Real => chi.primeChebyshevSum (min P (Nat.floor (t ^ r)))) :=
    (measurable_of_countable (fun n : Nat => chi.primeChebyshevSum (min P n))).comp
      (Nat.measurable_floor.comp (by fun_prop))
  have hWeightMeas : Measurable (fun t : Real => (Robin1984.robinRealWeight 1 t : Complex)) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  have hMajor := hWeight.const_mul (Chebyshev.theta (P : Real))
  have hBoundAE : Filter.Eventually (fun t : Real =>
      norm (chi.primeChebyshevSum (min P (Nat.floor (t ^ r))) *
        (Robin1984.robinRealWeight 1 t : Complex)) <=
          Chebyshev.theta (P : Real) * Robin1984.robinRealWeight 1 t)
      (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hWeightNonneg := Robin1984.robinRealWeight_nonneg (n := 1) (hx.trans ht)
    have hPrime := (chi.norm_primeChebyshevSum_le_theta (min P (Nat.floor (t ^ r)))).trans
      (Chebyshev.theta_mono (Nat.cast_le.mpr (Nat.min_le_left P (Nat.floor (t ^ r)))))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeightNonneg]
    exact mul_le_mul_of_nonneg_right hPrime hWeightNonneg
  have hInt : IntegrableOn (fun t : Real => chi.primeChebyshevSum (min P (Nat.floor (t ^ r))) *
      (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) :=
    hMajor.mono' (hStepMeas.mul hWeightMeas).aestronglyMeasurable hBoundAE
  have hNorm := norm_integral_le_of_norm_le hMajor hBoundAE
  have hIntegral : integral (volume.restrict (Ioi x))
      (fun t : Real => Chebyshev.theta (P : Real) * Robin1984.robinRealWeight 1 t) =
        Chebyshev.theta (P : Real) / (x * Real.log x) := by
    rw [integral_const_mul, Robin1984.integral_robinRealWeight (n := 1) (by norm_num) hx]
    norm_num [Real.rpow_neg_one]
    ring
  exact And.intro hInt (hNorm.trans_eq hIntegral)

/-- The complete uncapped root-prime integral has a uniform elementary
power-tail majorant, valid before taking any asymptotic limit. -/
theorem norm_rootPrimeCharacterTail_le
    {N : Nat} (chi : DirichletCharacter Complex N) {r x : Real}
    (hr0 : 0 <= r) (hr1 : r < 1) (hx : 1 < x) :
    norm (rootPrimeCharacterTail chi r x) <=
      (Real.log 4 + 4) * x ^ (r - 1) / ((1 - r) * Real.log x) := by
  have hPower := Robin1984.integrableOn_rpow_mul_robinRealWeight (n := 1) hx
    (by simpa only [Nat.cast_one] using hr1)
  have hBoundAE : Filter.Eventually (fun t : Real =>
      norm (chi.primeChebyshevSum (Nat.floor (t ^ r)) * (Robin1984.robinRealWeight 1 t : Complex)) <=
        (Real.log 4 + 4) * (t ^ r * Robin1984.robinRealWeight 1 t))
      (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t := hx.trans ht
    have htPos : 0 < t := lt_trans Real.zero_lt_one htOne
    have hPrime := chi.norm_primeChebyshevSum_le_theta (Nat.floor (t ^ r))
    rw [<- Chebyshev.theta_eq_theta_coe_floor] at hPrime
    have hPrimeBound := hPrime.trans ((Chebyshev.theta_le_psi _).trans
      (Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg htPos.le _)))
    have hWeight := Robin1984.robinRealWeight_nonneg (n := 1) htOne
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeight]
    calc
      _ <= ((Real.log 4 + 4) * t ^ r) * Robin1984.robinRealWeight 1 t :=
        mul_le_mul_of_nonneg_right hPrimeBound hWeight
      _ = _ := by ring
  have hNorm := norm_integral_le_of_norm_le (hPower.const_mul (Real.log 4 + 4)) hBoundAE
  rw [integral_const_mul] at hNorm
  have hModel := (robinPowerTail_secondary_bounds hr0 hr1 hx).1
  have hC : 0 <= Real.log 4 + 4 := by
    have hLog : 0 <= Real.log (4 : Real) := Real.log_nonneg (by norm_num)
    linarith
  have hUpper : integral (volume.restrict (Ioi x))
      (fun t : Real => t ^ r * Robin1984.robinRealWeight 1 t) <=
        x ^ (r - 1) / ((1 - r) * Real.log x) := by linarith
  exact hNorm.trans ((mul_le_mul_of_nonneg_left hUpper hC).trans_eq (by ring))

/-- Before the cap threshold the two prime moments agree exactly, so
their full integral difference starts at that threshold, not at x. -/
theorem rootPrimeCharacterTail_sub_capped_eq_late
    {N : Nat} (chi : DirichletCharacter Complex N) (P : Nat) {r x T : Real}
    (hr0 : 0 <= r) (hr1 : r < 1) (hx : 1 < x) (hxT : x <= T) (hCap : T ^ r <= (P : Real)) :
    rootPrimeCharacterTail chi r x - cappedRootPrimeCharacterTail chi P r x =
      rootPrimeCharacterTail chi r T - cappedRootPrimeCharacterTail chi P r T := by
  let f : Real -> Complex := fun t =>
    (chi.primeChebyshevSum (Nat.floor (t ^ r)) -
      chi.primeChebyshevSum (min P (Nat.floor (t ^ r)))) * (Robin1984.robinRealWeight 1 t : Complex)
  have hIdentity (y : Real) (hy : 1 < y) :
      rootPrimeCharacterTail chi r y - cappedRootPrimeCharacterTail chi P r y =
        integral (volume.restrict (Ioi y)) f := by
    have hFirst := integrableOn_rootPrimeCharacterTail chi hr1 hy
    have hSecond := (cappedRootPrimeCharacterTail_integral_data chi P r hy).1
    unfold rootPrimeCharacterTail cappedRootPrimeCharacterTail
    rw [<- integral_sub hFirst hSecond]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  have hSupport (t : Real) (ht : Membership.mem (Ioi x) t) (htT : t <= T) : f t = 0 := by
    have htPos : 0 < t := lt_trans Real.zero_lt_one (hx.trans ht)
    have hRoot : t ^ r <= (P : Real) := (Real.rpow_le_rpow htPos.le htT hr0).trans hCap
    have hFloorCast : (Nat.floor (t ^ r) : Real) <= (P : Real) :=
      (Nat.floor_le (Real.rpow_nonneg htPos.le _)).trans hRoot
    have hFloor : Nat.floor (t ^ r) <= P := Nat.cast_le.mp hFloorCast
    simp only [f, Nat.min_eq_right hFloor, sub_self, zero_mul]
  have hSubset : Ioi T <= Ioi x := by
    intro t ht
    exact hxT.trans_lt ht
  rw [hIdentity x hx, hIdentity T (hx.trans_le hxT)]
  calc
    _ = integral (volume.restrict (Ioi x)) ((Ioi T).indicator f) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      by_cases htT : Membership.mem (Ioi T) t
      case pos =>
        rw [Set.indicator_of_mem htT]
      case neg =>
        rw [Set.indicator_of_notMem htT]
        exact hSupport t ht (le_of_not_gt htT)
    _ = _ := by
      rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        Set.inter_eq_left.mpr hSubset]

/-- Complete finite cap-error estimate at the true support threshold.
The finite theta(P) term is retained exactly in this bound. -/
theorem norm_rootPrimeCharacterTail_sub_capped_le
    {N : Nat} (chi : DirichletCharacter Complex N) (P : Nat) {r x T : Real}
    (hr0 : 0 <= r) (hr1 : r < 1) (hx : 1 < x) (hxT : x <= T) (hCap : T ^ r <= (P : Real)) :
    norm (rootPrimeCharacterTail chi r x - cappedRootPrimeCharacterTail chi P r x) <=
      (Real.log 4 + 4) * T ^ (r - 1) / ((1 - r) * Real.log T) +
        Chebyshev.theta (P : Real) / (T * Real.log T) := by
  rw [rootPrimeCharacterTail_sub_capped_eq_late chi P hr0 hr1 hx hxT hCap]
  have hT : 1 < T := hx.trans_le hxT
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_rootPrimeCharacterTail_le chi hr0 hr1 hT)
    (cappedRootPrimeCharacterTail_integral_data chi P r hT).2)

/-- At the exact cap threshold, the full late-start cap error is bounded
in its natural root-tail normalization, uniformly in the character. -/
theorem rootPrimeCharacterTail_cap_error_scaled_le
    {N : Nat} (chi : DirichletCharacter Complex N) (P : Nat)
    {r x T : Real} (hr0 : 0 <= r) (hr1 : r < 1) (hx : 1 < x)
    (hxT : x <= T) (hCap : T ^ r = (P : Real)) :
    norm (((T ^ (1 - r) * Real.log T : Real) : Complex) *
      (rootPrimeCharacterTail chi r x - cappedRootPrimeCharacterTail chi P r x)) <=
        (Real.log 4 + 4) / (1 - r) + (Real.log 4 + 4) := by
  let C : Real := Real.log 4 + 4
  have hT : 1 < T := hx.trans_le hxT
  have hTPos : 0 < T := lt_trans Real.zero_lt_one hT
  have hLog : 0 < Real.log T := Real.log_pos hT
  have hScale : 0 <= T ^ (1 - r) * Real.log T := by positivity
  have hTheta : Chebyshev.theta (P : Real) <= C * T ^ r := by
    rw [hCap]
    exact (Chebyshev.theta_le_psi _).trans (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg P))
  have hBound := norm_rootPrimeCharacterTail_sub_capped_le chi P hr0 hr1 hx hxT hCap.le
  have hMajor : norm (rootPrimeCharacterTail chi r x - cappedRootPrimeCharacterTail chi P r x) <=
      C * T ^ (r - 1) / ((1 - r) * Real.log T) + C * T ^ r / (T * Real.log T) :=
    hBound.trans (add_le_add le_rfl (div_le_div_of_nonneg_right hTheta (mul_pos hTPos hLog).le))
  have hCancel : T ^ (1 - r) * T ^ (r - 1) = 1 := by
    rw [<- Real.rpow_add hTPos, show 1 - r + (r - 1) = 0 by ring, Real.rpow_zero]
  have hPower : T ^ (1 - r) * T ^ r = T := by
    rw [<- Real.rpow_add hTPos, sub_add_cancel, Real.rpow_one]
  have hNormalize : (T ^ (1 - r) * Real.log T) *
      (C * T ^ (r - 1) / ((1 - r) * Real.log T) + C * T ^ r / (T * Real.log T)) =
        C / (1 - r) + C := by
    calc
      _ = C * (T ^ (1 - r) * T ^ (r - 1)) / (1 - r) +
          C * (T ^ (1 - r) * T ^ r) / T := by field_simp [hLog.ne']
      _ = _ := by rw [hCancel, hPower]; field_simp [hTPos.ne']
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale]
  exact (mul_le_mul_of_nonneg_left hMajor hScale).trans_eq hNormalize

end

end RobinBV.NumberField
