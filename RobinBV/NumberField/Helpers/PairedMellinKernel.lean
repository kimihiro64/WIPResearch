import Robin1984.NicolasLandau.RobinWeightedIntegral

/-!
# The inverse Robin-weight Mellin kernel

Multiplication by the exact exponent-one Robin weight turns this kernel into
the ordinary Chebyshev Mellin kernel. Its derivative separates into two
real amplitudes, useful for holomorphy without differentiating a step function.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

def pairedMellinAmplitude (t : Real) : Real :=
  (Real.log t) ^ 2 / (Real.log t + 1)

def pairedMellinSlope (t : Real) : Real :=
  1 - 1 / (Real.log t + 1) ^ 2

def pairedMellinKernel (s : Complex) (t : Real) : Complex :=
  (t : Complex) ^ (1 - s) * (pairedMellinAmplitude t : Complex)

def pairedMellinKernelDerivative (s : Complex) (t : Real) : Complex :=
  (t : Complex) ^ (-s) *
    ((1 - s) * (pairedMellinAmplitude t : Complex) + (pairedMellinSlope t : Complex))

theorem hasDerivAt_pairedMellinAmplitude
    {t : Real} (ht : 1 < t) :
    HasDerivAt pairedMellinAmplitude (pairedMellinSlope t / t) t := by
  have ht0 : Not (t = 0) := ne_of_gt (lt_trans zero_lt_one ht)
  have hd : Not (Real.log t + 1 = 0) := by
    have := Real.log_pos ht
    positivity
  have hLog := Real.hasDerivAt_log ht0
  have hRaw := (hLog.fun_pow 2).div (hLog.add_const 1) hd
  apply hRaw.congr_deriv
  unfold pairedMellinSlope
  norm_num
  field_simp [ht0, hd]
  ring

theorem cpow_one_sub_eq_cpow_neg_mul
    (s : Complex) {t : Real} (ht : 0 < t) :
    (t : Complex) ^ (1 - s) = (t : Complex) ^ (-s) * (t : Complex) := by
  rw [show 1 - s = -s + 1 by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)), Complex.cpow_one]

theorem hasDerivAt_pairedMellinKernel
    (s : Complex) {t : Real} (ht : 1 < t) :
    HasDerivAt (pairedMellinKernel s) (pairedMellinKernelDerivative s t) t := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hPower : HasDerivAt (fun u : Real => (u : Complex) ^ (1 - s))
      ((1 - s) * (t : Complex) ^ (-s)) t := by
    have hSlit : Membership.mem Complex.slitPlane (t : Complex) := by
      simp [ht0]
    simpa only [sub_sub_cancel_left] using
      (Complex.hasStrictDerivAt_cpow_const (c := 1 - s) hSlit).hasDerivAt.comp_ofReal
  have hRaw := hPower.mul (hasDerivAt_pairedMellinAmplitude ht).ofReal_comp
  apply hRaw.congr_deriv
  unfold pairedMellinKernelDerivative
  rw [cpow_one_sub_eq_cpow_neg_mul s ht0, Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)]

theorem pairedMellinKernel_mul_robinRealWeight
    (s : Complex) {t : Real} (ht : 1 < t) :
    pairedMellinKernel s t * (Robin1984.robinRealWeight 1 t : Complex) =
      (t : Complex) ^ (-s - 1) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have htNe : Not ((t : Complex) = 0) := Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)
  have hLog : Not ((Real.log t : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos ht))
  have hLogOne : Not ((Real.log t : Complex) + 1 = 0) := by
    have : Not (Real.log t + 1 = 0) := by
      have := Real.log_pos ht
      positivity
    exact_mod_cast this
  have hWeight : Robin1984.robinRealWeight 1 t =
      (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by
    unfold Robin1984.robinRealWeight
    norm_num
    ring
  rw [hWeight, pairedMellinKernel, pairedMellinAmplitude]
  push_cast
  have hPower : (t : Complex) ^ (-s - 1) =
      (t : Complex) ^ (1 - s) / (t : Complex) ^ (2 : Nat) := by
    rw [show -s - 1 = (1 - s) - 2 by ring, Complex.cpow_sub _ _ htNe]
    norm_cast
  rw [hPower]
  field_simp [htNe, hLog, hLogOne]

theorem continuousOn_pairedMellinAmplitude :
    ContinuousOn pairedMellinAmplitude (Ioi 1) :=
  fun _t ht => (hasDerivAt_pairedMellinAmplitude ht).continuousAt.continuousWithinAt

theorem continuousOn_pairedMellinSlope :
    ContinuousOn pairedMellinSlope (Ioi 1) := by
  intro t ht
  have ht0 : Not (t = 0) := ne_of_gt (lt_trans zero_lt_one ht)
  have hd : Not ((Real.log t + 1) ^ 2 = 0) := by
    have := Real.log_pos ht
    positivity
  exact (continuousAt_const.sub
    (continuousAt_const.div (((Real.continuousAt_log ht0).add_const 1).pow 2) hd)).continuousWithinAt

theorem continuousOn_pairedMellinKernelDerivative (s : Complex) :
    ContinuousOn (pairedMellinKernelDerivative s) (Ioi 1) := by
  have hPower : ContinuousOn (fun t : Real => (t : Complex) ^ (-s)) (Ioi 1) := by
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const t (-s)
      (Or.inr (ne_of_gt (lt_trans zero_lt_one ht)))).continuousWithinAt
  exact hPower.mul
    ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      continuousOn_pairedMellinAmplitude)).add
        (Complex.continuous_ofReal.comp_continuousOn continuousOn_pairedMellinSlope))

theorem integral_pairedMellinKernelDerivative_Ioc
    (s : Complex) {x t : Real} (hx : 1 < x) (hxt : x <= t) :
    integral (volume.restrict (Ioc x t)) (pairedMellinKernelDerivative s) =
      pairedMellinKernel s t - pairedMellinKernel s x := by
  have hSub : Set.Subset (uIcc x t) (Ioi 1) := by
    rw [uIcc_of_le hxt]
    intro u hu
    exact lt_of_lt_of_le hx hu.1
  have hInt : IntervalIntegrable (pairedMellinKernelDerivative s) volume x t :=
    ((continuousOn_pairedMellinKernelDerivative s).mono hSub).intervalIntegrable
  rw [<- intervalIntegral.integral_of_le hxt]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hasDerivAt_pairedMellinKernel s (hSub hu)) hInt

theorem pairedMellinAmplitude_bounds {t : Real} (ht : 1 < t) :
    And (0 <= pairedMellinAmplitude t) (pairedMellinAmplitude t <= Real.log t) := by
  have hL := Real.log_pos ht
  have hd : Not (Real.log t + 1 = 0) := by positivity
  have hNonneg : 0 <= pairedMellinAmplitude t := by
    unfold pairedMellinAmplitude
    positivity
  have hEq : pairedMellinAmplitude t * (Real.log t + 1) = (Real.log t) ^ 2 := by
    unfold pairedMellinAmplitude
    field_simp [hd]
  exact And.intro hNonneg (by nlinarith)

theorem pairedMellinSlope_bounds {t : Real} (ht : 1 < t) :
    And (0 <= pairedMellinSlope t) (pairedMellinSlope t <= 1) := by
  have hL := Real.log_pos ht
  have hSq : 1 <= (Real.log t + 1) ^ 2 := by nlinarith
  have hInv := one_div_le_one_div_of_le (show (0 : Real) < 1 by norm_num) hSq
  have hNonneg : 0 <= 1 / (Real.log t + 1) ^ 2 := by positivity
  unfold pairedMellinSlope
  constructor <;> linarith

theorem norm_pairedMellinKernelDerivative_le
    (s : Complex) {t : Real} (ht : 1 < t) :
    norm (pairedMellinKernelDerivative s t) <=
      t ^ (-s.re) * (norm (1 - s) * Real.log t + 1) := by
  have hA := pairedMellinAmplitude_bounds ht
  have hB := pairedMellinSlope_bounds ht
  unfold pairedMellinKernelDerivative
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one ht),
    Complex.neg_re]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _)
  calc
    _ <= norm ((1 - s) * (pairedMellinAmplitude t : Complex)) +
        norm (pairedMellinSlope t : Complex) := norm_add_le _ _
    _ = norm (1 - s) * pairedMellinAmplitude t + pairedMellinSlope t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA.1,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB.1]
    _ <= _ := add_le_add (mul_le_mul_of_nonneg_left hA.2 (norm_nonneg _)) hB.2

/-- The derivative is globally L1 on every tail above one in the safe
half-plane. This is the absolute Fubini hypothesis, not a continuation input. -/
theorem integrableOn_pairedMellinKernelDerivative
    {s : Complex} (hs : 1 < s.re) {x : Real} (hx : 1 < x) :
    IntegrableOn (pairedMellinKernelDerivative s) (Ioi x) := by
  let delta : Real := (s.re - 1) / 2
  have hDelta : 0 < delta := by dsimp only [delta]; linarith
  have hExponent : -s.re + delta < -1 := by dsimp only [delta]; linarith
  have hBase := integrableOn_Ioi_rpow_of_lt hExponent (lt_trans zero_lt_one hx)
  have hMeas : AEStronglyMeasurable (pairedMellinKernelDerivative s)
      (volume.restrict (Ioi x)) := ((continuousOn_pairedMellinKernelDerivative s).mono
    (Ioi_subset_Ioi hx.le)).aestronglyMeasurable measurableSet_Ioi
  apply (hBase.const_mul (norm (1 - s) / delta + 1)).mono' hMeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htOne : 1 < t := lt_trans hx ht
  have htPos : 0 < t := lt_trans zero_lt_one htOne
  have hLog := Real.log_le_rpow_div htPos.le hDelta
  have hOne := Real.one_le_rpow htOne.le hDelta.le
  calc
    norm (pairedMellinKernelDerivative s t) <=
        t ^ (-s.re) * (norm (1 - s) * Real.log t + 1) :=
      norm_pairedMellinKernelDerivative_le s htOne
    _ <= t ^ (-s.re) *
        (norm (1 - s) * (t ^ delta / delta) + t ^ delta) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hLog (norm_nonneg _)) hOne)
        (Real.rpow_nonneg htPos.le _)
    _ = (norm (1 - s) / delta + 1) * t ^ (-s.re + delta) := by
      rw [Real.rpow_add htPos]
      ring

/-- For every fixed positive endpoint the boundary kernel is entire in s. -/
theorem differentiable_pairedMellinKernel_parameter
    {t : Real} (ht : 0 < t) :
    Differentiable Complex (fun s => pairedMellinKernel s t) := by
  intro s
  have hPower := ((hasDerivAt_id s).const_sub 1).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)))
  exact (hPower.mul_const (pairedMellinAmplitude t : Complex)).differentiableAt

end

end RobinBV.NumberField
