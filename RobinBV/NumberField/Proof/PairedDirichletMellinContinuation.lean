import RobinBV.Mathlib.Analysis.MellinTail
import RobinBV.NumberField.Proof.PairedDirichletCriticalBound
import RobinBV.NumberField.Proof.PairedDirichletMellinIdentity

/-!
# Paired Mellin continuation from the critical arithmetic bound

The inverse-weight derivative separates into two real amplitudes. Their
products with the actual paired tail are O(t^(-1/2)) under the critical bound:
the first logarithm cancels exactly, and the second amplitude is bounded.
Ordinary tail Mellin holomorphy then supplies the half-plane Re(s)>1/2.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set Filter Asymptotics

noncomputable section

def pairedDirichletMellinAmplitude
    {N : Nat} (chi : DirichletCharacter Complex N) (t : Real) : Complex :=
  pairedDirichletWeightedIntegral chi 1 t * (pairedMellinAmplitude t : Complex)

def pairedDirichletMellinSlope
    {N : Nat} (chi : DirichletCharacter Complex N) (t : Real) : Complex :=
  pairedDirichletWeightedIntegral chi 1 t * (pairedMellinSlope t : Complex)

/-- A logarithm-sized real amplitude cancels the exact logarithm in the
critical bound. No estimate for the Chebyshev error is introduced. -/
theorem isBigO_pairedDirichletWeightedIntegral_mul_logAmplitude
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hBound : PairedDirichletCriticalBound chi) {w : Real -> Real}
    (hw : Filter.Eventually (fun t => And (0 <= w t) (w t <= Real.log t)) atTop) :
    IsBigO atTop
      (fun t : Real => pairedDirichletWeightedIntegral chi 1 t * (w t : Complex))
      (fun t : Real => t ^ (-(1 / 2 : Real))) := by
  apply IsBigO.of_bound (pairedDirichletZeroMass chi + 1)
  filter_upwards [hBound 1 (by norm_num), hw, eventually_ge_atTop (3 : Real)]
    with t hB hw ht
  have htOne : 1 < t := by linarith
  have htPos : 0 < t := by linarith
  have hLogPos := Real.log_pos htOne
  have hSqrtPos := Real.sqrt_pos.2 htPos
  have hRpowPos : 0 < t ^ (-(1 / 2 : Real)) := Real.rpow_pos_of_pos htPos _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1,
    Real.norm_eq_abs, abs_of_pos hRpowPos]
  calc
    norm (pairedDirichletWeightedIntegral chi 1 t) * w t <=
        norm (pairedDirichletWeightedIntegral chi 1 t) * Real.log t :=
      mul_le_mul_of_nonneg_left hw.2 (norm_nonneg _)
    _ <= ((pairedDirichletZeroMass chi + 1) / (Real.sqrt t * Real.log t)) * Real.log t :=
      mul_le_mul_of_nonneg_right hB hLogPos.le
    _ = (pairedDirichletZeroMass chi + 1) * t ^ (-(1 / 2 : Real)) := by
      rw [Real.rpow_neg htPos.le, <- Real.sqrt_eq_rpow]
      field_simp [hLogPos.ne', hSqrtPos.ne']

theorem isBigO_pairedDirichletMellinAmplitude
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hBound : PairedDirichletCriticalBound chi) :
    IsBigO atTop (pairedDirichletMellinAmplitude chi)
      (fun t : Real => t ^ (-(1 / 2 : Real))) := by
  apply isBigO_pairedDirichletWeightedIntegral_mul_logAmplitude hBound
  filter_upwards [eventually_gt_atTop (1 : Real)] with t ht
  exact pairedMellinAmplitude_bounds ht

theorem isBigO_pairedDirichletMellinSlope
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hBound : PairedDirichletCriticalBound chi) :
    IsBigO atTop (pairedDirichletMellinSlope chi)
      (fun t : Real => t ^ (-(1 / 2 : Real))) := by
  apply isBigO_pairedDirichletWeightedIntegral_mul_logAmplitude hBound
  filter_upwards [eventually_gt_atTop (1 : Real),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : Real))]
    with t ht hLog
  have hSlope := pairedMellinSlope_bounds ht
  exact And.intro hSlope.1 (le_trans hSlope.2 hLog)

theorem continuousOn_pairedDirichletMellinAmplitude
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) :
    ContinuousOn (pairedDirichletMellinAmplitude chi) (Ici 3) := by
  have hA : ContinuousOn pairedMellinAmplitude (Ici 3) :=
    continuousOn_pairedMellinAmplitude.mono (fun t ht => by
      change 3 <= t at ht
      change 1 < t
      linarith)
  exact (continuousOn_pairedDirichletWeightedIntegral_one hchi).mul
    (Complex.continuous_ofReal.comp_continuousOn hA)

theorem continuousOn_pairedDirichletMellinSlope
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) :
    ContinuousOn (pairedDirichletMellinSlope chi) (Ici 3) := by
  have hB : ContinuousOn pairedMellinSlope (Ici 3) :=
    continuousOn_pairedMellinSlope.mono (fun t ht => by
      change 3 <= t at ht
      change 1 < t
      linarith)
  exact (continuousOn_pairedDirichletWeightedIntegral_one hchi).mul
    (Complex.continuous_ofReal.comp_continuousOn hB)

/-- The constructed continuation, with its fixed endpoint and both amplitudes. -/
def pairedDirichletMellinContinuation
    {N : Nat} (chi : DirichletCharacter Complex N) (s : Complex) : Complex :=
  pairedMellinKernel s 3 * pairedDirichletWeightedIntegral chi 1 3 +
    (1 - s) * integral (volume.restrict (Ioi 3)) (fun t : Real =>
      (t : Complex) ^ (-s) * pairedDirichletMellinAmplitude chi t) +
    integral (volume.restrict (Ioi 3)) (fun t : Real =>
      (t : Complex) ^ (-s) * pairedDirichletMellinSlope chi t)

theorem integrableOn_pairedDirichletMellinAmplitude
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hBound : PairedDirichletCriticalBound chi)
    {s : Complex} (hs : (1 / 2 : Real) < s.re) :
    IntegrableOn (fun t : Real => (t : Complex) ^ (-s) *
      pairedDirichletMellinAmplitude chi t) (Ioi 3) := by
  have hRe : (1 - s).re < (1 / 2 : Real) := by
    change 1 - s.re < 1 / 2
    linarith
  simpa only [sub_sub_cancel_left] using
    integrableOn_tailMellin_of_isBigO (by norm_num : (0 : Real) < 3)
      (continuousOn_pairedDirichletMellinAmplitude hchi)
      (isBigO_pairedDirichletMellinAmplitude hBound) hRe

theorem integrableOn_pairedDirichletMellinSlope
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hBound : PairedDirichletCriticalBound chi)
    {s : Complex} (hs : (1 / 2 : Real) < s.re) :
    IntegrableOn (fun t : Real => (t : Complex) ^ (-s) *
      pairedDirichletMellinSlope chi t) (Ioi 3) := by
  have hRe : (1 - s).re < (1 / 2 : Real) := by
    change 1 - s.re < 1 / 2
    linarith
  simpa only [sub_sub_cancel_left] using
    integrableOn_tailMellin_of_isBigO (by norm_num : (0 : Real) < 3)
      (continuousOn_pairedDirichletMellinSlope hchi)
      (isBigO_pairedDirichletMellinSlope hBound) hRe

/-- The critical arithmetic bound supplies actual complex differentiability,
not an assumed analytic-continuation provider. -/
theorem differentiableAt_pairedDirichletMellinContinuation
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hBound : PairedDirichletCriticalBound chi)
    {s : Complex} (hs : (1 / 2 : Real) < s.re) :
    DifferentiableAt Complex (pairedDirichletMellinContinuation chi) s := by
  have hRe : (1 - s).re < (1 / 2 : Real) := by
    change 1 - s.re < 1 / 2
    linarith
  have hA := differentiableAt_tailMellin_of_isBigO
    (by norm_num : (0 : Real) < 3)
    (continuousOn_pairedDirichletMellinAmplitude hchi)
    (isBigO_pairedDirichletMellinAmplitude hBound) hRe
  have hB := differentiableAt_tailMellin_of_isBigO
    (by norm_num : (0 : Real) < 3)
    (continuousOn_pairedDirichletMellinSlope hchi)
    (isBigO_pairedDirichletMellinSlope hBound) hRe
  have hMap : DifferentiableAt Complex (fun z : Complex => 1 - z) s :=
    ((hasDerivAt_id s).const_sub 1).differentiableAt
  have hAComp : DifferentiableAt Complex (fun z : Complex =>
      integral (volume.restrict (Ioi 3)) (fun t : Real =>
        (t : Complex) ^ (-z) * pairedDirichletMellinAmplitude chi t)) s := by
    simpa only [Function.comp_def, sub_sub_cancel_left] using hA.comp s hMap
  have hBComp : DifferentiableAt Complex (fun z : Complex =>
      integral (volume.restrict (Ioi 3)) (fun t : Real =>
        (t : Complex) ^ (-z) * pairedDirichletMellinSlope chi t)) s := by
    simpa only [Function.comp_def, sub_sub_cancel_left] using hB.comp s hMap
  exact (((differentiable_pairedMellinKernel_parameter
    (by norm_num : (0 : Real) < 3) s).mul_const
      (pairedDirichletWeightedIntegral chi 1 3)).add (hMap.mul hAComp)).add hBComp

theorem pairedDirichletMellinContinuation_eq_reweight
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hBound : PairedDirichletCriticalBound chi)
    {s : Complex} (hs : (1 / 2 : Real) < s.re) :
    pairedDirichletMellinContinuation chi s =
      pairedMellinKernel s 3 * pairedDirichletWeightedIntegral chi 1 3 +
        integral (volume.restrict (Ioi 3)) (fun t : Real =>
          pairedMellinKernelDerivative s t * pairedDirichletWeightedIntegral chi 1 t) := by
  have hA := integrableOn_pairedDirichletMellinAmplitude hchi hBound hs
  have hB := integrableOn_pairedDirichletMellinSlope hchi hBound hs
  have hEq : integral (volume.restrict (Ioi 3)) (fun t : Real =>
      pairedMellinKernelDerivative s t * pairedDirichletWeightedIntegral chi 1 t) =
      (1 - s) * integral (volume.restrict (Ioi 3)) (fun t : Real =>
        (t : Complex) ^ (-s) * pairedDirichletMellinAmplitude chi t) +
      integral (volume.restrict (Ioi 3)) (fun t : Real =>
        (t : Complex) ^ (-s) * pairedDirichletMellinSlope chi t) := by
    calc
      _ = integral (volume.restrict (Ioi 3)) (fun t : Real =>
          (1 - s) * ((t : Complex) ^ (-s) * pairedDirichletMellinAmplitude chi t) +
            (t : Complex) ^ (-s) * pairedDirichletMellinSlope chi t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only [pairedMellinKernelDerivative, pairedDirichletMellinAmplitude,
          pairedDirichletMellinSlope]
        ring
      _ = _ := by rw [integral_add (hA.const_mul (1 - s)) hB, integral_const_mul]
  rw [hEq]
  unfold pairedDirichletMellinContinuation
  exact add_assoc _ _ _

/-- Agreement with the original paired Chebyshev Mellin tail on Re(s)>1. -/
theorem pairedDirichletMellinContinuation_eq_mellinTail
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hBound : PairedDirichletCriticalBound chi)
    {s : Complex} (hs : 1 < s.re) :
    pairedDirichletMellinContinuation chi s =
      integral (volume.restrict (Ioi 3)) (fun t : Real =>
        pairedDirichletChebyshevStep chi t * (t : Complex) ^ (-s - 1)) := by
  rw [pairedDirichletMellinContinuation_eq_reweight hchi hBound (by linarith)]
  exact (pairedDirichlet_mellin_reweight hchi hs (le_refl (3 : Real))).2.2.symm

end

end RobinBV.NumberField
