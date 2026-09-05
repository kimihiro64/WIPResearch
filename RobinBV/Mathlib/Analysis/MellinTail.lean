/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.MellinTransform

/-!
# Holomorphy of a Mellin transform restricted to a positive tail

A continuous function on a closed positive tail extends by zero to a locally
integrable function. Its Mellin transform has no lower-strip restriction:
power decay at infinity alone supplies holomorphy in the appropriate half-plane.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Asymptotics

noncomputable section

namespace MeasureTheory

/-- The zero extension from an open tail. -/
def tailMellinCutoff (x : Real) (f : Real -> Complex) : Real -> Complex :=
  (Ioi x).indicator f

/-- Continuity up to the cutoff gives local integrability of the zero extension. -/
theorem locallyIntegrable_tailMellinCutoff
    {x : Real} {f : Real -> Complex} (hf : ContinuousOn f (Ici x)) :
    LocallyIntegrable (tailMellinCutoff x f) volume := by
  have hContinuous : Continuous (fun t : Real => f (max x t)) :=
    hf.comp_continuous (continuous_const.max continuous_id) (fun t => le_max_left x t)
  have hEq : tailMellinCutoff x f = (Ioi x).indicator (fun t => f (max x t)) := by
    funext t
    by_cases ht : x < t
    next =>
      simp [tailMellinCutoff, ht, max_eq_right ht.le]
    next =>
      simp [tailMellinCutoff, ht]
  rw [hEq]
  exact hContinuous.locallyIntegrable.indicator measurableSet_Ioi

/-- The extension agrees with the original function sufficiently far right. -/
theorem tailMellinCutoff_eventually_eq
    (x : Real) (f : Real -> Complex) :
    EventuallyEq atTop (tailMellinCutoff x f) f := by
  filter_upwards [eventually_gt_atTop x] with t ht
  simp [tailMellinCutoff, ht]

/-- A positive cutoff eliminates every near-zero Mellin obstruction. -/
theorem tailMellinCutoff_eventually_zero
    {x : Real} (hx : 0 < x) (f : Real -> Complex) :
    EventuallyEq (nhdsWithin 0 (Ioi 0)) (tailMellinCutoff x f) (fun _ => 0) := by
  filter_upwards [(eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds] with t ht
  simp [tailMellinCutoff, not_lt.mpr ht.le]

/-- The full Mellin transform of the extension is exactly the complete tail. -/
theorem mellin_tailMellinCutoff
    {x : Real} (hx : 0 <= x) (f : Real -> Complex) (s : Complex) :
    mellin (tailMellinCutoff x f) s =
      integral (volume.restrict (Ioi x)) (fun t : Real => (t : Complex) ^ (s - 1) * f t) := by
  have hEq : (fun t : Real => (t : Complex) ^ (s - 1) * tailMellinCutoff x f t) =
      (Ioi x).indicator (fun t : Real => (t : Complex) ^ (s - 1) * f t) := by
    funext t
    by_cases ht : x < t <;> simp [tailMellinCutoff, ht]
  change integral (volume.restrict (Ioi 0))
    (fun t : Real => (t : Complex) ^ (s - 1) * tailMellinCutoff x f t) = _
  rw [hEq, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hx]

/-- Power decay at infinity implies convergence, with no lower-strip condition. -/
theorem mellinConvergent_tailMellinCutoff
    {x a : Real} (hx : 0 < x) {f : Real -> Complex}
    (hf : ContinuousOn f (Ici x))
    (hO : IsBigO atTop f (fun t : Real => t ^ (-a)))
    {s : Complex} (hs : s.re < a) :
    MellinConvergent (tailMellinCutoff x f) s := by
  have hLocal := (locallyIntegrable_tailMellinCutoff hf).locallyIntegrableOn (Ioi 0)
  have hTop := hO.congr' (tailMellinCutoff_eventually_eq x f).symm EventuallyEq.rfl
  have hBot : IsBigO (nhdsWithin 0 (Ioi 0)) (tailMellinCutoff x f)
      (fun t : Real => t ^ (-(s.re - 1))) :=
    (isBigO_zero _ _).congr' (tailMellinCutoff_eventually_zero hx f).symm EventuallyEq.rfl
  exact mellinConvergent_of_isBigO_rpow hLocal hTop hs hBot (by linarith)

/-- Tail power decay supplies complex differentiability in an entire half-plane. -/
theorem differentiableAt_tailMellin_of_isBigO
    {x a : Real} (hx : 0 < x) {f : Real -> Complex}
    (hf : ContinuousOn f (Ici x))
    (hO : IsBigO atTop f (fun t : Real => t ^ (-a)))
    {s : Complex} (hs : s.re < a) :
    DifferentiableAt Complex (fun z : Complex =>
      integral (volume.restrict (Ioi x)) (fun t : Real => (t : Complex) ^ (z - 1) * f t)) s := by
  have hLocal := (locallyIntegrable_tailMellinCutoff hf).locallyIntegrableOn (Ioi 0)
  have hTop := hO.congr' (tailMellinCutoff_eventually_eq x f).symm EventuallyEq.rfl
  have hBot : IsBigO (nhdsWithin 0 (Ioi 0)) (tailMellinCutoff x f)
      (fun t : Real => t ^ (-(s.re - 1))) :=
    (isBigO_zero _ _).congr' (tailMellinCutoff_eventually_zero hx f).symm EventuallyEq.rfl
  have hDiff := mellin_differentiableAt_of_isBigO_rpow hLocal hTop hs hBot (by linarith)
  have hEq : mellin (tailMellinCutoff x f) = (fun z : Complex =>
      integral (volume.restrict (Ioi x)) (fun t : Real => (t : Complex) ^ (z - 1) * f t)) :=
    funext (mellin_tailMellinCutoff hx.le f)
  rw [<- hEq]
  exact hDiff

/-- Absolute integrability on the original tail, not just its zero extension. -/
theorem integrableOn_tailMellin_of_isBigO
    {x a : Real} (hx : 0 < x) {f : Real -> Complex}
    (hf : ContinuousOn f (Ici x))
    (hO : IsBigO atTop f (fun t : Real => t ^ (-a)))
    {s : Complex} (hs : s.re < a) :
    IntegrableOn (fun t : Real => (t : Complex) ^ (s - 1) * f t) (Ioi x) := by
  have hCut := mellinConvergent_tailMellinCutoff hx hf hO hs
  change IntegrableOn (fun t : Real =>
    (t : Complex) ^ (s - 1) * tailMellinCutoff x f t) (Ioi 0) at hCut
  apply (hCut.mono_set (Ioi_subset_Ioi hx.le)).congr_fun _ measurableSet_Ioi
  intro t ht
  simp [tailMellinCutoff, ht]

end MeasureTheory
