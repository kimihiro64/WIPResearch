/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Complete-tail interchange for integrable real or complex factors

Two integrable factors give absolute integrability on the entire triangle.
The derivative factor may be complex; no positivity or real-valuedness is
needed. The complete tail and its boundary term remain explicit.

The triangular identities generalize the candidate TailReweight in Robin1984
at published commit 2a74ac5c912cebf839bd3bf908249201eb62eb2d (Apache-2.0).
No sibling or project import is required by this candidate.
-/

namespace MeasureTheory

open Set

noncomputable section

variable {K : Type*} [RCLike K] {mu : Measure Real}

/-- Product integrand on the full tail-interchange triangle. -/
def mulTailTriangle (v F : Real -> K) (a t : Real) : K :=
  if a <= t then v a * F t else 0

/-- Exact left section, including its upper endpoint. -/
theorem integral_mulTailTriangle_left
    {x t : Real} (v F : Real -> K) :
    integral (mu.restrict (Ioi x)) (fun a => mulTailTriangle v F a t) =
      integral (mu.restrict (Ioc x t)) v * F t := by
  have hFunction : (fun a => mulTailTriangle v F a t) =
      (Iic t).indicator (fun a : Real => v a * F t) := by
    funext a
    simp [mulTailTriangle, Set.indicator]
  rw [hFunction, setIntegral_indicator measurableSet_Iic]
  have hSet : Set.inter (Ioi x) (Iic t) = Ioc x t := by ext a; rfl
  change integral (mu.restrict (Set.inter (Ioi x) (Iic t)))
    (fun a : Real => v a * F t) = _
  rw [hSet, integral_mul_const]

/-- Exact right section. The closed endpoint is removed only under an
explicit null-singleton assumption on the measure. -/
theorem integral_mulTailTriangle_right [NullSingletonClass mu]
    {x a : Real} (ha : x < a) (v F : Real -> K) :
    integral (mu.restrict (Ioi x)) (fun t => mulTailTriangle v F a t) =
      v a * integral (mu.restrict (Ioi a)) F := by
  have hFunction : (fun t => mulTailTriangle v F a t) =
      (Ici a).indicator (fun t : Real => v a * F t) := by
    funext t
    simp [mulTailTriangle, Set.indicator]
  rw [hFunction, setIntegral_indicator measurableSet_Ici]
  have hSet : Set.inter (Ioi x) (Ici a) = Ici a := by
    apply inter_eq_right.mpr
    intro t ht
    exact lt_of_lt_of_le ha ht
  change integral (mu.restrict (Set.inter (Ioi x) (Ici a)))
    (fun t : Real => v a * F t) = _
  rw [hSet, integral_Ici_eq_integral_Ioi, integral_const_mul]

/-- Global L1 bounds on both factors supply the full triangular Fubini input. -/
theorem integrable_mulTailTriangle
    {x : Real} {v F : Real -> K}
    (hv : IntegrableOn v (Ioi x) mu) (hF : IntegrableOn F (Ioi x) mu) :
    Integrable (fun z : Prod Real Real => mulTailTriangle v F z.1 z.2)
      ((mu.restrict (Ioi x)).prod (mu.restrict (Ioi x))) := by
  change Integrable
    ({z : Prod Real Real | z.1 <= z.2}.indicator (fun z => v z.1 * F z.2)) _
  exact (hv.mul_prod hF).indicator (measurableSet_le measurable_fst measurable_snd)

/-- Absolute complete-tail interchange, with both resulting integrands proved
integrable rather than silently interchanged. -/
theorem integral_mul_tail_eq_integral_integral_Ioc_mul
    [SFinite mu] [NullSingletonClass mu]
    {x : Real} {v F : Real -> K}
    (hv : IntegrableOn v (Ioi x) mu) (hF : IntegrableOn F (Ioi x) mu) :
    And
      (IntegrableOn (fun t : Real => integral (mu.restrict (Ioc x t)) v * F t) (Ioi x) mu)
      (And
        (IntegrableOn (fun a : Real => v a * integral (mu.restrict (Ioi a)) F) (Ioi x) mu)
        (integral (mu.restrict (Ioi x)) (fun a : Real =>
          v a * integral (mu.restrict (Ioi a)) F) =
          integral (mu.restrict (Ioi x)) (fun t : Real =>
            integral (mu.restrict (Ioc x t)) v * F t))) := by
  have hJoint := integrable_mulTailTriangle hv hF
  have hLeft : IntegrableOn (fun t : Real => integral (mu.restrict (Ioc x t)) v * F t)
      (Ioi x) mu := by
    apply IntegrableOn.congr_fun hJoint.integral_prod_right _ measurableSet_Ioi
    intro t ht
    exact integral_mulTailTriangle_left v F
  have hRight : IntegrableOn (fun a : Real => v a * integral (mu.restrict (Ioi a)) F)
      (Ioi x) mu := by
    apply IntegrableOn.congr_fun hJoint.integral_prod_left _ measurableSet_Ioi
    intro a ha
    exact integral_mulTailTriangle_right ha v F
  have hSwap := integral_integral_swap (f := mulTailTriangle v F) hJoint
  have hRightEq :
      integral (mu.restrict (Ioi x)) (fun a : Real =>
        integral (mu.restrict (Ioi x)) (fun t : Real => mulTailTriangle v F a t)) =
      integral (mu.restrict (Ioi x)) (fun a : Real =>
        v a * integral (mu.restrict (Ioi a)) F) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro a ha
    exact integral_mulTailTriangle_right ha v F
  have hLeftEq :
      integral (mu.restrict (Ioi x)) (fun t : Real =>
        integral (mu.restrict (Ioi x)) (fun a : Real => mulTailTriangle v F a t)) =
      integral (mu.restrict (Ioi x)) (fun t : Real =>
        integral (mu.restrict (Ioc x t)) v * F t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact integral_mulTailTriangle_left v F
  rw [hRightEq, hLeftEq] at hSwap
  exact And.intro hLeft (And.intro hRight hSwap)

/-- A complete tail reweights against a complex primitive of an integrable
derivative. Absolute integrability of the reweighted tail is a conclusion. -/
theorem complete_tail_reweight_of_integrable
    [SFinite mu] [NullSingletonClass mu]
    {x : Real} {h v F : Real -> K}
    (hv : IntegrableOn v (Ioi x) mu) (hF : IntegrableOn F (Ioi x) mu)
    (hPrimitive : forall t : Real, x < t ->
      integral (mu.restrict (Ioc x t)) v = h t - h x) :
    And
      (IntegrableOn (fun t : Real => h t * F t) (Ioi x) mu)
      (And
        (IntegrableOn (fun a : Real => v a * integral (mu.restrict (Ioi a)) F) (Ioi x) mu)
        (integral (mu.restrict (Ioi x)) (fun t : Real => h t * F t) =
          h x * integral (mu.restrict (Ioi x)) F +
            integral (mu.restrict (Ioi x)) (fun a : Real =>
              v a * integral (mu.restrict (Ioi a)) F))) := by
  have hSwap := integral_mul_tail_eq_integral_integral_Ioc_mul hv hF
  have hWeighted : IntegrableOn (fun t : Real => h t * F t) (Ioi x) mu := by
    apply (hSwap.1.add (hF.const_mul (h x))).congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.add_apply]
    rw [hPrimitive t ht, sub_mul, sub_add_cancel]
  have hLeft :
      integral (mu.restrict (Ioi x)) (fun t : Real =>
        integral (mu.restrict (Ioc x t)) v * F t) =
      integral (mu.restrict (Ioi x)) (fun t : Real => h t * F t) -
        h x * integral (mu.restrict (Ioi x)) F := by
    calc
      _ = integral (mu.restrict (Ioi x)) (fun t : Real =>
          h t * F t - h x * F t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [hPrimitive t ht, sub_mul]
      _ = _ := by rw [integral_sub hWeighted (hF.const_mul (h x)), integral_const_mul]
  have hEq := hSwap.2.2
  rw [hLeft] at hEq
  refine And.intro hWeighted (And.intro hSwap.2.1 ?_)
  exact (sub_eq_iff_eq_add.mp hEq.symm).trans (add_comm _ _)

end

end MeasureTheory
