/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.AlmostAllCorridorMoment

/-!
# Two-half corridor moment assembly

The analytic corridor moment estimates are proved on `[X,2X]`.  This module
adds the exact endpoint-safe assembly over `[X,4X]`, retaining both
integrability hypotheses and converting the shared endpoint from closed to
half-open form without dropping mass.
-/

set_option autoImplicit false

open MeasureTheory

theorem almost_all_integral_Icc_four_of_halves
    {X B1 B2 : Real} (hX : 0 <= X) {f : Real -> Real}
    (h1 : IntegrableOn f (Set.Icc X (2*X)))
    (h2 : IntegrableOn f (Set.Icc (2*X) (4*X)))
    (hb1 : integral (volume.restrict (Set.Icc X (2*X))) f <= B1)
    (hb2 : integral (volume.restrict (Set.Icc (2*X) (4*X))) f <= B2) :
    integral (volume.restrict (Set.Icc X (4*X))) f <= B1 + B2 := by
  have hdisj : Disjoint (Set.Icc X (2*X)) (Set.Ioc (2*X) (4*X)) := by
    exact Set.disjoint_left.mpr (by
      intro x hx hy
      exact (lt_irrefl x) (lt_of_le_of_lt hx.2 hy.1))
  have hsub : Set.Subset (Set.Ioc (2*X) (4*X)) (Set.Icc (2*X) (4*X)) := by
    intro x hx
    exact And.intro (le_of_lt hx.1) hx.2
  have h2' : IntegrableOn f (Set.Ioc (2*X) (4*X)) := h2.mono_set hsub
  have hunion : Set.union (Set.Icc X (2*X)) (Set.Ioc (2*X) (4*X)) =
      Set.Icc X (4*X) := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioc]
    constructor
    case mp =>
      intro hx
      rcases hx with hx | hx
      case inl => exact And.intro hx.1 (le_trans hx.2 (by linarith))
      case inr => exact And.intro (by linarith [hx.1]) hx.2
    case mpr =>
      intro hx
      by_cases hmid : x <= 2*X
      case pos => exact Or.inl (And.intro hx.1 hmid)
      case neg => exact Or.inr (And.intro (lt_of_not_ge hmid) hx.2)
  rw [<- hunion]
  have hmeasure : volume.restrict
      (Set.union (Set.Icc X (2*X)) (Set.Ioc (2*X) (4*X))) =
      volume.restrict (Set.Icc X (2*X)) +
        volume.restrict (Set.Ioc (2*X) (4*X)) :=
    Measure.restrict_union hdisj measurableSet_Ioc
  have hb2' : integral (volume.restrict (Set.Ioc (2*X) (4*X))) f <= B2 := by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc] using hb2
  have hsum := MeasureTheory.integral_add_measure h1 h2'
  have heq : integral (volume.restrict (Set.Icc X (2*X)) +
      volume.restrict (Set.Ioc (2*X) (4*X))) f =
      integral (volume.restrict (Set.Icc X (2*X))) f +
        integral (volume.restrict (Set.Ioc (2*X) (4*X))) f := by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc] using hsum
  have hle : integral (volume.restrict (Set.Icc X (2*X)) +
      volume.restrict (Set.Ioc (2*X) (4*X))) f <= B1 + B2 := by
    rw [heq]
    exact add_le_add hb1 hb2'
  rw [hmeasure]
  exact hle

theorem almost_all_sum_integral_Icc_four_of_halves
    {X Bf1 Bf2 Bg1 Bg2 : Real} (hX : 0 <= X)
    {f g : Real -> Real}
    (hf1 : IntegrableOn f (Set.Icc X (2*X)))
    (hf2 : IntegrableOn f (Set.Icc (2*X) (4*X)))
    (hg1 : IntegrableOn g (Set.Icc X (2*X)))
    (hg2 : IntegrableOn g (Set.Icc (2*X) (4*X)))
    (hbf1 : integral (volume.restrict (Set.Icc X (2*X))) f <= Bf1)
    (hbf2 : integral (volume.restrict (Set.Icc (2*X) (4*X))) f <= Bf2)
    (hbg1 : integral (volume.restrict (Set.Icc X (2*X))) g <= Bg1)
    (hbg2 : integral (volume.restrict (Set.Icc (2*X) (4*X))) g <= Bg2) :
    integral (volume.restrict (Set.Icc X (4*X))) (fun x => f x + g x)
      <= Bf1 + Bf2 + Bg1 + Bg2 := by
  have hs1 : IntegrableOn (fun x => f x + g x) (Set.Icc X (2*X)) :=
    hf1.add hg1
  have hs2 : IntegrableOn (fun x => f x + g x) (Set.Icc (2*X) (4*X)) :=
    hf2.add hg2
  have hsf1 : integral (volume.restrict (Set.Icc X (2*X)))
      (fun x => f x + g x) <= Bf1 + Bg1 := by
    have heq := MeasureTheory.integral_add hf1 hg1
    rw [heq]
    linarith
  have hsf2 : integral (volume.restrict (Set.Icc (2*X) (4*X)))
      (fun x => f x + g x) <= Bf2 + Bg2 := by
    have heq := MeasureTheory.integral_add hf2 hg2
    rw [heq]
    linarith
  have hmain := almost_all_integral_Icc_four_of_halves hX hs1 hs2 hsf1 hsf2
  linarith

theorem almost_all_lintegral_sum_Icc_four_of_halves
    {X Bf1 Bf2 Bg1 Bg2 : Real} (hX : 0 <= X)
    {f g : Real -> Real}
    (hf1 : IntegrableOn f (Set.Icc X (2*X)))
    (hf2 : IntegrableOn f (Set.Icc (2*X) (4*X)))
    (hg1 : IntegrableOn g (Set.Icc X (2*X)))
    (hg2 : IntegrableOn g (Set.Icc (2*X) (4*X)))
    (hfull : IntegrableOn (fun x => f x + g x) (Set.Icc X (4*X)))
    (hnonneg : forall x, 0 <= f x + g x)
    (hbf1 : integral (volume.restrict (Set.Icc X (2*X))) f <= Bf1)
    (hbf2 : integral (volume.restrict (Set.Icc (2*X) (4*X))) f <= Bf2)
    (hbg1 : integral (volume.restrict (Set.Icc X (2*X))) g <= Bg1)
    (hbg2 : integral (volume.restrict (Set.Icc (2*X) (4*X))) g <= Bg2) :
    lintegral (volume.restrict (Set.Icc X (4*X)))
        (fun x => ENNReal.ofReal (f x + g x)) <=
      ENNReal.ofReal (Bf1 + Bf2 + Bg1 + Bg2) := by
  have hsum := almost_all_sum_integral_Icc_four_of_halves hX
    hf1 hf2 hg1 hg2 hbf1 hbf2 hbg1 hbg2
  have heq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfull
    (Filter.Eventually.of_forall hnonneg)
  rw [<- heq]
  exact ENNReal.ofReal_le_ofReal hsum
