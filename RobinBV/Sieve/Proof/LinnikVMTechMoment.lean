/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMTechOrthogonality

/-!
# The inner moment in Vinogradov's technical estimate

This module specializes the exact even-moment expansion to the dependent
Fejer choices used in Theorem 24.7.  It keeps every tuple, polynomial degree,
and phase factor explicit so that the result can be consumed directly by the
reciprocal-square kernel product bound.
-/

open Complex

noncomputable def linnikVMTechFejerMomentPhase
    {k : Nat} (alpha : Fin k -> Real) {H : Fin k -> Nat}
    (h : linnikVMTechFejerChoice H) (l : Nat) : Real :=
  Finset.univ.sum (fun j : Fin k =>
    ((h j).val : Real) *
      (2 * Real.pi * alpha j * (l : Real) ^ (j.val + 1)))

noncomputable def linnikVMTechTuplePowerDifference
    {s L k : Nat} (u v : Fin s -> Fin L) (j : Fin k) : Real :=
  Finset.univ.sum (fun i : Fin s =>
      ((u i).val : Real) ^ (j.val + 1)) -
    Finset.univ.sum (fun i : Fin s =>
      ((v i).val : Real) ^ (j.val + 1))

theorem linnik_vmtech_fejer_moment_phase_difference
    {s L k : Nat} (alpha : Fin k -> Real) {H : Fin k -> Nat}
    (h : linnikVMTechFejerChoice H) (u v : Fin s -> Fin L) :
    Finset.univ.sum (fun i : Fin s =>
        linnikVMTechFejerMomentPhase alpha h (u i).val) -
      Finset.univ.sum (fun i : Fin s =>
        linnikVMTechFejerMomentPhase alpha h (v i).val) =
      Finset.univ.sum (fun j : Fin k =>
        ((h j).val : Real) *
          (2 * Real.pi * alpha j *
            linnikVMTechTuplePowerDifference u v j)) := by
  unfold linnikVMTechFejerMomentPhase
  rw [Finset.sum_comm]
  rw [show Finset.univ.sum (fun i : Fin s =>
      Finset.univ.sum (fun j : Fin k =>
        ((h j).val : Real) *
          (2 * Real.pi * alpha j *
            ((v i).val : Real) ^ (j.val + 1)))) =
      Finset.univ.sum (fun j : Fin k =>
        Finset.univ.sum (fun i : Fin s =>
          ((h j).val : Real) *
            (2 * Real.pi * alpha j *
              ((v i).val : Real) ^ (j.val + 1)))) by
        exact Finset.sum_comm]
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  unfold linnikVMTechTuplePowerDifference
  calc
    Finset.univ.sum (fun i : Fin s =>
        ((h j).val : Real) *
          (2 * Real.pi * alpha j *
            ((u i).val : Real) ^ (j.val + 1))) -
      Finset.univ.sum (fun i : Fin s =>
        ((h j).val : Real) *
          (2 * Real.pi * alpha j *
            ((v i).val : Real) ^ (j.val + 1))) =
        (((h j).val : Real) * (2 * Real.pi * alpha j)) *
          (Finset.univ.sum (fun i : Fin s =>
              ((u i).val : Real) ^ (j.val + 1)) -
            Finset.univ.sum (fun i : Fin s =>
              ((v i).val : Real) ^ (j.val + 1))) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;>
        apply Finset.sum_congr rfl <;>
        intro i hi <;> ring
    _ = ((h j).val : Real) *
        (2 * Real.pi * alpha j *
          (Finset.univ.sum (fun i : Fin s =>
              ((u i).val : Real) ^ (j.val + 1)) -
            Finset.univ.sum (fun i : Fin s =>
              ((v i).val : Real) ^ (j.val + 1)))) := by ring

theorem linnik_vmtech_fejer_inner_even_moment_expansion
    {s L k : Nat} (alpha : Fin k -> Real) {H : Fin k -> Nat}
    (h : linnikVMTechFejerChoice H) :
    ((norm (Finset.univ.sum (fun l : Fin L =>
        Complex.exp (Complex.I *
          (linnikVMTechFejerMomentPhase alpha h l.val : Complex)))) ^
          (2 * s) : Real) : Complex) =
      Finset.univ.sum (fun u : Fin s -> Fin L =>
        Finset.univ.sum (fun v : Fin s -> Fin L =>
          Complex.exp (Complex.I *
            (Finset.univ.sum (fun j : Fin k =>
              ((h j).val : Real) *
                (2 * Real.pi * alpha j *
                  linnikVMTechTuplePowerDifference u v j)) :
                    Real) : Complex))) := by
  rw [linnik_vmtech_even_moment_expansion]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [linnik_vmtech_fejer_moment_phase_difference]

noncomputable def linnikVMTechDifferenceMoment
    {k : Nat} (alpha : Fin k -> Real) (L s : Nat)
    (h : Fin k -> Int) : Real :=
  norm (Finset.univ.sum (fun l : Fin L =>
    Complex.exp (Complex.I *
      (Finset.univ.sum (fun j : Fin k =>
        (h j : Real) *
          (2 * Real.pi * alpha j *
            (l.val : Real) ^ (j.val + 1))) : Real) : Complex))) ^ (2 * s)

theorem linnikVMTechDifferenceMoment_nonneg
    {k : Nat} (alpha : Fin k -> Real) (L s : Nat)
    (h : Fin k -> Int) :
    0 <= linnikVMTechDifferenceMoment alpha L s h := by
  unfold linnikVMTechDifferenceMoment
  positivity

theorem linnik_vmtech_fejer_choice_moment_eq_kernel_sum
    (k r X L s : Nat) (alpha : Fin k -> Real) :
    Finset.univ.sum
        (linnikVMTechFejerWeight k r X
          (linnikVMTechDifferenceMoment alpha L s)) =
      Finset.univ.sum (fun u : Fin s -> Fin L =>
        Finset.univ.sum (fun v : Fin s -> Fin L =>
          Finset.univ.prod (fun j : Fin k =>
            2 * finiteFejerKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1)
              (2 * Real.pi * alpha j *
                linnikVMTechTuplePowerDifference u v j)))) := by
  let H : Fin k -> Nat := fun j =>
    4 * (k * r * X ^ (j.val + 1)) + 1
  let t : Prod (Fin s -> Fin L) (Fin s -> Fin L) -> Fin k -> Real :=
    fun uv j => 2 * Real.pi * alpha j *
      linnikVMTechTuplePowerDifference uv.fst uv.snd j
  have hexp := linnik_vmtech_sum_fejer_product_expansion H t
  rw [<- Finset.univ_product_univ, Finset.sum_product] at hexp
  apply Complex.ofReal_injective
  calc
    ((Finset.univ.sum
        (linnikVMTechFejerWeight k r X
          (linnikVMTechDifferenceMoment alpha L s)) : Real) : Complex) =
        Finset.univ.sum (fun h : linnikVMTechFejerChoice H =>
          ((Finset.univ.prod (fun j : Fin k =>
            linnikVMTechFejerCoefficient (H j) (h j).val) : Real) :
              Complex) *
            ((linnikVMTechDifferenceMoment alpha L s
              (fun j => (h j).val) : Real) : Complex)) := by
      unfold linnikVMTechFejerWeight
      push_cast
      rfl
    _ = Finset.univ.sum (fun h : linnikVMTechFejerChoice H =>
        ((Finset.univ.prod (fun j : Fin k =>
          linnikVMTechFejerCoefficient (H j) (h j).val) : Real) :
            Complex) *
          Finset.univ.sum (fun u : Fin s -> Fin L =>
            Finset.univ.sum (fun v : Fin s -> Fin L =>
              Complex.exp (Complex.I *
                (Finset.univ.sum (fun j : Fin k =>
                  ((h j).val : Real) *
                    (2 * Real.pi * alpha j *
                      linnikVMTechTuplePowerDifference u v j)) :
                        Real) : Complex)))) := by
      apply Finset.sum_congr rfl
      intro h hh
      congr 1
      exact linnik_vmtech_fejer_inner_even_moment_expansion alpha h
    _ = ((Finset.univ.sum (fun u : Fin s -> Fin L =>
        Finset.univ.sum (fun v : Fin s -> Fin L =>
          Finset.univ.prod (fun j : Fin k =>
            2 * finiteFejerKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1)
              (2 * Real.pi * alpha j *
                linnikVMTechTuplePowerDifference u v j)))) : Real) :
                  Complex) := by
      simpa only [Finset.sum_product, H, t] using hexp.symm

theorem linnik_vmtech_difference_moment_sum_le_fejer_kernel_sum
    (k r X L s : Nat) (alpha : Fin k -> Real) :
    (linnikVMTechDifferenceRange k r X).sum
        (linnikVMTechDifferenceMoment alpha L s) <=
      Finset.univ.sum (fun u : Fin s -> Fin L =>
        Finset.univ.sum (fun v : Fin s -> Fin L =>
          Finset.univ.prod (fun j : Fin k =>
            2 * finiteFejerKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1)
              (2 * Real.pi * alpha j *
                linnikVMTechTuplePowerDifference u v j)))) := by
  calc
    (linnikVMTechDifferenceRange k r X).sum
        (linnikVMTechDifferenceMoment alpha L s) <=
      (linnikVMTechDifferenceRange k r X).sum (fun h =>
        (Finset.univ.prod (fun j : Fin k =>
          linnikVMTechFejerCoefficient
            (4 * (k * r * X ^ (j.val + 1)) + 1) (h j))) *
          linnikVMTechDifferenceMoment alpha L s h) :=
      linnik_vmtech_difference_sum_le_fejer_weighted_sum
        k r X (linnikVMTechDifferenceMoment alpha L s)
        (fun h hh => linnikVMTechDifferenceMoment_nonneg alpha L s h)
    _ <= Finset.univ.sum
        (linnikVMTechFejerWeight k r X
          (linnikVMTechDifferenceMoment alpha L s)) :=
      linnik_vmtech_weighted_difference_sum_le_fejer_choice_sum
        k r X (linnikVMTechDifferenceMoment alpha L s)
        (linnikVMTechDifferenceMoment_nonneg alpha L s)
    _ = Finset.univ.sum (fun u : Fin s -> Fin L =>
        Finset.univ.sum (fun v : Fin s -> Fin L =>
          Finset.univ.prod (fun j : Fin k =>
            2 * finiteFejerKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1)
              (2 * Real.pi * alpha j *
                linnikVMTechTuplePowerDifference u v j)))) :=
      linnik_vmtech_fejer_choice_moment_eq_kernel_sum k r X L s alpha

theorem linnik_vmtech_fejer_kernel_sum_le_reciprocal_sum
    (k r X L s : Nat) (alpha : Fin k -> Real) :
    Finset.univ.sum (fun u : Fin s -> Fin L =>
        Finset.univ.sum (fun v : Fin s -> Fin L =>
          Finset.univ.prod (fun j : Fin k =>
            2 * finiteFejerKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1)
              (2 * Real.pi * alpha j *
                linnikVMTechTuplePowerDifference u v j)))) <=
      Finset.univ.sum (fun u : Fin s -> Fin L =>
        Finset.univ.sum (fun v : Fin s -> Fin L =>
          Finset.univ.prod (fun j : Fin k =>
            2 * linnikReciprocalSquareKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
              (alpha j * linnikVMTechTuplePowerDifference u v j)))) := by
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro v hv
  have hbound := linnik_vmtech_fejer_product_le_reciprocal
    (fun j : Fin k => 4 * (k * r * X ^ (j.val + 1)) + 1)
    (fun j : Fin k =>
      alpha j * linnikVMTechTuplePowerDifference u v j)
    (by
      intro j
      omega)
  simpa only [mul_assoc] using hbound

theorem linnik_vmtech_difference_moment_sum_le_reciprocal_sum
    (k r X L s : Nat) (alpha : Fin k -> Real) :
    (linnikVMTechDifferenceRange k r X).sum
        (linnikVMTechDifferenceMoment alpha L s) <=
      Finset.univ.sum (fun u : Fin s -> Fin L =>
        Finset.univ.sum (fun v : Fin s -> Fin L =>
          Finset.univ.prod (fun j : Fin k =>
            2 * linnikReciprocalSquareKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
              (alpha j * linnikVMTechTuplePowerDifference u v j)))) := by
  exact (linnik_vmtech_difference_moment_sum_le_fejer_kernel_sum
    k r X L s alpha).trans
      (linnik_vmtech_fejer_kernel_sum_le_reciprocal_sum
        k r X L s alpha)

theorem linnikVMTechTuplePowerDifference_eq_cast
    {s L k : Nat} (u v : Fin s -> Fin L) (j : Fin k) :
    linnikVMTechTuplePowerDifference u v j =
      (linnikVMTechPowerDifference
        (fun x : Fin L => x.val) u v j : Real) := by
  rw [linnikVMTechPowerDifference_cast]
  rfl

theorem linnik_vmtech_real_sum_group_by_power_difference
    (k r X : Nat) (weight : (Fin k -> Int) -> Real) :
    ((Finset.univ : Finset (Fin (k * r) -> Fin X)).product
        Finset.univ).sum (fun vw =>
          weight (fun j => linnikVMTechPowerDifference
            (fun x : Fin X => x.val) vw.fst vw.snd j)) =
      (linnikVMTechDifferenceRange k r X).sum (fun h =>
        ((linnikVMTechDifferenceFiber k r X h).card : Real) *
          weight h) := by
  have hgroup := linnik_vmtech_sum_group_by_power_difference
    k r X (fun h => (weight h : Complex))
  have hreal := congrArg Complex.re hgroup
  simpa using hreal

theorem linnik_vmtech_pair_sum_le_vmvt_mul_difference_sum
    (k r X : Nat) (weight : (Fin k -> Int) -> Real)
    (hweight : forall h, 0 <= weight h) :
    ((Finset.univ : Finset (Fin (k * r) -> Fin X)).product
        Finset.univ).sum (fun vw =>
          weight (fun j => linnikVMTechPowerDifference
            (fun x : Fin X => x.val) vw.fst vw.snd j)) <=
      (Finset.vinogradovMeanValue k (k * r) X : Real) *
        (linnikVMTechDifferenceRange k r X).sum weight := by
  rw [linnik_vmtech_real_sum_group_by_power_difference]
  calc
    (linnikVMTechDifferenceRange k r X).sum (fun h =>
        ((linnikVMTechDifferenceFiber k r X h).card : Real) *
          weight h) <=
      (linnikVMTechDifferenceRange k r X).sum (fun h =>
        (Finset.vinogradovMeanValue k (k * r) X : Real) *
          weight h) := by
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_right
        (linnikVMTechDifferenceFiber_card_le_vmvt k r X h)
        (hweight h)
    _ = (Finset.vinogradovMeanValue k (k * r) X : Real) *
        (linnikVMTechDifferenceRange k r X).sum weight := by
      rw [Finset.mul_sum]

theorem linnik_vmtech_reciprocal_tuple_sum_le_vmvt_mul_difference_sum
    (k r X L : Nat) (alpha : Fin k -> Real) :
    Finset.univ.sum (fun u : Fin (k * r) -> Fin L =>
        Finset.univ.sum (fun v : Fin (k * r) -> Fin L =>
          Finset.univ.prod (fun j : Fin k =>
            2 * linnikReciprocalSquareKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
              (alpha j * linnikVMTechTuplePowerDifference u v j)))) <=
      (Finset.vinogradovMeanValue k (k * r) L : Real) *
        (linnikVMTechDifferenceRange k r L).sum (fun h =>
          Finset.univ.prod (fun j : Fin k =>
            2 * linnikReciprocalSquareKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
              (alpha j * (h j : Real)))) := by
  let weight : (Fin k -> Int) -> Real := fun h =>
    Finset.univ.prod (fun j : Fin k =>
      2 * linnikReciprocalSquareKernel
        (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
        (alpha j * (h j : Real)))
  have hnonneg : forall h, 0 <= weight h := by
    intro h
    unfold weight
    apply Finset.prod_nonneg
    intro j hj
    apply mul_nonneg (by norm_num)
    exact linnikReciprocalSquareKernel_nonneg _ _ (by positivity)
  have hbound := linnik_vmtech_pair_sum_le_vmvt_mul_difference_sum
    k r L weight hnonneg
  have hpairs :
      (Finset.univ : Finset (Fin (k * r) -> Fin L)).product
          (Finset.univ : Finset (Fin (k * r) -> Fin L)) =
        (Finset.univ : Finset
          (Prod (Fin (k * r) -> Fin L) (Fin (k * r) -> Fin L))) := by
    exact Finset.univ_product_univ
  rw [hpairs] at hbound
  calc
    Finset.univ.sum (fun u : Fin (k * r) -> Fin L =>
        Finset.univ.sum (fun v : Fin (k * r) -> Fin L =>
          Finset.univ.prod (fun j : Fin k =>
            2 * linnikReciprocalSquareKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
              (alpha j * linnikVMTechTuplePowerDifference u v j)))) =
      (Finset.univ : Finset
        (Prod (Fin (k * r) -> Fin L) (Fin (k * r) -> Fin L))).sum (fun vw =>
          weight (fun j => linnikVMTechPowerDifference
            (fun x : Fin L => x.val) vw.fst vw.snd j)) := by
      simpa only [weight, linnikVMTechTuplePowerDifference_eq_cast,
        Finset.univ_product_univ] using
        (Finset.sum_product
          (s := (Finset.univ : Finset (Fin (k * r) -> Fin L)))
          (t := (Finset.univ : Finset (Fin (k * r) -> Fin L)))
          (f := fun vw => weight (fun j =>
            linnikVMTechPowerDifference
              (fun x : Fin L => x.val) vw.fst vw.snd j))).symm
    _ <= (Finset.vinogradovMeanValue k (k * r) L : Real) *
        (linnikVMTechDifferenceRange k r L).sum weight := hbound
    _ = (Finset.vinogradovMeanValue k (k * r) L : Real) *
        (linnikVMTechDifferenceRange k r L).sum (fun h =>
          Finset.univ.prod (fun j : Fin k =>
            2 * linnikReciprocalSquareKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
              (alpha j * (h j : Real)))) := by rfl

theorem linnik_vmtech_difference_moment_sum_le_vmvt_mul_kernel_sum
    (k r X L : Nat) (alpha : Fin k -> Real) :
    (linnikVMTechDifferenceRange k r X).sum
        (linnikVMTechDifferenceMoment alpha L (k * r)) <=
      (Finset.vinogradovMeanValue k (k * r) L : Real) *
        (linnikVMTechDifferenceRange k r L).sum (fun h =>
          Finset.univ.prod (fun j : Fin k =>
            2 * linnikReciprocalSquareKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
              (alpha j * (h j : Real)))) := by
  exact (linnik_vmtech_difference_moment_sum_le_reciprocal_sum
    k r X L (k * r) alpha).trans
      (linnik_vmtech_reciprocal_tuple_sum_le_vmvt_mul_difference_sum
        k r X L alpha)
