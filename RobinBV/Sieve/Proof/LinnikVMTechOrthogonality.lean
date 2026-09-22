/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMTechHolder

/-!
# Weighted orthogonality for Vinogradov's technical estimate

This module bounds every power-difference fiber on its exact finite support.
It is the support-control input for the Fejer-weighted orthogonality step in
Theorem 24.7.
-/

open Complex

theorem linnikVMTechPowerDifferenceReal_abs_le
    {I : Type*} [Fintype I] {b k M : Nat}
    (m : I -> Nat) (hm : forall x, m x <= M)
    (u v : Fin b -> I) (j : Fin k) :
    abs (linnikVMTechPowerDifferenceReal m u v j) <=
      (b : Real) * (M : Real) ^ (j.val + 1) := by
  let U : Nat := Finset.univ.sum (fun i => m (u i) ^ (j.val + 1))
  let V : Nat := Finset.univ.sum (fun i => m (v i) ^ (j.val + 1))
  have hu : U <= b * M ^ (j.val + 1) := by
    dsimp only [U]
    calc
      Finset.univ.sum (fun i => m (u i) ^ (j.val + 1)) <=
          Finset.univ.sum (fun _ : Fin b => M ^ (j.val + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        exact hm (u i)
      _ = b * M ^ (j.val + 1) := by simp
  have hv : V <= b * M ^ (j.val + 1) := by
    dsimp only [V]
    calc
      Finset.univ.sum (fun i => m (v i) ^ (j.val + 1)) <=
          Finset.univ.sum (fun _ : Fin b => M ^ (j.val + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        exact hm (v i)
      _ = b * M ^ (j.val + 1) := by simp
  have huR : (U : Real) <= (b : Real) * (M : Real) ^ (j.val + 1) := by
    exact_mod_cast hu
  have hvR : (V : Real) <= (b : Real) * (M : Real) ^ (j.val + 1) := by
    exact_mod_cast hv
  have hU0 : (0 : Real) <= U := by positivity
  have hV0 : (0 : Real) <= V := by positivity
  have hUcast : (U : Real) =
      Finset.univ.sum (fun i => (m (u i) : Real) ^ (j.val + 1)) := by
    dsimp only [U]
    push_cast
    rfl
  have hVcast : (V : Real) =
      Finset.univ.sum (fun i => (m (v i) : Real) ^ (j.val + 1)) := by
    dsimp only [V]
    push_cast
    rfl
  unfold linnikVMTechPowerDifferenceReal
  rw [<- hUcast, <- hVcast, abs_le]
  constructor <;> linarith

theorem linnikVMTechDifferenceRange_abs_le
    (k r X : Nat) (h : Fin k -> Int)
    (hh : Membership.mem (linnikVMTechDifferenceRange k r X) h)
    (j : Fin k) :
    abs (h j : Real) <=
      (k * r : Real) * (X : Real) ^ (j.val + 1) := by
  obtain hw := Finset.mem_image.mp hh
  choose vw hvw hvwDiff using hw
  have hj := congrFun hvwDiff j
  rw [<- hj, linnikVMTechPowerDifference_cast]
  simpa only [Nat.cast_mul] using
    (linnikVMTechPowerDifferenceReal_abs_le
      (fun x : Fin X => x.val) (fun x => Nat.le_of_lt x.isLt)
      vw.fst vw.snd j)

def linnikVMTechFejerDifference (ab : Prod Nat Nat) : Int :=
  (ab.fst : Int) - (ab.snd : Int)

def linnikVMTechFejerPairs (H : Nat) : Finset (Prod Nat Nat) :=
  (Finset.range H).product (Finset.range H)

def linnikVMTechFejerDifferenceRange (H : Nat) : Finset Int :=
  (linnikVMTechFejerPairs H).image linnikVMTechFejerDifference

def linnikVMTechFejerFiber (H : Nat) (h : Int) : Finset (Prod Nat Nat) :=
  (linnikVMTechFejerPairs H).filter
    (fun ab => linnikVMTechFejerDifference ab = h)

theorem linnik_vmtech_fejer_sum_group_by_difference
    (H : Nat) (weight : Int -> Complex) :
    (linnikVMTechFejerPairs H).sum
        (fun ab => weight (linnikVMTechFejerDifference ab)) =
      (linnikVMTechFejerDifferenceRange H).sum (fun h =>
        ((linnikVMTechFejerFiber H h).card : Complex) * weight h) := by
  let pairs := linnikVMTechFejerPairs H
  let diff := linnikVMTechFejerDifference
  have hmaps : forall ab, Membership.mem pairs ab ->
      Membership.mem (pairs.image diff) (diff ab) := by
    intro ab hab
    exact Finset.mem_image.mpr (Exists.intro ab (And.intro hab rfl))
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun ab => weight (diff ab))
  rw [<- hfiber]
  change (pairs.image diff).sum (fun h =>
      (pairs.filter (fun ab => diff ab = h)).sum
        (fun ab => weight (diff ab))) =
    (pairs.image diff).sum (fun h =>
      ((pairs.filter (fun ab => diff ab = h)).card : Complex) * weight h)
  apply Finset.sum_congr rfl
  intro h hh
  calc
    (pairs.filter (fun ab => diff ab = h)).sum
        (fun ab => weight (diff ab)) =
      (pairs.filter (fun ab => diff ab = h)).sum
        (fun _ => weight h) := by
      apply Finset.sum_congr rfl
      intro ab hab
      rw [(Finset.mem_filter.mp hab).2]
    _ = ((pairs.filter (fun ab => diff ab = h)).card : Complex) *
        weight h := by simp

noncomputable def linnikVMTechFejerCoefficient (H : Nat) (h : Int) : Real :=
  2 * ((linnikVMTechFejerFiber H h).card : Real) / H

theorem linnik_vmtech_fejer_coefficient_expansion
    (H : Nat) (t : Real) :
    (((2 * finiteFejerKernel H t : Real)) : Complex) =
      (linnikVMTechFejerDifferenceRange H).sum (fun h =>
        (linnikVMTechFejerCoefficient H h : Complex) *
          Complex.exp (Complex.I * (h : Complex) * (t : Complex))) := by
  let weight : Int -> Complex := fun h =>
    Complex.exp (Complex.I * (h : Complex) * (t : Complex))
  let scale : Complex := ((2 / (H : Real) : Real) : Complex)
  have hgroup := linnik_vmtech_fejer_sum_group_by_difference H weight
  calc
    (((2 * finiteFejerKernel H t : Real)) : Complex) =
        scale * (((norm (finiteCircleSum H t) ^ 2 : Real)) : Complex) := by
      unfold finiteFejerKernel scale
      push_cast
      ring
    _ = scale * (linnikVMTechFejerPairs H).sum
        (fun ab => weight (linnikVMTechFejerDifference ab)) := by
      congr 1
      rw [finiteCircleSum_sq_eq_cross]
      unfold linnikVMTechFejerPairs linnikVMTechFejerDifference weight
      exact (Finset.sum_product
        (s := Finset.range H) (t := Finset.range H)
        (f := fun ab => Complex.exp
          (Complex.I *
            (((ab.fst : Int) - (ab.snd : Int) : Int) : Complex) *
              (t : Complex)))).symm
    _ = scale * (linnikVMTechFejerDifferenceRange H).sum (fun h =>
        ((linnikVMTechFejerFiber H h).card : Complex) * weight h) := by
      rw [hgroup]
    _ = (linnikVMTechFejerDifferenceRange H).sum (fun h =>
        (linnikVMTechFejerCoefficient H h : Complex) *
          Complex.exp (Complex.I * (h : Complex) * (t : Complex))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      unfold scale weight linnikVMTechFejerCoefficient
      push_cast
      ring

theorem linnikVMTechFejerFiber_card_lower
    (B : Nat) (h : Int)
    (hlow : -(B : Int) <= h) (hhigh : h <= (B : Int)) :
    2 * B + 1 <= (linnikVMTechFejerFiber (4 * B + 1) h).card := by
  let shift : Nat := ((B : Int) + h).toNat
  have hshiftNonneg : 0 <= (B : Int) + h := by omega
  have hshiftHigh : (B : Int) + h <= 2 * (B : Int) := by omega
  have hshiftCast : (shift : Int) = (B : Int) + h := by
    exact Int.toNat_of_nonneg hshiftNonneg
  have hshiftLeInt : (shift : Int) <= ((2 * B : Nat) : Int) := by
    rw [hshiftCast]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact hshiftHigh
  have hshiftLe : shift <= 2 * B := by
    exact_mod_cast hshiftLeInt
  have hcard := Finset.card_le_card_of_injOn
    (fun t : Nat => (t + shift, t + B))
    (s := Finset.range (2 * B + 1))
    (t := linnikVMTechFejerFiber (4 * B + 1) h)
    (by
      intro t ht
      have htBound : t < 2 * B + 1 := Finset.mem_range.mp ht
      unfold linnikVMTechFejerFiber linnikVMTechFejerPairs
        linnikVMTechFejerDifference
      apply Finset.mem_filter.mpr
      constructor
      next =>
        apply Finset.mem_product.mpr
        constructor
        next =>
          rw [Finset.mem_range]
          change t + shift < 4 * B + 1
          omega
        next =>
          rw [Finset.mem_range]
          change t + B < 4 * B + 1
          omega
      next =>
        push_cast
        rw [hshiftCast]
        omega)
    (by
      intro x hx y hy hxy
      have hfst := congrArg Prod.fst hxy
      exact Nat.add_right_cancel hfst)
  simpa using hcard

theorem linnikVMTechFejerDifference_mem_of_bounds
    (B : Nat) (h : Int)
    (hlow : -(B : Int) <= h) (hhigh : h <= (B : Int)) :
    Membership.mem (linnikVMTechFejerDifferenceRange (4 * B + 1)) h := by
  have hcard := linnikVMTechFejerFiber_card_lower B h hlow hhigh
  have hpos : 0 < (linnikVMTechFejerFiber (4 * B + 1) h).card := by
    omega
  obtain hab := Finset.card_pos.mp hpos
  choose ab hab using hab
  have habFilter := Finset.mem_filter.mp hab
  unfold linnikVMTechFejerDifferenceRange
  exact Finset.mem_image.mpr
    (Exists.intro ab (And.intro habFilter.1 habFilter.2))

theorem linnikVMTechFejerCoefficient_one_le
    (B : Nat) (h : Int)
    (hlow : -(B : Int) <= h) (hhigh : h <= (B : Int)) :
    1 <= linnikVMTechFejerCoefficient (4 * B + 1) h := by
  have hcardNat := linnikVMTechFejerFiber_card_lower B h hlow hhigh
  have hcardReal : (2 * B + 1 : Nat) <=
      ((linnikVMTechFejerFiber (4 * B + 1) h).card : Real) := by
    exact_mod_cast hcardNat
  have hden : (0 : Real) < (4 * B + 1 : Nat) := by positivity
  have hmul : ((4 * B + 1 : Nat) : Real) <=
      2 * ((linnikVMTechFejerFiber (4 * B + 1) h).card : Real) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcardReal
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  unfold linnikVMTechFejerCoefficient
  calc
    1 = ((4 * B + 1 : Nat) : Real) / (4 * B + 1 : Nat) := by
      field_simp
    _ <= 2 * ((linnikVMTechFejerFiber (4 * B + 1) h).card : Real) /
        (4 * B + 1 : Nat) :=
      div_le_div_of_nonneg_right hmul hden.le

theorem linnikVMTechDifferenceRange_mem_fejerDifferenceRange
    (k r X : Nat) (h : Fin k -> Int)
    (hh : Membership.mem (linnikVMTechDifferenceRange k r X) h)
    (j : Fin k) :
    Membership.mem
      (linnikVMTechFejerDifferenceRange
        (4 * (k * r * X ^ (j.val + 1)) + 1)) (h j) := by
  let B : Nat := k * r * X ^ (j.val + 1)
  have habs := linnikVMTechDifferenceRange_abs_le k r X h hh j
  have hboundsReal : And
      (-((B : Nat) : Real) <= (h j : Real))
      ((h j : Real) <= (B : Nat)) := by
    dsimp only [B]
    norm_num only [Nat.cast_mul, Nat.cast_pow] at habs
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    exact abs_le.mp habs
  have hlow : -(B : Int) <= h j := by
    exact_mod_cast hboundsReal.1
  have hhigh : h j <= (B : Int) := by
    exact_mod_cast hboundsReal.2
  exact linnikVMTechFejerDifference_mem_of_bounds B (h j) hlow hhigh

theorem linnikVMTechDifferenceRange_fejerCoefficient_one_le
    (k r X : Nat) (h : Fin k -> Int)
    (hh : Membership.mem (linnikVMTechDifferenceRange k r X) h)
    (j : Fin k) :
    1 <= linnikVMTechFejerCoefficient
      (4 * (k * r * X ^ (j.val + 1)) + 1) (h j) := by
  let B : Nat := k * r * X ^ (j.val + 1)
  have habs := linnikVMTechDifferenceRange_abs_le k r X h hh j
  have hboundsReal : And
      (-((B : Nat) : Real) <= (h j : Real))
      ((h j : Real) <= (B : Nat)) := by
    dsimp only [B]
    norm_num only [Nat.cast_mul, Nat.cast_pow] at habs
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    exact abs_le.mp habs
  have hlow : -(B : Int) <= h j := by
    exact_mod_cast hboundsReal.1
  have hhigh : h j <= (B : Int) := by
    exact_mod_cast hboundsReal.2
  exact linnikVMTechFejerCoefficient_one_le B (h j) hlow hhigh

theorem linnikVMTechDifferenceRange_fejerCoefficient_product_one_le
    (k r X : Nat) (h : Fin k -> Int)
    (hh : Membership.mem (linnikVMTechDifferenceRange k r X) h) :
    1 <= Finset.univ.prod (fun j : Fin k =>
      linnikVMTechFejerCoefficient
        (4 * (k * r * X ^ (j.val + 1)) + 1) (h j)) := by
  calc
    1 = Finset.univ.prod (fun _ : Fin k => (1 : Real)) := by simp
    _ <= Finset.univ.prod (fun j : Fin k =>
        linnikVMTechFejerCoefficient
          (4 * (k * r * X ^ (j.val + 1)) + 1) (h j)) := by
      apply Finset.prod_le_prod
      next =>
        intro j hj
        exact zero_le_one
      next =>
        intro j hj
        exact linnikVMTechDifferenceRange_fejerCoefficient_one_le
          k r X h hh j

theorem linnik_vmtech_difference_sum_le_fejer_weighted_sum
    (k r X : Nat) (F : (Fin k -> Int) -> Real)
    (hF : forall h, Membership.mem (linnikVMTechDifferenceRange k r X) h ->
      0 <= F h) :
    (linnikVMTechDifferenceRange k r X).sum F <=
      (linnikVMTechDifferenceRange k r X).sum (fun h =>
        (Finset.univ.prod (fun j : Fin k =>
          linnikVMTechFejerCoefficient
            (4 * (k * r * X ^ (j.val + 1)) + 1) (h j))) * F h) := by
  apply Finset.sum_le_sum
  intro h hh
  calc
    F h = 1 * F h := by ring
    _ <= (Finset.univ.prod (fun j : Fin k =>
        linnikVMTechFejerCoefficient
          (4 * (k * r * X ^ (j.val + 1)) + 1) (h j))) * F h :=
      mul_le_mul_of_nonneg_right
        (linnikVMTechDifferenceRange_fejerCoefficient_product_one_le
          k r X h hh) (hF h hh)

abbrev linnikVMTechFejerChoice
    {k : Nat} (H : Fin k -> Nat) : Type :=
  (j : Fin k) ->
    {h : Int // Membership.mem (linnikVMTechFejerDifferenceRange (H j)) h}

noncomputable def linnikVMTechFejerChoiceOfDifference
    (k r X : Nat)
    (h : {g : Fin k -> Int //
      Membership.mem (linnikVMTechDifferenceRange k r X) g}) :
    linnikVMTechFejerChoice
      (fun j : Fin k => 4 * (k * r * X ^ (j.val + 1)) + 1) :=
  fun j => Subtype.mk (h.val j)
    (linnikVMTechDifferenceRange_mem_fejerDifferenceRange
      k r X h.val h.property j)

theorem linnikVMTechFejerChoiceOfDifference_injective
    (k r X : Nat) :
    Function.Injective (linnikVMTechFejerChoiceOfDifference k r X) := by
  intro h g heq
  apply Subtype.ext
  funext j
  exact congrArg Subtype.val (congrFun heq j)

theorem linnikVMTechFejerCoefficient_nonneg (H : Nat) (h : Int) :
    0 <= linnikVMTechFejerCoefficient H h := by
  unfold linnikVMTechFejerCoefficient
  positivity

noncomputable def linnikVMTechFejerWeight
    (k r X : Nat) (F : (Fin k -> Int) -> Real)
    (h : linnikVMTechFejerChoice
      (fun j : Fin k => 4 * (k * r * X ^ (j.val + 1)) + 1)) : Real :=
  (Finset.univ.prod (fun j : Fin k =>
    linnikVMTechFejerCoefficient
      (4 * (k * r * X ^ (j.val + 1)) + 1) (h j).val)) *
    F (fun j => (h j).val)

theorem linnik_vmtech_weighted_difference_sum_le_fejer_choice_sum
    (k r X : Nat) (F : (Fin k -> Int) -> Real)
    (hF : forall h, 0 <= F h) :
    (linnikVMTechDifferenceRange k r X).sum (fun h =>
        (Finset.univ.prod (fun j : Fin k =>
          linnikVMTechFejerCoefficient
            (4 * (k * r * X ^ (j.val + 1)) + 1) (h j))) * F h) <=
      Finset.univ.sum (linnikVMTechFejerWeight k r X F) := by
  rw [<- Finset.sum_attach]
  change
    (linnikVMTechDifferenceRange k r X).attach.sum (fun h =>
        linnikVMTechFejerWeight k r X F
          (linnikVMTechFejerChoiceOfDifference k r X h)) <=
      Finset.univ.sum (linnikVMTechFejerWeight k r X F)
  rw [<- Finset.sum_image]
  next =>
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro h hh hnot
    unfold linnikVMTechFejerWeight
    apply mul_nonneg
    next =>
      apply Finset.prod_nonneg
      intro j hj
      exact linnikVMTechFejerCoefficient_nonneg _ _
    next =>
      exact hF _
  next =>
    intro h hh g hg heq
    exact linnikVMTechFejerChoiceOfDifference_injective k r X heq

theorem linnik_vmtech_fejer_product_expansion
    {k : Nat} (H : Fin k -> Nat) (t : Fin k -> Real) :
    ((Finset.univ.prod (fun j : Fin k =>
      2 * finiteFejerKernel (H j) (t j)) : Real) : Complex) =
      Finset.univ.sum (fun h : linnikVMTechFejerChoice H =>
        Finset.univ.prod (fun j : Fin k =>
          (linnikVMTechFejerCoefficient (H j) (h j).val : Complex) *
            Complex.exp
              (Complex.I * ((h j).val : Complex) * (t j : Complex)))) := by
  have hcast :
      ((Finset.univ.prod (fun j : Fin k =>
        2 * finiteFejerKernel (H j) (t j)) : Real) : Complex) =
        Finset.univ.prod (fun j : Fin k =>
          (((2 * finiteFejerKernel (H j) (t j) : Real)) : Complex)) := by
    push_cast
    rfl
  rw [hcast]
  have hterm (j : Fin k) :
      (((2 * finiteFejerKernel (H j) (t j) : Real)) : Complex) =
        Finset.univ.sum (fun h :
          {x : Int // Membership.mem
            (linnikVMTechFejerDifferenceRange (H j)) x} =>
          (linnikVMTechFejerCoefficient (H j) h.val : Complex) *
            Complex.exp
              (Complex.I * (h.val : Complex) * (t j : Complex))) := by
    calc
      (((2 * finiteFejerKernel (H j) (t j) : Real)) : Complex) =
          (linnikVMTechFejerDifferenceRange (H j)).sum (fun h =>
            (linnikVMTechFejerCoefficient (H j) h : Complex) *
              Complex.exp
                (Complex.I * (h : Complex) * (t j : Complex))) :=
        linnik_vmtech_fejer_coefficient_expansion (H j) (t j)
      _ = Finset.univ.sum (fun h :
          {x : Int // Membership.mem
            (linnikVMTechFejerDifferenceRange (H j)) x} =>
          (linnikVMTechFejerCoefficient (H j) h.val : Complex) *
            Complex.exp
              (Complex.I * (h.val : Complex) * (t j : Complex))) := by
        exact Finset.sum_subtype
          (linnikVMTechFejerDifferenceRange (H j))
          (fun x => Iff.rfl) _
  simp_rw [hterm]
  exact (Fintype.prod_sum (fun (j : Fin k)
      (h : {x : Int // Membership.mem
        (linnikVMTechFejerDifferenceRange (H j)) x}) =>
    (linnikVMTechFejerCoefficient (H j) h.val : Complex) *
      Complex.exp
        (Complex.I * (h.val : Complex) * (t j : Complex))))

theorem linnik_vmtech_fejer_product_term_eq
    {k : Nat} (H : Fin k -> Nat) (t : Fin k -> Real)
    (h : linnikVMTechFejerChoice H) :
    Finset.univ.prod (fun j : Fin k =>
        (linnikVMTechFejerCoefficient (H j) (h j).val : Complex) *
          Complex.exp
            (Complex.I * ((h j).val : Complex) * (t j : Complex))) =
      ((Finset.univ.prod (fun j : Fin k =>
        linnikVMTechFejerCoefficient (H j) (h j).val) : Real) : Complex) *
        Complex.exp (Complex.I *
          ((Finset.univ.sum (fun j : Fin k =>
            ((h j).val : Real) * t j) : Real) : Complex)) := by
  rw [Finset.prod_mul_distrib, <- Complex.exp_sum]
  have hcoeff :
      Finset.univ.prod (fun j : Fin k =>
        (linnikVMTechFejerCoefficient (H j) (h j).val : Complex)) =
        ((Finset.univ.prod (fun j : Fin k =>
          linnikVMTechFejerCoefficient (H j) (h j).val) : Real) :
            Complex) := by
    push_cast
    rfl
  rw [hcoeff]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem linnik_vmtech_fejer_product_le_reciprocal
    {k : Nat} (H : Fin k -> Nat) (x : Fin k -> Real)
    (hH : forall j, 0 < H j) :
    Finset.univ.prod (fun j : Fin k =>
        2 * finiteFejerKernel (H j) (2 * Real.pi * x j)) <=
      Finset.univ.prod (fun j : Fin k =>
        2 * linnikReciprocalSquareKernel (H j : Real) (x j)) := by
  apply Finset.prod_le_prod
  next =>
    intro j hj
    exact mul_nonneg (by norm_num)
      (finiteFejerKernel_nonneg (H j) (2 * Real.pi * x j))
  next =>
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (finiteFejerKernel_two_pi_le_linnikReciprocalSquareKernel
        (H j) (hH j) (x j)) (by norm_num)

theorem linnik_vmtech_sum_fejer_product_expansion
    {Q : Type*} [Fintype Q] {k : Nat}
    (H : Fin k -> Nat) (t : Q -> Fin k -> Real) :
    ((Finset.univ.sum (fun q : Q =>
        Finset.univ.prod (fun j : Fin k =>
          2 * finiteFejerKernel (H j) (t q j))) : Real) : Complex) =
      Finset.univ.sum (fun h : linnikVMTechFejerChoice H =>
        ((Finset.univ.prod (fun j : Fin k =>
          linnikVMTechFejerCoefficient (H j) (h j).val) : Real) :
            Complex) *
          Finset.univ.sum (fun q : Q =>
            Complex.exp (Complex.I *
              ((Finset.univ.sum (fun j : Fin k =>
                ((h j).val : Real) * t q j) : Real) : Complex)))) := by
  calc
    ((Finset.univ.sum (fun q : Q =>
        Finset.univ.prod (fun j : Fin k =>
          2 * finiteFejerKernel (H j) (t q j))) : Real) : Complex) =
        Finset.univ.sum (fun q : Q =>
          ((Finset.univ.prod (fun j : Fin k =>
            2 * finiteFejerKernel (H j) (t q j)) : Real) : Complex)) := by
      push_cast
      rfl
    _ = Finset.univ.sum (fun q : Q =>
        Finset.univ.sum (fun h : linnikVMTechFejerChoice H =>
          Finset.univ.prod (fun j : Fin k =>
            (linnikVMTechFejerCoefficient (H j) (h j).val : Complex) *
              Complex.exp
                (Complex.I * ((h j).val : Complex) *
                  (t q j : Complex))))) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact linnik_vmtech_fejer_product_expansion H (t q)
    _ = Finset.univ.sum (fun h : linnikVMTechFejerChoice H =>
        ((Finset.univ.prod (fun j : Fin k =>
          linnikVMTechFejerCoefficient (H j) (h j).val) : Real) :
            Complex) *
          Finset.univ.sum (fun q : Q =>
            Complex.exp (Complex.I *
              ((Finset.univ.sum (fun j : Fin k =>
                ((h j).val : Real) * t q j) : Real) : Complex)))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      simp_rw [linnik_vmtech_fejer_product_term_eq]
      rw [Finset.mul_sum]
