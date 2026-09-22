/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMTechMoment

/-!
# Rectangular power-difference support

This module embeds the exact Vinogradov power-difference range into the
independent symmetric coordinate box dictated by its proved degree bounds.
The resulting product factorization is the final finite-support bridge needed
before applying the degreewise kernel estimate in Theorem 24.7.
-/

abbrev linnikVMTechDifferenceBox (k r L : Nat) : Type :=
  (j : Fin k) ->
    {h : Int // Membership.mem
      (Finset.Icc
        (-(k * r * L ^ (j.val + 1) : Int))
        (k * r * L ^ (j.val + 1) : Int)) h}

noncomputable def linnikVMTechDifferenceBoxOfRange
    (k r L : Nat)
    (h : {g : Fin k -> Int //
      Membership.mem (linnikVMTechDifferenceRange k r L) g}) :
    linnikVMTechDifferenceBox k r L := fun j => by
  have habs := linnikVMTechDifferenceRange_abs_le k r L h.val h.property j
  have hboundsReal : And
      (-((k * r * L ^ (j.val + 1) : Nat) : Real) <= (h.val j : Real))
      ((h.val j : Real) <= (k * r * L ^ (j.val + 1) : Nat)) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow] at habs
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    exact abs_le.mp habs
  have hlow : -(k * r * L ^ (j.val + 1) : Int) <= h.val j := by
    exact_mod_cast hboundsReal.1
  have hhigh : h.val j <= (k * r * L ^ (j.val + 1) : Int) := by
    exact_mod_cast hboundsReal.2
  exact Subtype.mk (h.val j) (Finset.mem_Icc.mpr (And.intro hlow hhigh))

theorem linnikVMTechDifferenceBoxOfRange_injective
    (k r L : Nat) :
    Function.Injective (linnikVMTechDifferenceBoxOfRange k r L) := by
  intro h g heq
  apply Subtype.ext
  funext j
  exact congrArg Subtype.val (congrFun heq j)

theorem linnik_vmtech_difference_sum_le_box_sum
    (k r L : Nat) (F : (Fin k -> Int) -> Real)
    (hF : forall h, 0 <= F h) :
    (linnikVMTechDifferenceRange k r L).sum F <=
      Finset.univ.sum (fun h : linnikVMTechDifferenceBox k r L =>
        F (fun j => (h j).val)) := by
  rw [<- Finset.sum_attach]
  let embed := linnikVMTechDifferenceBoxOfRange k r L
  let G : linnikVMTechDifferenceBox k r L -> Real := fun h =>
    F (fun j => (h j).val)
  change
    (linnikVMTechDifferenceRange k r L).attach.sum (fun h => G (embed h)) <=
      Finset.univ.sum G
  rw [<- Finset.sum_image]
  all_goals
    first
    | apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro h hh hnot
      unfold G
      exact hF _
    | intro h hh g hg heq
      unfold embed at heq
      exact linnikVMTechDifferenceBoxOfRange_injective k r L heq

theorem linnik_vmtech_difference_box_sum_prod
    (k r L : Nat) (f : (j : Fin k) -> Int -> Real) :
    Finset.univ.sum (fun h : linnikVMTechDifferenceBox k r L =>
        Finset.univ.prod (fun j : Fin k => f j (h j).val)) =
      Finset.univ.prod (fun j : Fin k =>
        (Finset.Icc
          (-(k * r * L ^ (j.val + 1) : Int))
          (k * r * L ^ (j.val + 1) : Int)).sum (f j)) := by
  calc
    Finset.univ.sum (fun h : linnikVMTechDifferenceBox k r L =>
        Finset.univ.prod (fun j : Fin k => f j (h j).val)) =
      Finset.univ.prod (fun j : Fin k =>
        Finset.univ.sum (fun h :
          {x : Int // Membership.mem
            (Finset.Icc
              (-(k * r * L ^ (j.val + 1) : Int))
              (k * r * L ^ (j.val + 1) : Int)) x} => f j h.val)) := by
      exact (Fintype.prod_sum (fun (j : Fin k)
        (h : {x : Int // Membership.mem
          (Finset.Icc
            (-(k * r * L ^ (j.val + 1) : Int))
            (k * r * L ^ (j.val + 1) : Int)) x}) => f j h.val)).symm
    _ = Finset.univ.prod (fun j : Fin k =>
        (Finset.Icc
          (-(k * r * L ^ (j.val + 1) : Int))
          (k * r * L ^ (j.val + 1) : Int)).sum (f j)) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact (Finset.sum_subtype
        (Finset.Icc
          (-(k * r * L ^ (j.val + 1) : Int))
          (k * r * L ^ (j.val + 1) : Int))
        (fun x => Iff.rfl) (f j)).symm

theorem linnik_vmtech_kernel_difference_sum_le_box_product
    (k r X L : Nat) (alpha : Fin k -> Real) :
    (linnikVMTechDifferenceRange k r L).sum (fun h =>
        Finset.univ.prod (fun j : Fin k =>
          2 * linnikReciprocalSquareKernel
            (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
            (alpha j * (h j : Real)))) <=
      Finset.univ.prod (fun j : Fin k =>
        (Finset.Icc
          (-(k * r * L ^ (j.val + 1) : Int))
          (k * r * L ^ (j.val + 1) : Int)).sum (fun h =>
            2 * linnikReciprocalSquareKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
              (alpha j * (h : Real)))) := by
  let f : (j : Fin k) -> Int -> Real := fun j h =>
    2 * linnikReciprocalSquareKernel
      (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
      (alpha j * (h : Real))
  let F : (Fin k -> Int) -> Real := fun h =>
    Finset.univ.prod (fun j : Fin k => f j (h j))
  have hF : forall h, 0 <= F h := by
    intro h
    unfold F f
    apply Finset.prod_nonneg
    intro j hj
    apply mul_nonneg (by norm_num)
    exact linnikReciprocalSquareKernel_nonneg _ _ (by positivity)
  calc
    (linnikVMTechDifferenceRange k r L).sum (fun h =>
        Finset.univ.prod (fun j : Fin k =>
          2 * linnikReciprocalSquareKernel
            (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
            (alpha j * (h j : Real)))) =
      (linnikVMTechDifferenceRange k r L).sum F := by rfl
    _ <= Finset.univ.sum (fun h : linnikVMTechDifferenceBox k r L =>
        F (fun j => (h j).val)) :=
      linnik_vmtech_difference_sum_le_box_sum k r L F hF
    _ = Finset.univ.prod (fun j : Fin k =>
        (Finset.Icc
          (-(k * r * L ^ (j.val + 1) : Int))
          (k * r * L ^ (j.val + 1) : Int)).sum (fun h =>
            2 * linnikReciprocalSquareKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
              (alpha j * (h : Real)))) := by
      exact linnik_vmtech_difference_box_sum_prod k r L f

noncomputable def linnikVMTechIntAbsFiber (B n : Nat) : Finset Int :=
  (Finset.Icc (-(B : Int)) (B : Int)).filter
    (fun h => h.natAbs = n)

theorem linnik_vmtech_int_Icc_sum_group_by_natAbs
    (B : Nat) (f : Int -> Real) :
    (Finset.Icc (-(B : Int)) (B : Int)).sum f =
      (Finset.range (B + 1)).sum (fun n =>
        (linnikVMTechIntAbsFiber B n).sum f) := by
  let s := Finset.Icc (-(B : Int)) (B : Int)
  let g : Int -> Nat := Int.natAbs
  have hmaps : forall h, Membership.mem s h ->
      Membership.mem (Finset.range (B + 1)) (g h) := by
    intro h hh
    have hbounds := Finset.mem_Icc.mp hh
    rw [Finset.mem_range]
    change h.natAbs < B + 1
    obtain heq | heq := Int.natAbs_eq h
    case inl =>
      rw [heq] at hbounds
      have hle : h.natAbs <= B := by
        exact_mod_cast hbounds.2
      omega
    case inr =>
      rw [heq] at hbounds
      have hleInt : (h.natAbs : Int) <= (B : Int) := by omega
      have hle : h.natAbs <= B := by exact_mod_cast hleInt
      omega
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps f
  rw [<- hgroup]
  rfl

theorem linnikVMTechIntAbsFiber_card_le_two (B n : Nat) :
    (linnikVMTechIntAbsFiber B n).card <= 2 := by
  have hsub : linnikVMTechIntAbsFiber B n <=
      ({(n : Int), -(n : Int)} : Finset Int) := by
    intro h hh
    have hn := (Finset.mem_filter.mp hh).2
    obtain heq | heq := Int.natAbs_eq h
    case inl =>
      rw [heq, hn]
      simp
    case inr =>
      rw [heq, hn]
      simp
  calc
    (linnikVMTechIntAbsFiber B n).card <=
        ({(n : Int), -(n : Int)} : Finset Int).card :=
      Finset.card_le_card hsub
    _ <= 2 := Finset.card_le_two

theorem linnik_vmtech_int_Icc_sum_le_two_mul_range_sum
    (B : Nat) (f : Int -> Real)
    (hf : forall h, 0 <= f h)
    (heven : forall h, f (-h) = f h) :
    (Finset.Icc (-(B : Int)) (B : Int)).sum f <=
      2 * (Finset.range (B + 1)).sum (fun n => f (n : Int)) := by
  rw [linnik_vmtech_int_Icc_sum_group_by_natAbs]
  calc
    (Finset.range (B + 1)).sum (fun n =>
        (linnikVMTechIntAbsFiber B n).sum f) <=
      (Finset.range (B + 1)).sum (fun n => 2 * f (n : Int)) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        (linnikVMTechIntAbsFiber B n).sum f =
            (linnikVMTechIntAbsFiber B n).sum
              (fun _ => f (n : Int)) := by
          apply Finset.sum_congr rfl
          intro h hh
          have hnabs := (Finset.mem_filter.mp hh).2
          obtain heq | heq := Int.natAbs_eq h
          case inl =>
            rw [heq, hnabs]
          case inr =>
            rw [heq, hnabs, heven]
        _ = ((linnikVMTechIntAbsFiber B n).card : Real) *
            f (n : Int) := by simp
        _ <= 2 * f (n : Int) := by
          have hcardReal :
              ((linnikVMTechIntAbsFiber B n).card : Real) <= 2 := by
            exact_mod_cast linnikVMTechIntAbsFiber_card_le_two B n
          exact mul_le_mul_of_nonneg_right hcardReal (hf (n : Int))
    _ = 2 * (Finset.range (B + 1)).sum (fun n => f (n : Int)) := by
      rw [Finset.mul_sum]

theorem linnikReciprocalSquareKernel_neg (Y x : Real) :
    linnikReciprocalSquareKernel Y (-x) =
      linnikReciprocalSquareKernel Y x := by
  unfold linnikReciprocalSquareKernel
  rw [linnikNearestIntDist_neg]

theorem linnik_vmtech_reciprocal_Icc_sum_le_range_sum
    (B : Nat) (Y alpha : Real) (hY : 0 <= Y) :
    (Finset.Icc (-(B : Int)) (B : Int)).sum (fun h =>
        2 * linnikReciprocalSquareKernel Y (alpha * (h : Real))) <=
      2 * (Finset.range (B + 1)).sum (fun n =>
        2 * linnikReciprocalSquareKernel Y (alpha * (n : Real))) := by
  have hbound := linnik_vmtech_int_Icc_sum_le_two_mul_range_sum B
    (fun h : Int =>
      2 * linnikReciprocalSquareKernel Y (alpha * (h : Real)))
    (by
      intro h
      exact mul_nonneg (by norm_num)
        (linnikReciprocalSquareKernel_nonneg Y _ hY))
    (by
      intro h
      rw [Int.cast_neg]
      rw [show alpha * -(h : Real) = -(alpha * (h : Real)) by ring]
      rw [linnikReciprocalSquareKernel_neg])
  exact hbound

theorem linnik_vmtech_kernel_difference_sum_le_range_product
    (k r X L : Nat) (alpha : Fin k -> Real) :
    (linnikVMTechDifferenceRange k r L).sum (fun h =>
        Finset.univ.prod (fun j : Fin k =>
          2 * linnikReciprocalSquareKernel
            (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
            (alpha j * (h j : Real)))) <=
      (2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
        2 * (Finset.range (k * r * L ^ (j.val + 1) + 1)).sum
          (fun n => linnikReciprocalSquareKernel
            (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
            ((n : Real) * alpha j))) := by
  calc
    (linnikVMTechDifferenceRange k r L).sum (fun h =>
        Finset.univ.prod (fun j : Fin k =>
          2 * linnikReciprocalSquareKernel
            (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
            (alpha j * (h j : Real)))) <=
      Finset.univ.prod (fun j : Fin k =>
        (Finset.Icc
          (-(k * r * L ^ (j.val + 1) : Int))
          (k * r * L ^ (j.val + 1) : Int)).sum (fun h =>
            2 * linnikReciprocalSquareKernel
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
              (alpha j * (h : Real)))) :=
      linnik_vmtech_kernel_difference_sum_le_box_product
        k r X L alpha
    _ <= Finset.univ.prod (fun j : Fin k =>
        2 * (Finset.range (k * r * L ^ (j.val + 1) + 1)).sum
          (fun n => 2 * linnikReciprocalSquareKernel
            (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
            (alpha j * (n : Real)))) := by
      apply Finset.prod_le_prod
      case h0 =>
        intro j hj
        apply Finset.sum_nonneg
        intro h hh
        exact mul_nonneg (by norm_num)
          (linnikReciprocalSquareKernel_nonneg _ _ (by positivity))
      case h1 =>
        intro j hj
        exact linnik_vmtech_reciprocal_Icc_sum_le_range_sum
          (k * r * L ^ (j.val + 1))
          (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
          (alpha j) (by positivity)
    _ = (2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
        2 * (Finset.range (k * r * L ^ (j.val + 1) + 1)).sum
          (fun n => linnikReciprocalSquareKernel
            (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
            ((n : Real) * alpha j))) := by
      simp_rw [mul_comm (alpha _) (_ : Real)]
      simp_rw [<- Finset.mul_sum]
      rw [Finset.prod_mul_distrib]
      simp

theorem linnik_vmtech_kernel_difference_sum_le_envelope
    (k r X L : Nat) (alpha theta : Fin k -> Real)
    (a q : Fin k -> Nat)
    (hq : forall j, 0 < q j)
    (hcop : forall j, Nat.Coprime (a j) (q j))
    (htheta : forall j, abs (theta j) <= 1)
    (halpha : forall j,
      alpha j = (a j : Real) / q j + theta j / (q j : Real) ^ 2) :
    (linnikVMTechDifferenceRange k r L).sum (fun h =>
        Finset.univ.prod (fun j : Fin k =>
          2 * linnikReciprocalSquareKernel
            (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)
            (alpha j * (h j : Real)))) <=
      (2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
        48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
          (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
            (k * r * L ^ (j.val + 1) + 1) +
            (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j)) := by
  have hproduct := linnik_kernel_product_envelope_le
    (Finset.univ : Finset (Fin k))
    (fun j : Fin k =>
      (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat))
    alpha theta a q
    (fun j : Fin k => k * r * L ^ (j.val + 1))
    (by
      intro j hj
      positivity)
    (by
      intro j hj
      exact hq j)
    (by
      intro j hj
      exact hcop j)
    (by
      intro j hj
      exact htheta j)
    (by
      intro j hj
      exact halpha j)
  have hrange := linnik_vmtech_kernel_difference_sum_le_range_product
    k r X L alpha
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_one, Nat.cast_ofNat] at hproduct hrange
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_one, Nat.cast_ofNat] using hrange.trans
      (mul_le_mul_of_nonneg_left hproduct (by positivity))

theorem linnik_vmtech_difference_moment_sum_le_envelope
    (k r X L : Nat) (alpha theta : Fin k -> Real)
    (a q : Fin k -> Nat)
    (hq : forall j, 0 < q j)
    (hcop : forall j, Nat.Coprime (a j) (q j))
    (htheta : forall j, abs (theta j) <= 1)
    (halpha : forall j,
      alpha j = (a j : Real) / q j + theta j / (q j : Real) ^ 2) :
    (linnikVMTechDifferenceRange k r X).sum
        (linnikVMTechDifferenceMoment alpha L (k * r)) <=
      (Finset.vinogradovMeanValue k (k * r) L : Real) *
        ((2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
          48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
            (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
              (k * r * L ^ (j.val + 1) + 1) +
              (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j))) := by
  have hmoment := linnik_vmtech_difference_moment_sum_le_vmvt_mul_kernel_sum
    k r X L alpha
  have hkernel := linnik_vmtech_kernel_difference_sum_le_envelope
    k r X L alpha theta a q hq hcop htheta halpha
  exact hmoment.trans
    (mul_le_mul_of_nonneg_left hkernel (by positivity))
