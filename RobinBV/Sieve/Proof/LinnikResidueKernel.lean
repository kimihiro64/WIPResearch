/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Data.Nat.ModEq
import RobinBV.Sieve.Proof.LinnikTechnicalInequality

/-!
# Rational residue kernel for Linnik's technical inequality

This module bounds one complete rational residue block in the proof of
Montgomery--Vaughan Lemma 24.6.  The reciprocal-square kernel is defined with
its singular value filled by `Y`, matching the mathematical convention in the
source minimum.  Reflection of the nonzero residues and the finite p-series
bound give the explicit block estimate `Y + 4*q^2/Y`.

The affine residue theorem below permutes every coprime translate into the
canonical range.  Its next consumer adds the rational-approximation perturbation
and assembles the full `X`-range estimate.
-/

noncomputable def linnikReciprocalSquareKernel (Y x : Real) : Real :=
  if linnikNearestIntDist x = 0 then Y
  else min Y (1 / (Y * linnikNearestIntDist x ^ 2))

theorem linnik_rational_kernel_le_pair
    (Y : Real) (r q : Nat) (hY : 0 < Y) (hr : 0 < r) (hrq : r < q) :
    linnikReciprocalSquareKernel Y ((r : Real) / q) <=
      (q : Real) ^ 2 / Y *
        (1 / (r : Real) ^ 2 + 1 / ((q - r : Nat) : Real) ^ 2) := by
  have hq : 0 < q := lt_trans hr hrq
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hrReal : 0 < (r : Real) := by exact_mod_cast hr
  have hqr : 0 < q - r := Nat.sub_pos_of_lt hrq
  have hqrReal : 0 < ((q - r : Nat) : Real) := by exact_mod_cast hqr
  have hdist : linnikNearestIntDist ((r : Real) / q) =
      ((min r (q - r) : Nat) : Real) / q := by
    unfold linnikNearestIntDist
    rw [abs_sub_round_div_natCast_eq, Nat.mod_eq_of_lt hrq]
  have hmin : 0 < min r (q - r) := by omega
  have hdistPos : 0 < linnikNearestIntDist ((r : Real) / q) := by
    rw [hdist]
    positivity
  rw [linnikReciprocalSquareKernel, if_neg (ne_of_gt hdistPos)]
  apply le_trans (min_le_right _ _)
  rw [hdist]
  by_cases hle : r <= q - r
  next =>
    rw [min_eq_left hle]
    have heq : 1 / (Y * ((r : Real) / q) ^ 2) =
        (q : Real) ^ 2 / Y * (1 / (r : Real) ^ 2) := by
      field_simp
    rw [heq, mul_add]
    exact le_add_of_nonneg_right (by positivity)
  next =>
    have hrev : q - r <= r := Nat.le_of_not_ge hle
    rw [min_eq_right hrev]
    have hcast : (((q - r : Nat) : Real) / q) =
        ((q : Real) - r) / q := by
      rw [Nat.cast_sub (Nat.le_of_lt hrq)]
    rw [hcast]
    have heq : 1 / (Y * (((q : Real) - r) / q) ^ 2) =
        (q : Real) ^ 2 / Y * (1 / (((q : Real) - r) ^ 2)) := by
      field_simp
    rw [heq, mul_add]
    have hcastSub : (q : Real) - r = ((q - r : Nat) : Real) := by
      rw [Nat.cast_sub (Nat.le_of_lt hrq)]
    rw [hcastSub]
    exact le_add_of_nonneg_left (by positivity)

theorem linnik_sum_Ioo_inv_sq_lt_le_two (q : Nat) (hq : 0 < q) :
    Finset.sum (Finset.Ioo 0 q)
      (fun r => 1 / (r : Real) ^ 2) <= 2 := by
  simpa [Nat.sub_add_cancel hq] using
    (linnik_sum_Ioo_inv_sq_le_two (q - 1))

theorem linnik_sum_Ioo_sub_inv_sq_eq (q : Nat) :
    Finset.sum (Finset.Ioo 0 q)
        (fun r => 1 / ((q - r : Nat) : Real) ^ 2) =
      Finset.sum (Finset.Ioo 0 q)
        (fun r => 1 / (r : Real) ^ 2) := by
  apply Finset.sum_bij'
    (fun r _ => q - r) (fun r _ => q - r)
  next =>
    intro r hr
    simp only [Finset.mem_Ioo] at hr
    simp only [Finset.mem_Ioo]
    omega
  next =>
    intro r hr
    simp only [Finset.mem_Ioo] at hr
    simp only [Finset.mem_Ioo]
    omega
  next =>
    intro r hr
    simp only [Finset.mem_Ioo] at hr
    omega
  next =>
    intro r hr
    simp only [Finset.mem_Ioo] at hr
    omega
  next =>
    intro r hr
    rfl

theorem linnik_rational_nonzero_kernel_sum_le
    (Y : Real) (q : Nat) (hY : 0 < Y) (hq : 0 < q) :
    Finset.sum (Finset.Ioo 0 q)
        (fun r => linnikReciprocalSquareKernel Y ((r : Real) / q)) <=
      4 * (q : Real) ^ 2 / Y := by
  have hfactor : 0 <= (q : Real) ^ 2 / Y := by positivity
  calc
    Finset.sum (Finset.Ioo 0 q)
        (fun r => linnikReciprocalSquareKernel Y ((r : Real) / q)) <=
        Finset.sum (Finset.Ioo 0 q) (fun r =>
          (q : Real) ^ 2 / Y *
            (1 / (r : Real) ^ 2 + 1 / ((q - r : Nat) : Real) ^ 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      simp only [Finset.mem_Ioo] at hr
      exact linnik_rational_kernel_le_pair Y r q hY hr.1 hr.2
    _ = (q : Real) ^ 2 / Y *
        (Finset.sum (Finset.Ioo 0 q) (fun r => 1 / (r : Real) ^ 2) +
          Finset.sum (Finset.Ioo 0 q)
            (fun r => 1 / ((q - r : Nat) : Real) ^ 2)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
    _ = (q : Real) ^ 2 / Y *
        (2 * Finset.sum (Finset.Ioo 0 q)
          (fun r => 1 / (r : Real) ^ 2)) := by
      rw [linnik_sum_Ioo_sub_inv_sq_eq]
      ring
    _ <= (q : Real) ^ 2 / Y * (2 * 2) := by
      gcongr
      exact linnik_sum_Ioo_inv_sq_lt_le_two q hq
    _ = 4 * (q : Real) ^ 2 / Y := by ring

theorem linnik_rational_residue_kernel_sum_le
    (Y : Real) (q : Nat) (hY : 0 < Y) (hq : 0 < q) :
    Finset.sum (Finset.range q)
        (fun r => linnikReciprocalSquareKernel Y ((r : Real) / q)) <=
      Y + 4 * (q : Real) ^ 2 / Y := by
  have hrange : Finset.range q = Insert.insert 0 (Finset.Ioo 0 q) := by
    ext r
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  have hzero : linnikReciprocalSquareKernel Y (((0 : Nat) : Real) / q) = Y := by
    simp [linnikReciprocalSquareKernel, linnikNearestIntDist]
  rw [hzero]
  exact _root_.add_le_add le_rfl
    (linnik_rational_nonzero_kernel_sum_le Y q hY hq)

theorem linnikReciprocalSquareKernel_nonneg
    (Y x : Real) (hY : 0 <= Y) :
    0 <= linnikReciprocalSquareKernel Y x := by
  unfold linnikReciprocalSquareKernel
  split
  next => exact hY
  next => exact le_min hY (by positivity)

theorem linnik_affine_residue_injective_on
    (a c q : Nat) (hcop : Nat.Coprime a q) :
    forall r, Membership.mem (Finset.range q) r ->
      forall s, Membership.mem (Finset.range q) s ->
        (a * r + c) % q = (a * s + c) % q -> r = s := by
  intro r hr s hs heq
  have hsum : Nat.ModEq q (a * r + c) (a * s + c) := by
    exact heq
  have hmul : Nat.ModEq q (a * r) (a * s) :=
    Nat.ModEq.add_right_cancel' c hsum
  have hbase : Nat.ModEq q r s :=
    Nat.ModEq.cancel_left_of_coprime hcop.symm hmul
  exact hbase.eq_of_lt_of_lt (Finset.mem_range.mp hr) (Finset.mem_range.mp hs)

theorem linnik_affine_rational_residue_kernel_sum_le
    (Y : Real) (a c q : Nat) (hY : 0 < Y) (hq : 0 < q)
    (hcop : Nat.Coprime a q) :
    Finset.sum (Finset.range q) (fun r =>
        linnikReciprocalSquareKernel Y
          ((((a * r + c) % q : Nat) : Real) / q)) <=
      Y + 4 * (q : Real) ^ 2 / Y := by
  let f : Nat -> Nat := fun r => (a * r + c) % q
  have hinj : forall r, Membership.mem (Finset.range q) r ->
      forall s, Membership.mem (Finset.range q) s -> f r = f s -> r = s := by
    intro r hr s hs hrs
    exact linnik_affine_residue_injective_on a c q hcop r hr s hs hrs
  have hsubset : Finset.image f (Finset.range q) <= Finset.range q := by
    intro z hz
    rw [Finset.mem_image] at hz
    choose r hr hzr using hz
    rw [<- hzr]
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
  have himage : Finset.sum (Finset.image f (Finset.range q)) (fun z =>
      linnikReciprocalSquareKernel Y ((z : Real) / q)) =
      Finset.sum (Finset.range q) (fun r =>
        linnikReciprocalSquareKernel Y ((f r : Real) / q)) := by
    rw [Finset.sum_image]
    exact hinj
  calc
    Finset.sum (Finset.range q) (fun r =>
        linnikReciprocalSquareKernel Y
          ((((a * r + c) % q : Nat) : Real) / q)) =
        Finset.sum (Finset.image f (Finset.range q)) (fun z =>
          linnikReciprocalSquareKernel Y ((z : Real) / q)) := by
      exact himage.symm
    _ <= Finset.sum (Finset.range q) (fun z =>
        linnikReciprocalSquareKernel Y ((z : Real) / q)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro z hz hznot
      exact linnikReciprocalSquareKernel_nonneg Y ((z : Real) / q) hY.le
    _ <= Y + 4 * (q : Real) ^ 2 / Y :=
      linnik_rational_residue_kernel_sum_le Y q hY hq

theorem linnikReciprocalSquareKernel_le_four_of_close
    (Y x y : Real) (q : Nat) (hY : 0 < Y) (hq : 0 < q)
    (hy : 2 / (q : Real) <= linnikNearestIntDist y)
    (hxy : abs (x - y) <= 1 / (q : Real)) :
    linnikReciprocalSquareKernel Y x <=
      4 * linnikReciprocalSquareKernel Y y := by
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hyPos : 0 < linnikNearestIntDist y := by
    have htwo : 0 < 2 / (q : Real) := by positivity
    exact lt_of_lt_of_le htwo hy
  have hone : 1 / (q : Real) <= linnikNearestIntDist y / 2 := by
    have htwoEq : 2 / (q : Real) = 2 * (1 / (q : Real)) := by ring
    rw [htwoEq] at hy
    nlinarith
  have hlip := linnikNearestIntDist_sub_abs_le x y
  have habs : abs (y - x) = abs (x - y) := by rw [abs_sub_comm]
  rw [habs] at hlip
  have hhalf : linnikNearestIntDist y / 2 <= linnikNearestIntDist x := by
    linarith
  have hxPos : 0 < linnikNearestIntDist x := by
    nlinarith
  rw [linnikReciprocalSquareKernel, if_neg (ne_of_gt hxPos),
    linnikReciprocalSquareKernel, if_neg (ne_of_gt hyPos)]
  by_cases htrunc : Y <= 1 / (Y * linnikNearestIntDist y ^ 2)
  next =>
    rw [min_eq_left htrunc]
    calc
      min Y (1 / (Y * linnikNearestIntDist x ^ 2)) <= Y := min_le_left _ _
      _ <= 4 * Y := by nlinarith
  next =>
    have hyKernel : 1 / (Y * linnikNearestIntDist y ^ 2) <= Y :=
      le_of_not_ge htrunc
    rw [min_eq_right hyKernel]
    apply le_trans (min_le_right _ _)
    have hsum : 0 <= linnikNearestIntDist x +
        linnikNearestIntDist y / 2 := by positivity
    have hprod : 0 <=
        (linnikNearestIntDist x - linnikNearestIntDist y / 2) *
          (linnikNearestIntDist x + linnikNearestIntDist y / 2) :=
      mul_nonneg (sub_nonneg.mpr hhalf) hsum
    have hsquare : linnikNearestIntDist y ^ 2 / 4 <=
        linnikNearestIntDist x ^ 2 := by
      nlinarith
    have hden : (Y * linnikNearestIntDist y ^ 2) / 4 <=
        Y * linnikNearestIntDist x ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsquare hY.le
      nlinarith
    have hrecip := one_div_le_one_div_of_le
      (by positivity : 0 < (Y * linnikNearestIntDist y ^ 2) / 4) hden
    calc
      1 / (Y * linnikNearestIntDist x ^ 2) <=
          1 / ((Y * linnikNearestIntDist y ^ 2) / 4) := hrecip
      _ = 4 * (1 / (Y * linnikNearestIntDist y ^ 2)) := by
        field_simp

noncomputable def linnikOneSidedResidueKernel
    (Y : Real) (q r : Nat) : Real :=
  min Y ((q : Real) ^ 2 / (Y * (r : Real) ^ 2))

theorem linnikOneSidedResidueKernel_nonneg
    (Y : Real) (q r : Nat) (hY : 0 <= Y) :
    0 <= linnikOneSidedResidueKernel Y q r := by
  unfold linnikOneSidedResidueKernel
  exact le_min hY (by positivity)

theorem linnikOneSidedResidueKernel_le_left
    (Y : Real) (q r : Nat) :
    linnikOneSidedResidueKernel Y q r <= Y := by
  unfold linnikOneSidedResidueKernel
  exact min_le_left _ _

theorem linnikOneSidedResidueKernel_le_reciprocal
    (Y : Real) (q r : Nat) :
    linnikOneSidedResidueKernel Y q r <=
      (q : Real) ^ 2 / Y * (1 / (r : Real) ^ 2) := by
  unfold linnikOneSidedResidueKernel
  apply le_trans (min_le_right _ _)
  ring_nf
  exact le_rfl

theorem linnik_rational_kernel_le_truncated_pair
    (Y : Real) (r q : Nat) (hY : 0 < Y) (hr : 0 < r) (hrq : r < q) :
    linnikReciprocalSquareKernel Y ((r : Real) / q) <=
      linnikOneSidedResidueKernel Y q r +
        linnikOneSidedResidueKernel Y q (q - r) := by
  have hq : 0 < q := lt_trans hr hrq
  have hdist : linnikNearestIntDist ((r : Real) / q) =
      ((min r (q - r) : Nat) : Real) / q := by
    unfold linnikNearestIntDist
    rw [abs_sub_round_div_natCast_eq, Nat.mod_eq_of_lt hrq]
  have hmin : 0 < min r (q - r) := by omega
  have hdistPos : 0 < linnikNearestIntDist ((r : Real) / q) := by
    rw [hdist]
    positivity
  rw [linnikReciprocalSquareKernel, if_neg (ne_of_gt hdistPos), hdist]
  by_cases hle : r <= q - r
  next =>
    rw [min_eq_left hle]
    have heq : 1 / (Y * ((r : Real) / q) ^ 2) =
        (q : Real) ^ 2 / (Y * (r : Real) ^ 2) := by
      field_simp
    rw [heq]
    exact le_add_of_nonneg_right
      (linnikOneSidedResidueKernel_nonneg Y q (q - r) hY.le)
  next =>
    have hrev : q - r <= r := Nat.le_of_not_ge hle
    rw [min_eq_right hrev]
    have hcast : (((q - r : Nat) : Real) / q) =
        ((q : Real) - r) / q := by
      rw [Nat.cast_sub (Nat.le_of_lt hrq)]
    rw [hcast]
    have heq : 1 / (Y * (((q : Real) - r) / q) ^ 2) =
        (q : Real) ^ 2 / (Y * (((q - r : Nat) : Real) ^ 2)) := by
      rw [Nat.cast_sub (Nat.le_of_lt hrq)]
      field_simp
    rw [heq]
    exact le_add_of_nonneg_left
      (linnikOneSidedResidueKernel_nonneg Y q r hY.le)

theorem linnik_one_sided_residue_sum_le
    (Y : Real) (q R : Nat) (hY : 0 < Y) :
    Finset.sum (Finset.Ioo 0 q)
        (fun r => linnikOneSidedResidueKernel Y q r) <=
      Y * (R : Real) +
        2 * (q : Real) ^ 2 / (Y * ((R : Real) + 1)) := by
  let low := (Finset.Ioo 0 q).filter (fun r => r <= R)
  let high := (Finset.Ioo 0 q).filter (fun r => Not (r <= R))
  have hlowSubset : low <= Finset.Icc 1 R := by
    intro r hr
    have hrParts := Finset.mem_filter.mp hr
    simp only [Finset.mem_Ioo] at hrParts
    simp only [Finset.mem_Icc]
    omega
  have hlowCard : low.card <= R := by
    calc
      low.card <= (Finset.Icc 1 R).card := Finset.card_le_card hlowSubset
      _ = R := by simp
  have hlowCardReal : (low.card : Real) <= R := by exact_mod_cast hlowCard
  have hlow : Finset.sum low
      (fun r => linnikOneSidedResidueKernel Y q r) <= Y * (R : Real) := by
    calc
      Finset.sum low (fun r => linnikOneSidedResidueKernel Y q r) <=
          Finset.sum low (fun _ => Y) := by
        apply Finset.sum_le_sum
        intro r hr
        exact linnikOneSidedResidueKernel_le_left Y q r
      _ = (low.card : Real) * Y := by simp
      _ <= (R : Real) * Y :=
        mul_le_mul_of_nonneg_right hlowCardReal hY.le
      _ = Y * (R : Real) := by ring
  have hhighEq : high = Finset.Ioo R q := by
    ext r
    simp only [high, Finset.mem_filter, Finset.mem_Ioo]
    omega
  have hfactor : 0 <= (q : Real) ^ 2 / Y := by positivity
  have hhigh : Finset.sum high
      (fun r => linnikOneSidedResidueKernel Y q r) <=
      2 * (q : Real) ^ 2 / (Y * ((R : Real) + 1)) := by
    calc
      Finset.sum high (fun r => linnikOneSidedResidueKernel Y q r) <=
          Finset.sum high (fun r =>
            (q : Real) ^ 2 / Y * (1 / (r : Real) ^ 2)) := by
        apply Finset.sum_le_sum
        intro r hr
        exact linnikOneSidedResidueKernel_le_reciprocal Y q r
      _ = (q : Real) ^ 2 / Y *
          Finset.sum high (fun r => 1 / (r : Real) ^ 2) := by
        rw [Finset.mul_sum]
      _ = (q : Real) ^ 2 / Y *
          Finset.sum (Finset.Ioo R q) (fun r => 1 / (r : Real) ^ 2) := by
        rw [hhighEq]
      _ <= (q : Real) ^ 2 / Y * (2 / ((R : Real) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hfactor
        simpa using sum_Ioo_inv_sq_le R q
      _ = 2 * (q : Real) ^ 2 / (Y * ((R : Real) + 1)) := by
        field_simp
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Ioo 0 q) (fun r => r <= R)
    (fun r => linnikOneSidedResidueKernel Y q r)
  have htotal : Finset.sum (Finset.Ioo 0 q)
      (fun r => linnikOneSidedResidueKernel Y q r) =
      Finset.sum low (fun r => linnikOneSidedResidueKernel Y q r) +
        Finset.sum high (fun r => linnikOneSidedResidueKernel Y q r) := by
    simpa [low, high] using hsplit.symm
  rw [htotal]
  exact _root_.add_le_add hlow hhigh

theorem linnik_one_sided_residue_sum_le_three_q
    (Y : Real) (q : Nat) (hY : 0 < Y) (hq : 0 < q) :
    Finset.sum (Finset.Ioo 0 q)
        (fun r => linnikOneSidedResidueKernel Y q r) <= 3 * (q : Real) := by
  let R := Nat.floor ((q : Real) / Y)
  have hratio : 0 <= (q : Real) / Y := by positivity
  have hfloor : (R : Real) <= (q : Real) / Y := by
    exact Nat.floor_le hratio
  have hlt : (q : Real) / Y < (R : Real) + 1 := by
    simpa [R] using Nat.lt_floor_add_one ((q : Real) / Y)
  have hfirst : Y * (R : Real) <= (q : Real) := by
    calc
      Y * (R : Real) <= Y * ((q : Real) / Y) :=
        mul_le_mul_of_nonneg_left hfloor hY.le
      _ = (q : Real) := by field_simp
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hqden : (q : Real) <= Y * ((R : Real) + 1) := by
    have hmul := mul_lt_mul_of_pos_left hlt hY
    have heq : Y * ((q : Real) / Y) = (q : Real) := by field_simp
    rw [heq] at hmul
    exact hmul.le
  have htailBase : (q : Real) ^ 2 /
      (Y * ((R : Real) + 1)) <= (q : Real) := by
    calc
      (q : Real) ^ 2 / (Y * ((R : Real) + 1)) <=
          (q : Real) ^ 2 / (q : Real) :=
        div_le_div_of_nonneg_left (sq_nonneg (q : Real)) hqReal hqden
      _ = (q : Real) := by field_simp
  have htail : 2 * (q : Real) ^ 2 /
      (Y * ((R : Real) + 1)) <= 2 * (q : Real) := by
    calc
      2 * (q : Real) ^ 2 / (Y * ((R : Real) + 1)) =
          2 * ((q : Real) ^ 2 / (Y * ((R : Real) + 1))) := by ring
      _ <= 2 * (q : Real) :=
        mul_le_mul_of_nonneg_left htailBase (by norm_num)
  have hsum := linnik_one_sided_residue_sum_le Y q R hY
  calc
    Finset.sum (Finset.Ioo 0 q)
        (fun r => linnikOneSidedResidueKernel Y q r) <=
        Y * (R : Real) +
          2 * (q : Real) ^ 2 / (Y * ((R : Real) + 1)) := hsum
    _ <= (q : Real) + 2 * (q : Real) := by
      exact _root_.add_le_add hfirst htail
    _ = 3 * (q : Real) := by ring
