/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Data.ZMod.Basic
import RobinBV.Sieve.Proof.LinnikSharpResidueKernel

/-!
# Perturbed rational blocks in Linnik's technical inequality

This module isolates the exact exceptional-residue packet in Montgomery--
Vaughan Lemma 24.6.  A rational residue can lie within `2/q` of an integer only
at `0`, `1`, or `q-1`; hence every complete block has at most three exceptional
positions.  The complementary residues meet the distance hypothesis of
`linnikReciprocalSquareKernel_le_four_of_close`.

The subsequent theorem combines this packet with the affine block estimate and
the rounded perturbation bound to control one complete approximate-rational
block.
-/

def linnikExceptionalResidues (q : Nat) : Finset Nat :=
  (Finset.range q).filter (fun z => Or (z < 2) (q - z < 2))

theorem linnikExceptionalResidues_subset_three (q : Nat) :
    linnikExceptionalResidues q <= {0, 1, q - 1} := by
  intro z hz
  have hzParts := Finset.mem_filter.mp hz
  have hzRange : z < q := Finset.mem_range.mp hzParts.1
  have hzClose : Or (z < 2) (q - z < 2) := hzParts.2
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hzClose with hleft | hright
  next =>
    omega
  next =>
    omega

theorem linnikExceptionalResidues_card_le_three (q : Nat) :
    (linnikExceptionalResidues q).card <= 3 := by
  exact (Finset.card_le_card (linnikExceptionalResidues_subset_three q)).trans
    Finset.card_le_three

theorem linnik_rational_residue_distance_ge_two
    (q z : Nat) (hq : 0 < q)
    (hz : Membership.mem (Finset.range q) z)
    (hzNot : Not (Membership.mem (linnikExceptionalResidues q) z)) :
    2 / (q : Real) <= linnikNearestIntDist ((z : Real) / q) := by
  have hzlt : z < q := Finset.mem_range.mp hz
  have hnot : Not (Or (z < 2) (q - z < 2)) := by
    intro hclose
    apply hzNot
    exact Finset.mem_filter.mpr (And.intro hz hclose)
  have hzTwo : 2 <= z := by omega
  have hqzTwo : 2 <= q - z := by omega
  have hmin : 2 <= min z (q - z) := le_min hzTwo hqzTwo
  have hdist : linnikNearestIntDist ((z : Real) / q) =
      ((min z (q - z) : Nat) : Real) / q := by
    unfold linnikNearestIntDist
    rw [abs_sub_round_div_natCast_eq, Nat.mod_eq_of_lt hzlt]
  rw [hdist]
  apply div_le_div_of_nonneg_right
  next => exact_mod_cast hmin
  next => positivity

def linnikExceptionalAffineIndices (a c q : Nat) : Finset Nat :=
  (Finset.range q).filter (fun r =>
    Membership.mem (linnikExceptionalResidues q) ((a * r + c) % q))

theorem linnikExceptionalAffineIndices_card_le_three
    (a c q : Nat) (hcop : Nat.Coprime a q) :
    (linnikExceptionalAffineIndices a c q).card <= 3 := by
  let f : Nat -> Nat := fun r => (a * r + c) % q
  have hinj : forall r,
      Membership.mem (linnikExceptionalAffineIndices a c q) r ->
      forall s, Membership.mem (linnikExceptionalAffineIndices a c q) s ->
        f r = f s -> r = s := by
    intro r hr s hs hrs
    have hrRange := (Finset.mem_filter.mp hr).1
    have hsRange := (Finset.mem_filter.mp hs).1
    exact linnik_affine_residue_injective_on a c q hcop
      r hrRange s hsRange hrs
  have hsubset : Finset.image f (linnikExceptionalAffineIndices a c q) <=
      linnikExceptionalResidues q := by
    intro z hz
    rw [Finset.mem_image] at hz
    choose r hr hzr using hz
    have hrExceptional := (Finset.mem_filter.mp hr).2
    rw [<- hzr]
    exact hrExceptional
  have hcard : (Finset.image f
      (linnikExceptionalAffineIndices a c q)).card =
      (linnikExceptionalAffineIndices a c q).card :=
    Finset.card_image_iff.mpr hinj
  calc
    (linnikExceptionalAffineIndices a c q).card =
        (Finset.image f (linnikExceptionalAffineIndices a c q)).card :=
      hcard.symm
    _ <= (linnikExceptionalResidues q).card := Finset.card_le_card hsubset
    _ <= 3 := linnikExceptionalResidues_card_le_three q

theorem linnikReciprocalSquareKernel_le_left (Y x : Real) :
    linnikReciprocalSquareKernel Y x <= Y := by
  unfold linnikReciprocalSquareKernel
  split
  next => exact le_rfl
  next => exact min_le_left _ _

theorem linnik_perturbed_affine_block_kernel_sum_le_of_rational_bound
    (Y M : Real) (a c q : Nat) (actual : Nat -> Real)
    (hY : 0 < Y) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hclose : forall r, Membership.mem (Finset.range q) r ->
      abs (actual r - ((((a * r + c) % q : Nat) : Real) / q)) <=
        1 / (q : Real))
    (hrational : Finset.sum (Finset.range q) (fun r =>
      linnikReciprocalSquareKernel Y
        ((((a * r + c) % q : Nat) : Real) / q)) <= M) :
    Finset.sum (Finset.range q)
        (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
      3 * Y + 4 * M := by
  let f : Nat -> Nat := fun r => (a * r + c) % q
  let bad := linnikExceptionalAffineIndices a c q
  let good := (Finset.range q).filter (fun r =>
    Not (Membership.mem (linnikExceptionalResidues q) (f r)))
  have hbadCard : bad.card <= 3 := by
    exact linnikExceptionalAffineIndices_card_le_three a c q hcop
  have hbadCardReal : (bad.card : Real) <= 3 := by exact_mod_cast hbadCard
  have hbad : Finset.sum bad
      (fun r => linnikReciprocalSquareKernel Y (actual r)) <= 3 * Y := by
    calc
      Finset.sum bad (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
          Finset.sum bad (fun _ => Y) := by
        apply Finset.sum_le_sum
        intro r hr
        exact linnikReciprocalSquareKernel_le_left Y (actual r)
      _ = (bad.card : Real) * Y := by simp
      _ <= 3 * Y := mul_le_mul_of_nonneg_right hbadCardReal hY.le
  have hgood : Finset.sum good
      (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
      4 * M := by
    calc
      Finset.sum good (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
          Finset.sum good (fun r => 4 *
            linnikReciprocalSquareKernel Y ((f r : Real) / q)) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrParts := Finset.mem_filter.mp hr
        have hrRange : Membership.mem (Finset.range q) r := hrParts.1
        have hzRange : Membership.mem (Finset.range q) (f r) := by
          exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
        have hzDist := linnik_rational_residue_distance_ge_two q (f r) hq
          hzRange hrParts.2
        apply linnikReciprocalSquareKernel_le_four_of_close Y
          (actual r) ((f r : Real) / q) q hY hq hzDist
        simpa [f] using hclose r hrRange
      _ <= Finset.sum (Finset.range q) (fun r => 4 *
          linnikReciprocalSquareKernel Y ((f r : Real) / q)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro r hr hrNot
        exact mul_nonneg (by norm_num)
          (linnikReciprocalSquareKernel_nonneg Y ((f r : Real) / q) hY.le)
      _ = 4 * Finset.sum (Finset.range q) (fun r =>
          linnikReciprocalSquareKernel Y ((f r : Real) / q)) := by
        rw [Finset.mul_sum]
      _ <= 4 * M := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa [f] using hrational
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.range q)
    (fun r => Membership.mem (linnikExceptionalResidues q) (f r))
    (fun r => linnikReciprocalSquareKernel Y (actual r))
  have htotal : Finset.sum (Finset.range q)
      (fun r => linnikReciprocalSquareKernel Y (actual r)) =
      Finset.sum bad (fun r => linnikReciprocalSquareKernel Y (actual r)) +
        Finset.sum good (fun r =>
          linnikReciprocalSquareKernel Y (actual r)) := by
    simpa [bad, good, f, linnikExceptionalAffineIndices] using hsplit.symm
  rw [htotal]
  calc
    Finset.sum bad (fun r => linnikReciprocalSquareKernel Y (actual r)) +
        Finset.sum good (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
        3 * Y + 4 * M :=
      _root_.add_le_add hbad hgood

theorem linnik_perturbed_affine_block_kernel_sum_le
    (Y : Real) (a c q : Nat) (actual : Nat -> Real)
    (hY : 0 < Y) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hclose : forall r, Membership.mem (Finset.range q) r ->
      abs (actual r - ((((a * r + c) % q : Nat) : Real) / q)) <=
        1 / (q : Real)) :
    Finset.sum (Finset.range q)
        (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
      7 * Y + 16 * (q : Real) ^ 2 / Y := by
  calc
    Finset.sum (Finset.range q)
        (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
        3 * Y + 4 * (Y + 4 * (q : Real) ^ 2 / Y) :=
      linnik_perturbed_affine_block_kernel_sum_le_of_rational_bound
        Y (Y + 4 * (q : Real) ^ 2 / Y) a c q actual hY hq hcop hclose
        (linnik_affine_rational_residue_kernel_sum_le Y a c q hY hq hcop)
    _ = 7 * Y + 16 * (q : Real) ^ 2 / Y := by ring

theorem linnik_perturbed_affine_block_kernel_sum_le_sharp
    (Y : Real) (a c q : Nat) (actual : Nat -> Real)
    (hY : 0 < Y) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hclose : forall r, Membership.mem (Finset.range q) r ->
      abs (actual r - ((((a * r + c) % q : Nat) : Real) / q)) <=
        1 / (q : Real)) :
    Finset.sum (Finset.range q)
        (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
      7 * Y + 24 * (q : Real) := by
  calc
    Finset.sum (Finset.range q)
        (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
        3 * Y + 4 * (Y + 6 * (q : Real)) :=
      linnik_perturbed_affine_block_kernel_sum_le_of_rational_bound
        Y (Y + 6 * (q : Real)) a c q actual hY hq hcop hclose
        (linnik_affine_rational_residue_kernel_sum_le_sharp
          Y a c q hY hq hcop)
    _ = 7 * Y + 24 * (q : Real) := by ring

theorem linnik_ordinary_block_rounding_error
    (alpha theta : Real) (a q u r : Nat)
    (hq : 0 < q) (htheta : abs theta <= 1) (hr : r < q)
    (halpha : alpha = (a : Real) / q + theta / (q : Real) ^ 2) :
    abs ((((u * q + r : Nat) : Real) * alpha) -
      ((u * a : Nat) : Real) -
      ((((r * a : Nat) : Real) + (round ((u : Real) * theta) : Real)) / q)) <=
        3 / (2 * (q : Real)) := by
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hrReal : (r : Real) <= (q : Real) := by exact_mod_cast hr.le
  have hround := abs_sub_round ((u : Real) * theta)
  have heq :
      (((u * q + r : Nat) : Real) * alpha) -
          ((u * a : Nat) : Real) -
          ((((r * a : Nat) : Real) +
            (round ((u : Real) * theta) : Real)) / q) =
        (((u : Real) * theta - (round ((u : Real) * theta) : Real)) / q) +
          ((r : Real) * theta / (q : Real) ^ 2) := by
    rw [halpha]
    push_cast
    field_simp
    ring
  rw [heq]
  calc
    abs ((((u : Real) * theta - (round ((u : Real) * theta) : Real)) / q) +
        ((r : Real) * theta / (q : Real) ^ 2)) <=
        abs (((u : Real) * theta - (round ((u : Real) * theta) : Real)) / q) +
          abs ((r : Real) * theta / (q : Real) ^ 2) := abs_add_le _ _
    _ = abs ((u : Real) * theta - (round ((u : Real) * theta) : Real)) / q +
        ((r : Real) * abs theta) / (q : Real) ^ 2 := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hqReal,
        abs_of_pos (sq_pos_of_pos hqReal), abs_of_nonneg (by positivity : (0 : Real) <= r)]
    _ <= (1 / 2) / (q : Real) +
        ((r : Real) * 1) / (q : Real) ^ 2 := by
      apply _root_.add_le_add
      next => exact div_le_div_of_nonneg_right hround hqReal.le
      next =>
        apply div_le_div_of_nonneg_right _ (sq_nonneg (q : Real))
        exact mul_le_mul_of_nonneg_left htheta (by positivity)
    _ <= (1 / 2) / (q : Real) +
        ((q : Real) * 1) / (q : Real) ^ 2 := by
      apply _root_.add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ (sq_nonneg (q : Real))
      exact mul_le_mul_of_nonneg_right hrReal (by norm_num)
    _ = 3 / (2 * (q : Real)) := by
      field_simp
      norm_num

/-- The least nonnegative residue of an integer modulo `q`. -/
def linnikIntResidue (q : Nat) [NeZero q] (n : Int) : Nat :=
  (n : ZMod q).val

/-- Nearest-integer distance of an integral rational depends only on its
least nonnegative residue. -/
theorem linnikNearestIntDist_int_div_eq_residue
    (q : Nat) (n : Int) (hq : 0 < q) :
    letI : NeZero q := { out := Nat.ne_of_gt hq }
    linnikNearestIntDist ((n : Real) / q) =
      linnikNearestIntDist ((linnikIntResidue q n : Real) / q) := by
  letI : NeZero q := { out := Nat.ne_of_gt hq }
  have hval : ((linnikIntResidue q n : Nat) : Int) = n % (q : Int) := by
    exact ZMod.val_intCast n
  have hdecomp : n = n % (q : Int) + n / (q : Int) * (q : Int) := by
    exact (Int.emod_add_ediv_mul n (q : Int)).symm
  have hdecompInt : n =
      (linnikIntResidue q n : Int) + n / (q : Int) * (q : Int) := by
    rw [hval]
    exact hdecomp
  have hdecompReal : (n : Real) =
      (linnikIntResidue q n : Real) +
        (n / (q : Int) : Int) * (q : Real) := by
    exact_mod_cast hdecompInt
  have hreal : (n : Real) / q =
      (linnikIntResidue q n : Real) / q + (n / (q : Int) : Int) := by
    rw [hdecompReal]
    field_simp
  rw [hreal]
  exact linnikNearestIntDist_add_int
    ((linnikIntResidue q n : Real) / q) (n / (q : Int))
