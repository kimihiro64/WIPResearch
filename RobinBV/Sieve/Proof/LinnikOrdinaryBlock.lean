/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikPerturbedBlock

/-!
# Ordinary approximate-rational blocks in Linnik's inequality

This module enlarges the exceptional residue packet from distance `2/q` to
distance `3/q`.  That is the packet required by the ordinary block rounding
error `3/(2q)`.  There are at most five exceptional residues, while every
remaining term is at most four times its rational model.
-/

theorem linnikReciprocalSquareKernel_le_four_of_distance_close
    (Y x y : Real) (hY : 0 < Y)
    (hy : 0 < linnikNearestIntDist y)
    (hxy : abs (linnikNearestIntDist x - linnikNearestIntDist y) <=
      linnikNearestIntDist y / 2) :
    linnikReciprocalSquareKernel Y x <=
      4 * linnikReciprocalSquareKernel Y y := by
  have hhalf : linnikNearestIntDist y / 2 <=
      linnikNearestIntDist x := by
    have hlower := (abs_le.mp hxy).1
    linarith
  have hxPos : 0 < linnikNearestIntDist x := by
    nlinarith
  rw [linnikReciprocalSquareKernel, if_neg (ne_of_gt hxPos),
    linnikReciprocalSquareKernel, if_neg (ne_of_gt hy)]
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

def linnikWideExceptionalResidues (q : Nat) : Finset Nat :=
  (Finset.range q).filter (fun z => Or (z < 3) (q - z < 3))

theorem linnikWideExceptionalResidues_subset_five (q : Nat) :
    linnikWideExceptionalResidues q <= {0, 1, 2, q - 2, q - 1} := by
  intro z hz
  have hzParts := Finset.mem_filter.mp hz
  have hzRange : z < q := Finset.mem_range.mp hzParts.1
  have hzClose : Or (z < 3) (q - z < 3) := hzParts.2
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hzClose with hleft | hright
  next =>
    omega
  next =>
    omega

theorem linnikWideExceptionalResidues_card_le_five (q : Nat) :
    (linnikWideExceptionalResidues q).card <= 5 := by
  exact (Finset.card_le_card
    (linnikWideExceptionalResidues_subset_five q)).trans
      Finset.card_le_five

theorem linnik_rational_residue_distance_ge_three
    (q z : Nat) (hq : 0 < q)
    (hz : Membership.mem (Finset.range q) z)
    (hzNot : Not (Membership.mem (linnikWideExceptionalResidues q) z)) :
    3 / (q : Real) <= linnikNearestIntDist ((z : Real) / q) := by
  have hzlt : z < q := Finset.mem_range.mp hz
  have hnot : Not (Or (z < 3) (q - z < 3)) := by
    intro hclose
    apply hzNot
    exact Finset.mem_filter.mpr (And.intro hz hclose)
  have hzThree : 3 <= z := by omega
  have hqzThree : 3 <= q - z := by omega
  have hmin : 3 <= min z (q - z) := le_min hzThree hqzThree
  have hdist : linnikNearestIntDist ((z : Real) / q) =
      ((min z (q - z) : Nat) : Real) / q := by
    unfold linnikNearestIntDist
    rw [abs_sub_round_div_natCast_eq, Nat.mod_eq_of_lt hzlt]
  rw [hdist]
  apply div_le_div_of_nonneg_right
  next => exact_mod_cast hmin
  next => positivity

def linnikWideExceptionalAffineIndices (a c q : Nat) : Finset Nat :=
  (Finset.range q).filter (fun r =>
    Membership.mem (linnikWideExceptionalResidues q) ((a * r + c) % q))

theorem linnikWideExceptionalAffineIndices_card_le_five
    (a c q : Nat) (hcop : Nat.Coprime a q) :
    (linnikWideExceptionalAffineIndices a c q).card <= 5 := by
  let f : Nat -> Nat := fun r => (a * r + c) % q
  have hinj : forall r,
      Membership.mem (linnikWideExceptionalAffineIndices a c q) r ->
      forall s, Membership.mem (linnikWideExceptionalAffineIndices a c q) s ->
        f r = f s -> r = s := by
    intro r hr s hs hrs
    have hrRange := (Finset.mem_filter.mp hr).1
    have hsRange := (Finset.mem_filter.mp hs).1
    exact linnik_affine_residue_injective_on a c q hcop
      r hrRange s hsRange hrs
  have hsubset : Finset.image f (linnikWideExceptionalAffineIndices a c q) <=
      linnikWideExceptionalResidues q := by
    intro z hz
    rw [Finset.mem_image] at hz
    choose r hr hzr using hz
    have hrExceptional := (Finset.mem_filter.mp hr).2
    rw [<- hzr]
    exact hrExceptional
  have hcard : (Finset.image f
      (linnikWideExceptionalAffineIndices a c q)).card =
      (linnikWideExceptionalAffineIndices a c q).card :=
    Finset.card_image_iff.mpr hinj
  calc
    (linnikWideExceptionalAffineIndices a c q).card =
        (Finset.image f (linnikWideExceptionalAffineIndices a c q)).card :=
      hcard.symm
    _ <= (linnikWideExceptionalResidues q).card :=
      Finset.card_le_card hsubset
    _ <= 5 := linnikWideExceptionalResidues_card_le_five q

theorem linnik_wide_perturbed_affine_block_kernel_sum_le_of_rational_bound
    (Y M : Real) (a c q : Nat) (actual : Nat -> Real)
    (hY : 0 < Y) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hclose : forall r, Membership.mem (Finset.range q) r ->
      abs (linnikNearestIntDist (actual r) -
        linnikNearestIntDist ((((a * r + c) % q : Nat) : Real) / q)) <=
          3 / (2 * (q : Real)))
    (hrational : Finset.sum (Finset.range q) (fun r =>
      linnikReciprocalSquareKernel Y
        ((((a * r + c) % q : Nat) : Real) / q)) <= M) :
    Finset.sum (Finset.range q)
        (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
      5 * Y + 4 * M := by
  let f : Nat -> Nat := fun r => (a * r + c) % q
  let bad := linnikWideExceptionalAffineIndices a c q
  let good := (Finset.range q).filter (fun r =>
    Not (Membership.mem (linnikWideExceptionalResidues q) (f r)))
  have hbadCard : bad.card <= 5 := by
    exact linnikWideExceptionalAffineIndices_card_le_five a c q hcop
  have hbadCardReal : (bad.card : Real) <= 5 := by exact_mod_cast hbadCard
  have hbad : Finset.sum bad
      (fun r => linnikReciprocalSquareKernel Y (actual r)) <= 5 * Y := by
    calc
      Finset.sum bad (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
          Finset.sum bad (fun _ => Y) := by
        apply Finset.sum_le_sum
        intro r hr
        exact linnikReciprocalSquareKernel_le_left Y (actual r)
      _ = (bad.card : Real) * Y := by simp
      _ <= 5 * Y := mul_le_mul_of_nonneg_right hbadCardReal hY.le
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
        have hzDist := linnik_rational_residue_distance_ge_three
          q (f r) hq hzRange hrParts.2
        have hyPos : 0 < linnikNearestIntDist ((f r : Real) / q) :=
          lt_of_lt_of_le (by positivity : 0 < 3 / (q : Real)) hzDist
        apply linnikReciprocalSquareKernel_le_four_of_distance_close
          Y (actual r) ((f r : Real) / q) hY hyPos
        have hcloseR := hclose r hrRange
        have hthree :
            3 / (2 * (q : Real)) = (3 / (q : Real)) / 2 := by ring
        rw [hthree] at hcloseR
        exact hcloseR.trans
          (div_le_div_of_nonneg_right hzDist (by norm_num))
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
    (fun r => Membership.mem (linnikWideExceptionalResidues q) (f r))
    (fun r => linnikReciprocalSquareKernel Y (actual r))
  have htotal : Finset.sum (Finset.range q)
      (fun r => linnikReciprocalSquareKernel Y (actual r)) =
      Finset.sum bad (fun r => linnikReciprocalSquareKernel Y (actual r)) +
        Finset.sum good (fun r =>
          linnikReciprocalSquareKernel Y (actual r)) := by
    simpa [bad, good, f, linnikWideExceptionalAffineIndices] using hsplit.symm
  rw [htotal]
  exact _root_.add_le_add hbad hgood

theorem linnik_wide_perturbed_affine_block_kernel_sum_le
    (Y : Real) (a c q : Nat) (actual : Nat -> Real)
    (hY : 0 < Y) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (hclose : forall r, Membership.mem (Finset.range q) r ->
      abs (linnikNearestIntDist (actual r) -
        linnikNearestIntDist ((((a * r + c) % q : Nat) : Real) / q)) <=
          3 / (2 * (q : Real))) :
    Finset.sum (Finset.range q)
        (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
      9 * Y + 24 * (q : Real) := by
  calc
    Finset.sum (Finset.range q)
        (fun r => linnikReciprocalSquareKernel Y (actual r)) <=
        5 * Y + 4 * (Y + 6 * (q : Real)) :=
      linnik_wide_perturbed_affine_block_kernel_sum_le_of_rational_bound
        Y (Y + 6 * (q : Real)) a c q actual hY hq hcop hclose
        (linnik_affine_rational_residue_kernel_sum_le_sharp
          Y a c q hY hq hcop)
    _ = 9 * Y + 24 * (q : Real) := by ring

theorem linnikIntResidue_nat_mul_add
    (q a r : Nat) (c : Int) (hq : 0 < q) :
    letI : NeZero q := { out := Nat.ne_of_gt hq }
    linnikIntResidue q (((r * a : Nat) : Int) + c) =
      (a * r + linnikIntResidue q c) % q := by
  letI : NeZero q := { out := Nat.ne_of_gt hq }
  unfold linnikIntResidue
  have hz :
      (((((r * a : Nat) : Int) + c : Int) : ZMod q)) =
        ((a * r + (c : ZMod q).val : Nat) : ZMod q) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring
  have hv := congrArg ZMod.val hz
  simpa only [ZMod.val_natCast] using hv

theorem linnikNearestIntDist_nat_mul_add_div_eq_residue
    (q a r : Nat) (c : Int) (hq : 0 < q) :
    letI : NeZero q := { out := Nat.ne_of_gt hq }
    linnikNearestIntDist
        (((((r * a : Nat) : Int) + c : Int) : Real) / q) =
      linnikNearestIntDist
        ((((a * r + linnikIntResidue q c) % q : Nat) : Real) / q) := by
  letI : NeZero q := { out := Nat.ne_of_gt hq }
  rw [linnikNearestIntDist_int_div_eq_residue q
    (((r * a : Nat) : Int) + c) hq]
  rw [linnikIntResidue_nat_mul_add q a r c hq]

theorem linnik_ordinary_block_nearest_distance_close
    (alpha theta : Real) (a q u r : Nat)
    (hq : 0 < q) (htheta : abs theta <= 1) (hr : r < q)
    (halpha : alpha = (a : Real) / q + theta / (q : Real) ^ 2) :
    letI : NeZero q := { out := Nat.ne_of_gt hq }
    abs (linnikNearestIntDist (((u * q + r : Nat) : Real) * alpha) -
      linnikNearestIntDist
        ((((a * r + linnikIntResidue q
          (round ((u : Real) * theta))) % q : Nat) : Real) / q)) <=
      3 / (2 * (q : Real)) := by
  letI : NeZero q := { out := Nat.ne_of_gt hq }
  let phase : Real := ((u * q + r : Nat) : Real) * alpha
  let shift : Int := (u * a : Nat)
  let center : Real :=
    (((r * a : Nat) : Real) + (round ((u : Real) * theta) : Real)) / q
  have hphase : linnikNearestIntDist (phase - (shift : Real)) =
      linnikNearestIntDist phase := by
    simpa [sub_eq_add_neg] using
      linnikNearestIntDist_add_int phase (-shift)
  have hcenter : linnikNearestIntDist center =
      linnikNearestIntDist
        ((((a * r + linnikIntResidue q
          (round ((u : Real) * theta))) % q : Nat) : Real) / q) := by
    have hcenterCast :
        center =
          (((((r * a : Nat) : Int) +
            round ((u : Real) * theta) : Int) : Real) / q) := by
      simp [center]
    rw [hcenterCast]
    exact linnikNearestIntDist_nat_mul_add_div_eq_residue q a r
      (round ((u : Real) * theta)) hq
  have hlipLeft := linnikNearestIntDist_sub_abs_le
    (phase - (shift : Real)) center
  have hlipRight := linnikNearestIntDist_sub_abs_le
    center (phase - (shift : Real))
  have hlip :
      abs (linnikNearestIntDist (phase - (shift : Real)) -
        linnikNearestIntDist center) <=
      abs ((phase - (shift : Real)) - center) := by
    rw [abs_le]
    constructor
    next =>
      rw [abs_sub_comm] at hlipLeft
      linarith
    next =>
      linarith
  have hraw : abs ((phase - (shift : Real)) - center) <=
      3 / (2 * (q : Real)) := by
    simpa [phase, shift, center] using
      linnik_ordinary_block_rounding_error
        alpha theta a q u r hq htheta hr halpha
  rw [hphase, hcenter] at hlip
  exact hlip.trans hraw

theorem linnik_ordinary_affine_block_kernel_sum_le
    (Y alpha theta : Real) (a q u : Nat)
    (hY : 0 < Y) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (htheta : abs theta <= 1)
    (halpha : alpha = (a : Real) / q + theta / (q : Real) ^ 2) :
    Finset.sum (Finset.range q) (fun r =>
      linnikReciprocalSquareKernel Y
        (((u * q + r : Nat) : Real) * alpha)) <=
      9 * Y + 24 * (q : Real) := by
  letI : NeZero q := { out := Nat.ne_of_gt hq }
  apply linnik_wide_perturbed_affine_block_kernel_sum_le
    Y a (linnikIntResidue q (round ((u : Real) * theta))) q
      (fun r => ((u * q + r : Nat) : Real) * alpha) hY hq hcop
  intro r hr
  exact linnik_ordinary_block_nearest_distance_close
    alpha theta a q u r hq htheta (Finset.mem_range.mp hr) halpha

theorem linnik_sum_range_mul_eq_sum_blocks
    (f : Nat -> Real) (K q : Nat) :
    Finset.sum (Finset.range (K * q)) f =
      Finset.sum (Finset.range K) (fun u =>
        Finset.sum (Finset.range q) (fun r => f (u * q + r))) := by
  induction K with
  | zero =>
      simp
  | succ K ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem linnik_ordinary_range_kernel_sum_le
    (Y alpha theta : Real) (a q X : Nat)
    (hY : 0 < Y) (hq : 0 < q) (hcop : Nat.Coprime a q)
    (htheta : abs theta <= 1)
    (halpha : alpha = (a : Real) / q + theta / (q : Real) ^ 2) :
    Finset.sum (Finset.range X) (fun n =>
      linnikReciprocalSquareKernel Y ((n : Real) * alpha)) <=
      24 * (((X : Real) * Y) / q + X + Y + q) := by
  let K : Nat := X / q + 1
  let f : Nat -> Real := fun n =>
    linnikReciprocalSquareKernel Y ((n : Real) * alpha)
  have hcover : X <= K * q := by
    have hmod := Nat.mod_lt X hq
    have hlt : X < (X / q + 1) * q := by
      calc
        X = X % q + q * (X / q) := (Nat.mod_add_div X q).symm
        _ < q + q * (X / q) := Nat.add_lt_add_right hmod _
        _ = (X / q + 1) * q := by ring
    simpa [K] using hlt.le
  have hprefix :
      Finset.sum (Finset.range X) f <=
        Finset.sum (Finset.range (K * q)) f := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hcover)
    intro n hnLarge hnSmall
    exact linnikReciprocalSquareKernel_nonneg
      Y ((n : Real) * alpha) hY.le
  have hblocks :
      Finset.sum (Finset.range (K * q)) f <=
        (K : Real) * (9 * Y + 24 * (q : Real)) := by
    rw [linnik_sum_range_mul_eq_sum_blocks]
    calc
      Finset.sum (Finset.range K) (fun u =>
          Finset.sum (Finset.range q) (fun r => f (u * q + r))) <=
          Finset.sum (Finset.range K)
            (fun _ => 9 * Y + 24 * (q : Real)) := by
        apply Finset.sum_le_sum
        intro u hu
        simpa [f, Nat.cast_add, Nat.cast_mul] using
          linnik_ordinary_affine_block_kernel_sum_le
            Y alpha theta a q u hY hq hcop htheta halpha
      _ = (K : Real) * (9 * Y + 24 * (q : Real)) := by
        simp
        ring
  have hdiv : ((X / q : Nat) : Real) <= (X : Real) / (q : Real) := by
    exact Nat.cast_div_le
  have hK : (K : Real) <= (X : Real) / (q : Real) + 1 := by
    dsimp [K]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hblockNonneg : 0 <= 9 * Y + 24 * (q : Real) := by positivity
  have hKBound :
      (K : Real) * (9 * Y + 24 * (q : Real)) <=
        ((X : Real) / (q : Real) + 1) *
          (9 * Y + 24 * (q : Real)) :=
    mul_le_mul_of_nonneg_right hK hblockNonneg
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hXY : 0 <= ((X : Real) * Y) / (q : Real) := by positivity
  have henvelope :
      ((X : Real) / (q : Real) + 1) *
          (9 * Y + 24 * (q : Real)) <=
        24 * (((X : Real) * Y) / q + X + Y + q) := by
    have hidentity :
        ((X : Real) / (q : Real) + 1) *
            (9 * Y + 24 * (q : Real)) =
          9 * (((X : Real) * Y) / q) +
            24 * (X : Real) + 9 * Y + 24 * (q : Real) := by
      field_simp
      ring
    rw [hidentity]
    nlinarith
  exact hprefix.trans (hblocks.trans (hKBound.trans henvelope))
