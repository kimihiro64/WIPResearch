/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalPrimePowerFringe
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalUnitFringe

/-!
# Complete boundary control for the signed unit-fringe correlation

Retain both endpoint strips in an exact three-way partition. Each strip
contains at most two reduced-class indices; the top kernel is bounded by
one and the lower kernel by its actual row capacity. This gives the explicit
weighted boundary cost and its Mangoldt specialization for every n >= 100.
The full signed interior prime correlation remains present and unestimated.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- The absolute signed kernel is at most the complete actual fringe count. -/
theorem abs_squareThirdSignedFringeKernel_le_card (n r : Nat) :
    abs (squareThirdSignedFringeKernel n r) <= ((squareThirdFringeRows n r).card : Int) := by
  have h1 := Finset.card_le_card (show squareThirdClassFringeRows n r 1 <= squareThirdFringeRows n r
    from Finset.filter_subset _ _)
  have h5 := Finset.card_le_card (show squareThirdClassFringeRows n r 5 <= squareThirdFringeRows n r
    from Finset.filter_subset _ _)
  unfold squareThirdSignedFringeKernel
  apply abs_le.mpr
  constructor <;> omega

/-- The signed kernel vanishes outside its exact enclosing fringe support. -/
theorem squareThirdSignedFringeKernel_eq_zero_of_notMem {n r : Nat} (hn : 100 <= n)
    (hr : Not (Membership.mem (squareThirdFringeSupport n) r)) :
    squareThirdSignedFringeKernel n r = 0 := by
  have hzero : squareThirdFringeRows n r = ({} : Finset Nat) := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro h hh
    exact hr (squareThirdFringeRows_bounds hn hh).2
  simp [squareThirdSignedFringeKernel, squareThirdClassFringeRows, hzero]

/-- The complete pointwise row capacity also bounds the signed kernel. -/
theorem abs_squareThirdSignedFringeKernel_le_capacity {n r : Nat}
    (hn : 100 <= n) (hr : 0 < r) :
    abs (squareThirdSignedFringeKernel n r) <= (2*(n/(3*r)+1) : Nat) := by
  have h1 := abs_squareThirdSignedFringeKernel_le_card n r
  have h2 := card_squareThirdFringeRows_le hn hr
  omega

/-- Each actual reduced-class fringe has at most one row beyond one-third of n. -/
theorem card_squareThirdClassFringeRows_le_one {n r a : Nat}
    (hn : 100 <= n) (ha : a = 1 \/ a = 5) (hr : n < 3*r) :
    (squareThirdClassFringeRows n r a).card <= 1 := by
  have hpoint := nextModSixPoint_spec r (show a < 6 by omega)
  rw [squareThirdClassFringeRows_eq_fixed hn hpoint.2.2 hpoint.1 hpoint.2.1]
  have hpodd : (nextModSixPoint r a)%2 = 1 := by omega
  have h3odd : (3*nextModSixPoint r a)%2 = 1 := by omega
  have hfixed := card_squareThirdFixedFactorRows_le (n := n) hpodd
  have hcapacity := card_oddMultiplesInSquare_le_div_add_one n h3odd
  have hlt : n < 3*nextModSixPoint r a := by omega
  rw [Nat.div_eq_of_lt hlt] at hcapacity
  omega

/-- The signed kernel is bounded by one throughout the top regime. -/
theorem abs_squareThirdSignedFringeKernel_le_one {n r : Nat}
    (hn : 100 <= n) (hr : n < 3*r) :
    abs (squareThirdSignedFringeKernel n r) <= 1 := by
  have h1 := card_squareThirdClassFringeRows_le_one hn (Or.inl rfl : 1 = 1 \/ 1 = 5) hr
  have h5 := card_squareThirdClassFringeRows_le_one hn (Or.inr rfl : 5 = 1 \/ 5 = 5) hr
  unfold squareThirdSignedFringeKernel
  apply abs_le.mpr
  constructor <;> omega

/-- The full fringe support restricted to the two reduced residue classes. -/
noncomputable def squareThirdUnitFringeSupport (n : Nat) : Finset Nat :=
  (squareThirdFringeSupport n).filter (fun r => r%6 = 1 \/ r%6 = 5)

/-- The entire interior unit support, with both endpoint strips removed explicitly. -/
noncomputable def squareThirdUnitInterior (n : Nat) : Finset Nat :=
  ((squareThirdUnitFringeSupport n).filter (fun r => Nat.nthRoot 3 (n*n+2*n) < r)).filter
    (fun r => r+5 <= n)

/-- The complete lower unit edge strip. -/
noncomputable def squareThirdUnitLowerEdge (n : Nat) : Finset Nat :=
  (squareThirdUnitFringeSupport n).filter (fun r => Not (Nat.nthRoot 3 (n*n+2*n) < r))

/-- The complete upper unit edge strip after excluding the lower strip. -/
noncomputable def squareThirdUnitUpperEdge (n : Nat) : Finset Nat :=
  ((squareThirdUnitFringeSupport n).filter (fun r => Nat.nthRoot 3 (n*n+2*n) < r)).filter
    (fun r => Not (r+5 <= n))

/-- The lower edge contains at most two unit-class indices. -/
theorem card_squareThirdUnitLowerEdge_le_two {n : Nat} (hn : 100 <= n) :
    (squareThirdUnitLowerEdge n).card <= 2 := by
  have hY := squareThirdFringeSupport_lower_pos hn
  have hsub : squareThirdUnitLowerEdge n <= modSixUnitCandidates (Nat.nthRoot 3 (n*n+2*n)-4) := by
    intro r hr
    have he := Finset.mem_filter.mp hr
    have hu := Finset.mem_filter.mp he.1
    have hs := Finset.mem_Icc.mp hu.1
    apply Finset.mem_filter.mpr
    exact And.intro (Finset.mem_Ico.mpr (And.intro hs.1 (by omega))) hu.2
  exact le_trans (Finset.card_le_card hsub) (card_modSixUnitCandidates_le_two _)

/-- The upper edge contains at most two unit-class indices. -/
theorem card_squareThirdUnitUpperEdge_le_two {n : Nat} (hn : 100 <= n) :
    (squareThirdUnitUpperEdge n).card <= 2 := by
  have hsub : squareThirdUnitUpperEdge n <= modSixUnitCandidates (n-4) := by
    intro r hr
    have he := Finset.mem_filter.mp hr
    have hu := Finset.mem_filter.mp (Finset.mem_filter.mp he.1).1
    have hs := Finset.mem_Icc.mp hu.1
    apply Finset.mem_filter.mpr
    exact And.intro (Finset.mem_Ico.mpr (And.intro (by omega) (by omega))) hu.2
  exact le_trans (Finset.card_le_card hsub) (card_modSixUnitCandidates_le_two _)

/-- Exact three-way partition with both edge strips and all weights retained. -/
theorem sum_squareThirdUnitFringeSupport_split (n : Nat) (F : Nat -> Real) :
    Finset.sum (squareThirdUnitFringeSupport n) F =
      Finset.sum (squareThirdUnitInterior n) F +
      Finset.sum (squareThirdUnitLowerEdge n) F +
      Finset.sum (squareThirdUnitUpperEdge n) F := by
  have h1 := Finset.sum_filter_add_sum_filter_not (squareThirdUnitFringeSupport n)
    (fun r => Nat.nthRoot 3 (n*n+2*n) < r) F
  have h2 := Finset.sum_filter_add_sum_filter_not
    ((squareThirdUnitFringeSupport n).filter (fun r => Nat.nthRoot 3 (n*n+2*n) < r))
    (fun r => r+5 <= n) F
  change Finset.sum _ F + Finset.sum (squareThirdUnitLowerEdge n) F = _ at h1
  change Finset.sum (squareThirdUnitInterior n) F + Finset.sum (squareThirdUnitUpperEdge n) F = _ at h2
  linarith only [h1, h2]

/-- The signed-unit mask never increases the absolute value of an arbitrary weight. -/
theorem abs_modSixSignedWeight_le (F : Nat -> Real) (r : Nat) :
    abs (modSixSignedWeight F r) <= abs (F r) := by
  by_cases h1 : r%6 = 1
  next => simp [modSixSignedWeight, modSixSign, h1]
  next =>
    by_cases h5 : r%6 = 5
    all_goals simp [modSixSignedWeight, modSixSign, h1, h5]

/-- The full centered correlation restricts exactly to its actual unit support. -/
theorem squareThirdUnitCenteredMass_eq_supported_kernel {n : Nat}
    (hn : 100 <= n) (F : Nat -> Real) :
    squareThirdUnitCenteredMass n F =
      (1/2:Real)*Finset.sum (squareThirdUnitFringeSupport n) (fun r =>
        (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight F r) := by
  rw [squareThirdUnitCenteredMass_eq_kernel hn]
  congr 1
  symm
  apply Finset.sum_subset
  next =>
    intro r hr
    have hs := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
    exact Finset.mem_range.mpr (by omega)
  next =>
    intro r hr hnot
    by_cases hs : Membership.mem (squareThirdFringeSupport n) r
    next =>
      have hu : Not (r%6 = 1 \/ r%6 = 5) := by
        intro hu
        exact hnot (Finset.mem_filter.mpr (And.intro hs hu))
      have h1 : Not (r%6 = 1) := by omega
      have h5 : Not (r%6 = 5) := by omega
      simp [modSixSignedWeight, modSixSign, h1, h5]
    next =>
      rw [squareThirdSignedFringeKernel_eq_zero_of_notMem hn hs]
      simp

/-- Removing the full signed interior leaves precisely the two weighted edge sums. -/
theorem squareThirdUnitCenteredMass_sub_interior_eq {n : Nat}
    (hn : 100 <= n) (F : Nat -> Real) :
    squareThirdUnitCenteredMass n F -
      (1/2:Real)*Finset.sum (squareThirdUnitInterior n) (fun r =>
        (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight F r) =
      (1/2:Real)*(
        Finset.sum (squareThirdUnitLowerEdge n) (fun r =>
          (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight F r) +
        Finset.sum (squareThirdUnitUpperEdge n) (fun r =>
          (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight F r)) := by
  rw [squareThirdUnitCenteredMass_eq_supported_kernel hn, sum_squareThirdUnitFringeSupport_split]
  ring


/-- A cutoff-uniform bound for the signed kernel on its entire actual support. -/
theorem abs_squareThirdSignedFringeKernel_le_cutoff {n r : Nat}
    (hn : 100 <= n) (hr : Membership.mem (squareThirdFringeSupport n) r) :
    abs (squareThirdSignedFringeKernel n r) <=
      (2*(n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1) : Nat) := by
  let Y := Nat.nthRoot 3 (n*n+2*n)-4
  have hY : 0 < Y := squareThirdFringeSupport_lower_pos hn
  have hs := Finset.mem_Icc.mp hr
  have hr0 : 0 < r := by omega
  have hK := abs_squareThirdSignedFringeKernel_le_capacity hn hr0
  have hmul := Nat.div_mul_le_self n (3*r)
  have hden := Nat.mul_le_mul_left (n/(3*r)) (show 3*Y <= 3*r by omega)
  have hdiv : n/(3*r) <= n/(3*Y) := by
    apply (Nat.le_div_iff_mul_le (show 0 < 3*Y by omega)).mpr
    nlinarith only [hmul, hden]
  change abs (squareThirdSignedFringeKernel n r) <= (2*(n/(3*Y)+1) : Nat)
  omega

/-- Both endpoint strips have an explicit weighted bound; the interior sum is retained exactly. -/
theorem abs_squareThirdUnitCenteredMass_sub_interior_le {n : Nat}
    (hn : 100 <= n) (F : Nat -> Real) {M : Real} (hM : 0 <= M)
    (hF : forall r : Nat, Membership.mem (squareThirdFringeSupport n) r -> abs (F r) <= M) :
    abs (squareThirdUnitCenteredMass n F -
      (1/2:Real)*Finset.sum (squareThirdUnitInterior n) (fun r =>
        (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight F r)) <=
      (2*(n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1)+1 : Nat)*M := by
  let B : Nat := n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1
  let g : Nat -> Real := fun r => (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight F r
  have hsum (s : Finset Nat) (C : Real) (hC : 0 <= C) (hs : s.card <= 2)
      (hpoint : forall r : Nat, Membership.mem s r -> abs (g r) <= C) :
      abs (Finset.sum s g) <= 2*C := by
    calc
      _ <= Finset.sum s (fun r => abs (g r)) := Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum s (fun _ => C) := Finset.sum_le_sum hpoint
      _ = (s.card : Real)*C := by simp
      _ <= _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hC
  have hL : abs (Finset.sum (squareThirdUnitLowerEdge n) g) <=
      2*(((2*B : Nat) : Real)*M) := by
    apply hsum _ _ (mul_nonneg (Nat.cast_nonneg _) hM) (card_squareThirdUnitLowerEdge_le_two hn)
    intro r hr
    have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
    have hK := abs_squareThirdSignedFringeKernel_le_cutoff hn hs
    have hKR : abs ((squareThirdSignedFringeKernel n r : Int) : Real) <= (2*B : Nat) := by
      exact_mod_cast hK
    have hFR := le_trans (abs_modSixSignedWeight_le F r) (hF r hs)
    dsimp [g]
    rw [abs_mul]
    exact mul_le_mul hKR hFR (abs_nonneg _) (Nat.cast_nonneg _)
  have hU : abs (Finset.sum (squareThirdUnitUpperEdge n) g) <= 2*M := by
    apply hsum _ _ hM (card_squareThirdUnitUpperEdge_le_two hn)
    intro r hr
    have hd := Finset.mem_filter.mp hr
    have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hd.1).1).1
    have hK := abs_squareThirdSignedFringeKernel_le_one hn (show n < 3*r by omega)
    have hKR : abs ((squareThirdSignedFringeKernel n r : Int) : Real) <= 1 := by
      exact_mod_cast hK
    have hFR := le_trans (abs_modSixSignedWeight_le F r) (hF r hs)
    dsimp [g]
    rw [abs_mul]
    calc
      _ <= 1*M := mul_le_mul hKR hFR (abs_nonneg _) (by norm_num)
      _ = M := one_mul M
  rw [squareThirdUnitCenteredMass_sub_interior_eq hn]
  change abs ((1/2:Real)*(Finset.sum (squareThirdUnitLowerEdge n) g+
    Finset.sum (squareThirdUnitUpperEdge n) g)) <= ((2*B+1 : Nat) : Real)*M
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:Real) <= 1/2)]
  have htri := abs_add_le (Finset.sum (squareThirdUnitLowerEdge n) g)
    (Finset.sum (squareThirdUnitUpperEdge n) g)
  push_cast at hL
  push_cast
  nlinarith only [hL, hU, htri]

/-- The actual Mangoldt centered mass has the explicit logarithmic two-edge remainder bound. -/
theorem abs_squareThirdMangoldtCentered_sub_interior_le {n : Nat}
    (hn : 100 <= n) :
    abs (squareThirdUnitCenteredMass n ArithmeticFunction.vonMangoldt -
      (1/2:Real)*Finset.sum (squareThirdUnitInterior n) (fun r =>
        (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight ArithmeticFunction.vonMangoldt r)) <=
      (2*(n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1)+1 : Nat)*Real.log n := by
  apply abs_squareThirdUnitCenteredMass_sub_interior_le hn
  next => exact Real.log_nonneg (by exact_mod_cast (show 1 <= n by omega))
  next =>
    intro r hr
    have hs := Finset.mem_Icc.mp hr
    have hY := squareThirdFringeSupport_lower_pos hn
    have hr0 : 0 < r := by omega
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact le_trans ArithmeticFunction.vonMangoldt_le_log
      (Real.log_le_log (by exact_mod_cast hr0) (by exact_mod_cast hs.2))

/-- The complete low interior prefix has an explicit weighted cardinality budget. -/
theorem abs_squareThirdUnitInterior_low_le {n : Nat} (hn : 100 <= n)
    (R : Nat) (F : Nat -> Real) {M : Real} (hM : 0 <= M)
    (hF : forall r, Membership.mem (squareThirdFringeSupport n) r -> abs (F r) <= M) :
    abs ((1/2:Real)*Finset.sum ((squareThirdUnitInterior n).filter (fun r => r <= R))
      (fun r => (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight F r)) <=
      (R : Real)*M := by
  let s := (squareThirdUnitInterior n).filter (fun r => r <= R)
  let g : Nat -> Real := fun r =>
    (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight F r
  have hs : s.card <= R := by
    have hsub : s <= Finset.Icc 1 R := by
      intro r hr
      have h := Finset.mem_filter.mp hr
      have hi := Finset.mem_filter.mp h.1
      have hy := Finset.mem_filter.mp hi.1
      exact Finset.mem_Icc.mpr (And.intro (by omega) h.2)
    simpa using Finset.card_le_card hsub
  have hp : forall r, Membership.mem s r -> abs (g r) <= 2*M := by
    intro r hr
    have h := Finset.mem_filter.mp hr
    have hi := Finset.mem_filter.mp h.1
    have hy := Finset.mem_filter.mp hi.1
    have hu := Finset.mem_filter.mp hy.1
    have hK : abs ((squareThirdSignedFringeKernel n r : Int) : Real) <= 2 := by
      exact_mod_cast abs_squareThirdSignedFringeKernel_le_two hn hy.2 hi.2
    have hw := le_trans (abs_modSixSignedWeight_le F r) (hF r hu.1)
    dsimp [g]
    rw [abs_mul]
    exact _root_.mul_le_mul hK hw (abs_nonneg _) (by norm_num)
  have hsum : abs (Finset.sum s g) <= (R : Real)*(2*M) := by
    calc
      _ <= Finset.sum s (fun r => abs (g r)) := Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum s (fun _ => 2*M) := Finset.sum_le_sum hp
      _ = (s.card : Real)*(2*M) := by simp
      _ <= _ := _root_.mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (by positivity)
  change abs ((1/2:Real)*Finset.sum s g) <= (R : Real)*M
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:Real) <= 1/2)]
  nlinarith only [hsum]

/-- Only the high interior remains after bounding the full low prefix and both edges. -/
theorem abs_squareThirdUnitCenteredMass_sub_high_le {n : Nat} (hn : 100 <= n)
    (R : Nat) (F : Nat -> Real) {M : Real} (hM : 0 <= M)
    (hF : forall r, Membership.mem (squareThirdFringeSupport n) r -> abs (F r) <= M) :
    abs (squareThirdUnitCenteredMass n F -
      (1/2:Real)*Finset.sum ((squareThirdUnitInterior n).filter (fun r => R < r))
        (fun r => (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight F r)) <=
      ((R+2*(n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1)+1 : Nat) : Real)*M := by
  let g : Nat -> Real := fun r =>
    (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight F r
  have hp := Finset.sum_filter_add_sum_filter_not (squareThirdUnitInterior n)
    (fun r => r <= R) g
  simp only [not_le] at hp
  have hlow := abs_squareThirdUnitInterior_low_le hn R F hM hF
  have hedge := abs_squareThirdUnitCenteredMass_sub_interior_le hn F hM hF
  change abs ((1/2:Real)*Finset.sum ((squareThirdUnitInterior n).filter (fun r => r <= R)) g)
    <= (R : Real)*M at hlow
  have he : squareThirdUnitCenteredMass n F -
      (1/2:Real)*Finset.sum ((squareThirdUnitInterior n).filter (fun r => R < r)) g =
      (squareThirdUnitCenteredMass n F - (1/2:Real)*Finset.sum (squareThirdUnitInterior n) g) +
      (1/2:Real)*Finset.sum ((squareThirdUnitInterior n).filter (fun r => r <= R)) g := by
    linarith only [hp]
  change abs (squareThirdUnitCenteredMass n F -
    (1/2:Real)*Finset.sum ((squareThirdUnitInterior n).filter (fun r => R < r)) g) <= _
  rw [he]
  have htri := abs_add_le
    (squareThirdUnitCenteredMass n F - (1/2:Real)*Finset.sum (squareThirdUnitInterior n) g)
    ((1/2:Real)*Finset.sum ((squareThirdUnitInterior n).filter (fun r => r <= R)) g)
  change abs (squareThirdUnitCenteredMass n F - (1/2:Real)*Finset.sum (squareThirdUnitInterior n) g)
    <= _ at hedge
  push_cast at hedge
  push_cast
  nlinarith only [htri, hlow, hedge]

/-- The actual Mangoldt mass reduces to the high interior with an explicit logarithmic cost. -/
theorem abs_squareThirdMangoldtCentered_sub_high_le {n : Nat} (hn : 100 <= n)
    (R : Nat) :
    abs (squareThirdUnitCenteredMass n ArithmeticFunction.vonMangoldt -
      (1/2:Real)*Finset.sum ((squareThirdUnitInterior n).filter (fun r => R < r))
        (fun r => (squareThirdSignedFringeKernel n r : Real)*
          modSixSignedWeight ArithmeticFunction.vonMangoldt r)) <=
      ((R+2*(n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1)+1 : Nat) : Real)*Real.log n := by
  apply abs_squareThirdUnitCenteredMass_sub_high_le hn
  next => exact Real.log_nonneg (by exact_mod_cast (show 1 <= n by omega))
  next =>
    intro r hr
    have hs := Finset.mem_Icc.mp hr
    have hY := squareThirdFringeSupport_lower_pos hn
    have hr0 : 0 < r := by omega
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact le_trans ArithmeticFunction.vonMangoldt_le_log
      (Real.log_le_log (by exact_mod_cast hr0) (by exact_mod_cast hs.2))

end Nat.PrimeSieve
