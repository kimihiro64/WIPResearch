/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalCounts
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalEndpointMass

/-!
# Weighted quadratic rows and pointwise endpoint fringes

Retain the complete signed endpoint ledger for arbitrary real weights. An
actual rounded fringe is covered by at most two modulus-six unit candidates;
fixed-factor rows inject into odd multiples of three times that factor. This
gives the uniform bound twice (floor(n/(3r)) + 1) for every n >= 100 and r > 0.
The bound is for the explicitly retained correction, not a replacement of
least-prime-owner counts by reciprocal densities.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- Weighted prefix in one residue class modulo six. -/
noncomputable def modSixWeightedPrefix (F : Nat -> Real) (a X : Nat) : Real :=
  Finset.sum ((Finset.range (X+1)).filter (fun p => p%6 = a)) F

/-- Every actual large-factor row point lies at least seven. -/
theorem squareThirdCofactorRow_ge_seven {n h p : Nat} (hn : 100 <= n)
    (hp : Membership.mem (squareThirdCofactorRow n h) p) : 7 <= p := by
  have hd := (mem_squareThirdCofactorRow n h p).mp hp
  have hpow := (Nat.nthRoot_lt_iff (by decide : Not (3 = 0))).mp hd.2.1
  by_contra hnot
  have hp6 : p <= 6 := by omega
  have hsq := Nat.mul_le_mul hp6 hp6
  have hcube := Nat.mul_le_mul hsq hp6
  nlinarith only [hn, hpow, hcube]

/-- Exact row sum plus its class-rounded lower prefix equals the upper prefix. -/
theorem sum_squareThirdRow_add_lower_prefix {n h : Nat} (hn : 100 <= n)
    (H : (squareThirdCofactorRow n h).Nonempty) (F : Nat -> Real) :
    Finset.sum (squareThirdCofactorRow n h) F +
      modSixWeightedPrefix F ((squareThirdFirst n h)%6) (squareThirdFirst n h-6) =
      modSixWeightedPrefix F ((squareThirdFirst n h)%6) (squareThirdLast n h) := by
  let L := squareThirdFirst n h
  let R := squareThirdLast n h
  let s := (Finset.range (R+1)).filter (fun p => p%6 = L%6)
  have hL : 7 <= L := squareThirdCofactorRow_ge_seven hn (squareThirdFirst_mem H)
  have hLR : L <= R := squareThirdFirst_le_last H
  have hrow : s.filter (fun p => L <= p) = squareThirdCofactorRow n h := by
    rw [squareThirdCofactorRow_eq_progression H]
    apply Finset.ext
    intro p
    simp only [s, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    change ((p < R+1 /\ p%6 = L%6) /\ L <= p) <-> ((L <= p /\ p <= R) /\ p%6 = L%6)
    omega
  have hlow : s.filter (fun p => Not (L <= p)) =
      (Finset.range (L-6+1)).filter (fun p => p%6 = L%6) := by
    apply Finset.ext
    intro p
    simp only [s, Finset.mem_filter, Finset.mem_range]
    omega
  have hsum := Finset.sum_filter_add_sum_filter_not s (fun p => L <= p) F
  rw [hrow, hlow] at hsum
  exact hsum

/-- Exact weighted row telescope with both original endpoint classes retained. -/
theorem sum_squareThirdRow_eq_prefix_difference {n h : Nat} (hn : 100 <= n)
    (H : (squareThirdCofactorRow n h).Nonempty) (F : Nat -> Real) :
    Finset.sum (squareThirdCofactorRow n h) F =
      modSixWeightedPrefix F ((squareThirdLast n h)%6) (squareThirdLast n h) -
      modSixWeightedPrefix F ((squareThirdFirst n h)%6) (squareThirdFirst n h-6) := by
  have hclass := squareThirdCofactorRow_mod_six (squareThirdLast_mem H) (squareThirdFirst_mem H)
  have hsum := sum_squareThirdRow_add_lower_prefix hn H F
  rw [hclass]
  linarith

/-- Every endpoint of an actual nonempty row belongs to the complete support. -/
theorem squareThirdEndpointKey_mem_support {n h : Nat}
    (hh : Membership.mem (squareThirdCenters n) h) (b : Bool) :
    Membership.mem (squareThirdEndpointSupport n) (squareThirdEndpointKey n h b) := by
  exact Finset.mem_image.mpr (Exists.intro (Prod.mk h b) (And.intro
    (Finset.mem_product.mpr (And.intro hh (Finset.mem_univ b))) rfl))

/-- Signed endpoint regrouping for an arbitrary real function on endpoint keys. -/
theorem sum_squareThirdEndpointCoefficient_mul (n : Nat) (f : Prod Nat Nat -> Real) :
    Finset.sum (squareThirdEndpointSupport n) (fun x => (squareThirdEndpointCoefficient n x : Real)*f x) =
      Finset.sum (squareThirdCenters n) (fun h => f (squareThirdEndpointKey n h true)-f (squareThirdEndpointKey n h false)) := by
  have hpoint (h : Nat) (hh : Membership.mem (squareThirdCenters n) h) (b : Bool) :
      Finset.sum (squareThirdEndpointSupport n)
        (fun x => (if squareThirdEndpointKey n h b = x then (1:Real) else 0)*f x) =
        f (squareThirdEndpointKey n h b) := by
    rw [Finset.sum_eq_single (squareThirdEndpointKey n h b)]
    next => simp
    next => intro x hx hne; simp [Ne.symm hne]
    next => intro hnot; exact False.elim (hnot (squareThirdEndpointKey_mem_support hh b))
  calc
    _ = Finset.sum (squareThirdEndpointSupport n) (fun x =>
        Finset.sum (squareThirdCenters n) (fun h =>
          (if squareThirdEndpointKey n h true = x then (1:Real) else 0)*f x -
          (if squareThirdEndpointKey n h false = x then (1:Real) else 0)*f x)) := by
      simp only [squareThirdEndpointCoefficient, Int.cast_sum, Int.cast_sub, Int.cast_ite,
        Int.cast_one, Int.cast_zero, Finset.sum_mul, sub_mul]
    _ = Finset.sum (squareThirdCenters n) (fun h =>
        Finset.sum (squareThirdEndpointSupport n) (fun x =>
          (if squareThirdEndpointKey n h true = x then (1:Real) else 0)*f x -
          (if squareThirdEndpointKey n h false = x then (1:Real) else 0)*f x)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.sum_sub_distrib, hpoint h hh true, hpoint h hh false]

/-- All actual weighted row sums equal the complete merged prefix ledger. -/
theorem sum_squareThirdRows_eq_merged_prefix {n : Nat} (hn : 100 <= n) (F : Nat -> Real) :
    Finset.sum (squareThirdCenters n) (fun h => Finset.sum (squareThirdCofactorRow n h) F) =
      Finset.sum (squareThirdEndpointSupport n) (fun x =>
        (squareThirdEndpointCoefficient n x : Real)*modSixWeightedPrefix F x.1 x.2) := by
  rw [sum_squareThirdEndpointCoefficient_mul]
  apply Finset.sum_congr rfl
  intro h hh
  have H := (Finset.mem_filter.mp hh).2
  exact sum_squareThirdRow_eq_prefix_difference hn H F

/-- The odd multiples of an odd divisor have the elementary interval capacity. -/
theorem card_oddMultiplesInSquare_le_div_add_one {d : Nat} (n : Nat) (hd : d%2 = 1) :
    (oddMultiplesInSquare n d).card <= n/d+1 := by
  have hd0 : 0 < d := by omega
  have hr := Nat.mod_lt n hd0
  have he := Nat.mod_add_div n d
  have hn : n < d*(n/d+1) := by nlinarith only [hr, he]
  have hu : n*n+2*n <= n*n+d*(2*(n/d+1)) := by nlinarith only [hn]
  have hdiv : (n*n+2*n)/d <= (n*n+d*(2*(n/d+1)))/d := Nat.div_le_div_right hu
  have hhalf : ((n*n+2*n)/d+1)/2 <= ((n*n+d*(2*(n/d+1)))/d+1)/2 :=
    Nat.div_le_div_right (Nat.add_le_add_right hdiv 1)
  rw [odd_multiple_floor_shift _ _ hd0] at hhalf
  have hcount := card_oddMultiplesInSquare n hd
  omega

/-- Every point in the rounded fringe is followed by an actual row point within six. -/
theorem squareThirdRoundedFringe_point {n h r : Nat} (hn : 100 <= n)
    (H : (squareThirdCofactorRow n h).Nonempty)
    (hlo : squareThirdFirst n h-6 < r) (hhi : r <= squareThirdLast n h) :
    exists p : Nat, Membership.mem (squareThirdCofactorRow n h) p /\ r <= p /\ p < r+6 := by
  let L := squareThirdFirst n h
  let R := squareThirdLast n h
  let e := (L%6+6-r%6)%6
  let p := r+e
  have he : e < 6 := Nat.mod_lt _ (by decide)
  have hpmod : p%6 = L%6 := by dsimp [p,e]; omega
  have hL : 7 <= L := squareThirdCofactorRow_ge_seven hn (squareThirdFirst_mem H)
  have hclass : R%6 = L%6 := squareThirdCofactorRow_mod_six (squareThirdLast_mem H) (squareThirdFirst_mem H)
  have hLp : L <= p := by change L-6 < r at hlo; dsimp [p] at *; omega
  have hpR : p <= R := by change r <= R at hhi; dsimp [p] at *; omega
  refine Exists.intro p (And.intro ?_ (And.intro (by dsimp [p]; omega) (by dsimp [p]; omega)))
  exact squareThirdCofactorRow_convex_mod_six (squareThirdFirst_mem H) (squareThirdLast_mem H) hLp hpR hpmod

/-- The at most two unit-class candidates in the six integers starting at r. -/
noncomputable def modSixUnitCandidates (r : Nat) : Finset Nat :=
  (Finset.Ico r (r+6)).filter (fun p => p%6 = 1 \/ p%6 = 5)

/-- Residue injectivity bounds the unit candidates in one modulus-six block. -/
theorem card_modSixUnitCandidates_le_two (r : Nat) : (modSixUnitCandidates r).card <= 2 := by
  have hcard : (modSixUnitCandidates r).card <= ({1,5} : Finset Nat).card := by
    apply Finset.card_le_card_of_injOn (fun p => p%6)
    next =>
      intro p hp
      have hm := (Finset.mem_filter.mp hp).2
      simpa using hm
    next =>
      intro p hp q hq heq
      change p%6 = q%6 at heq
      have hpi := Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1
      have hqi := Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1
      omega
  simpa using hcard

/-- Actual nonempty rows containing a specified smaller factor. -/
noncomputable def squareThirdFixedFactorRows (n p : Nat) : Finset Nat :=
  (squareThirdCenters n).filter (fun h => Membership.mem (squareThirdCofactorRow n h) p)

/-- Actual rows whose class-rounded endpoints straddle the specified index. -/
noncomputable def squareThirdFringeRows (n r : Nat) : Finset Nat :=
  (squareThirdCenters n).filter (fun h => squareThirdFirst n h-6 < r /\ r <= squareThirdLast n h)

/-- Fixed-factor rows inject into actual odd multiples of three times that factor. -/
theorem card_squareThirdFixedFactorRows_le {n p : Nat} (hpodd : p%2 = 1) :
    (squareThirdFixedFactorRows n p).card <= (oddMultiplesInSquare n (3*p)).card := by
  let g : Nat -> Nat := fun h => p*(p+2*(n+h-p))
  have hp0 : 0 < p := by omega
  apply Finset.card_le_card_of_injOn g
  next =>
    intro h hh
    have hp := (Finset.mem_filter.mp hh).2
    have hd := (mem_squareThirdCofactorRow n h p).mp hp
    have hc := hd.2.2.2.1
    have hqmod := hd.2.2.2.2
    have hqeq : p+2*(n+h-p) = 3*((p+2*(n+h-p))/3) := by omega
    have hdiv : Dvd.dvd (3*p) (g h) := by
      refine Exists.intro ((p+2*(n+h-p))/3) ?_
      calc
        g h = p*(p+2*(n+h-p)) := rfl
        _ = p*(3*((p+2*(n+h-p))/3)) := congrArg (fun z : Nat => p*z) hqeq
        _ = _ := by ring
    have hodd : (g h)%2 = 1 := by dsimp [g]; rw [Nat.mul_mod, hpodd]; omega
    have hupper : g h < n*n+2*n+1 := by dsimp [g]; nlinarith only [hc.interval_upper]
    change Membership.mem (oddMultiplesInSquare n (3*p)) (g h)
    simp only [oddMultiplesInSquare, oddMultiplesUpTo, Finset.mem_filter, Finset.mem_range]
    exact And.intro (And.intro hupper (And.intro hodd hdiv)) hc.interval_lower
  next =>
    intro h hh j hj heq
    have hp := (Finset.mem_filter.mp hh).2
    have hpd := (mem_squareThirdCofactorRow n h p).mp hp
    change p*(p+2*(n+h-p)) = p*(p+2*(n+j-p)) at heq
    have hco := Nat.eq_of_mul_eq_mul_left hp0 heq
    omega

/-- Every rounded-fringe row is covered by one of the two possible unit candidates. -/
theorem squareThirdFringeRows_subset_candidates {n r : Nat} (hn : 100 <= n) :
    squareThirdFringeRows n r <=
      (modSixUnitCandidates r).biUnion (squareThirdFixedFactorRows n) := by
  intro h hh
  have hd := Finset.mem_filter.mp hh
  have H := (Finset.mem_filter.mp hd.1).2
  choose p hp using squareThirdRoundedFringe_point hn H hd.2.1 hd.2.2
  have hpd := (mem_squareThirdCofactorRow n h p).mp hp.1
  have hpodd := hpd.2.2.2.1.odd_left
  apply Finset.mem_biUnion.mpr
  refine Exists.intro p (And.intro ?_ ?_)
  next =>
    apply Finset.mem_filter.mpr
    exact And.intro (Finset.mem_Ico.mpr hp.2) (by omega)
  next => exact Finset.mem_filter.mpr (And.intro hd.1 hp.1)

/-- Uniform pointwise capacity for all actual rounded-fringe rows. -/
theorem card_squareThirdFringeRows_le {n r : Nat} (hn : 100 <= n) (hr : 0 < r) :
    (squareThirdFringeRows n r).card <= 2*(n/(3*r)+1) := by
  have hsplit : (squareThirdFringeRows n r).card <=
      Finset.sum (modSixUnitCandidates r) (fun p => (squareThirdFixedFactorRows n p).card) :=
    le_trans (Finset.card_le_card (squareThirdFringeRows_subset_candidates hn)) (Finset.card_biUnion_le)
  have hpoint (p : Nat) (hp : Membership.mem (modSixUnitCandidates r) p) :
      (squareThirdFixedFactorRows n p).card <= n/(3*r)+1 := by
    have hd := Finset.mem_filter.mp hp
    have hpi := Finset.mem_Ico.mp hd.1
    have hpodd : p%2 = 1 := by omega
    have hraw := card_oddMultiplesInSquare_le_div_add_one n (show (3*p)%2 = 1 by omega)
    have hmul := Nat.div_mul_le_self n (3*p)
    have hden := Nat.mul_le_mul_left (n/(3*p)) (show 3*r <= 3*p by omega)
    have hdiv : n/(3*p) <= n/(3*r) := by
      apply (Nat.le_div_iff_mul_le (show 0 < 3*r by omega)).mpr
      nlinarith only [hmul,hden]
    exact le_trans (card_squareThirdFixedFactorRows_le hpodd) (by omega)
  calc
    _ <= Finset.sum (modSixUnitCandidates r) (fun p => (squareThirdFixedFactorRows n p).card) := hsplit
    _ <= Finset.sum (modSixUnitCandidates r) (fun _ => n/(3*r)+1) := Finset.sum_le_sum hpoint
    _ = (modSixUnitCandidates r).card*(n/(3*r)+1) := by simp
    _ <= _ := Nat.mul_le_mul_right _ (card_modSixUnitCandidates_le_two r)

/-- Ordinary finite weighted prefix, including zero for arbitrary weights. -/
noncomputable def squarePrefix (F : Nat -> Real) (X : Nat) : Real :=
  Finset.sum (Finset.range (X+1)) F

/-- Exact enclosing support for actual rounded-fringe indices. -/
noncomputable def squareThirdFringeSupport (n : Nat) : Finset Nat :=
  Finset.Icc (Nat.nthRoot 3 (n*n+2*n)-4) n

/-- Every occupied fringe index is positive and lies in the cube-cutoff support. -/
theorem squareThirdFringeRows_bounds {n r h : Nat} (hn : 100 <= n)
    (hh : Membership.mem (squareThirdFringeRows n r) h) :
    0 < r /\ Membership.mem (squareThirdFringeSupport n) r := by
  have hd := Finset.mem_filter.mp hh
  have H := (Finset.mem_filter.mp hd.1).2
  have hL := squareThirdCofactorRow_ge_seven hn (squareThirdFirst_mem H)
  have hLd := (mem_squareThirdCofactorRow n h _).mp (squareThirdFirst_mem H)
  have hRd := (mem_squareThirdCofactorRow n h _).mp (squareThirdLast_mem H)
  apply And.intro
  next => omega
  next =>
    apply Finset.mem_Icc.mpr
    exact And.intro (by omega) (by omega)

/-- A weighted prefix is the corresponding filtered part of every larger prefix. -/
theorem squarePrefix_eq_filter {X n : Nat} (hX : X <= n) (F : Nat -> Real) :
    squarePrefix F X =
      Finset.sum ((Finset.range (n+1)).filter (fun r => r <= X)) F := by
  have hs : (Finset.range (n+1)).filter (fun r => r <= X) = Finset.range (X+1) := by
    apply Finset.ext
    intro r
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hs]
  rfl

/-- A row's ordinary prefix difference retains precisely its rounded fringe. -/
theorem squareThirdPrefix_sub_eq_fringe {n h : Nat}
    (H : (squareThirdCofactorRow n h).Nonempty) (F : Nat -> Real) :
    squarePrefix F (squareThirdLast n h) - squarePrefix F (squareThirdFirst n h-6) =
      Finset.sum (Finset.range (n+1)) (fun r =>
        if squareThirdFirst n h-6 < r /\ r <= squareThirdLast n h then F r else 0) := by
  have hLd := (mem_squareThirdCofactorRow n h _).mp (squareThirdFirst_mem H)
  have hRd := (mem_squareThirdCofactorRow n h _).mp (squareThirdLast_mem H)
  have hLR := squareThirdFirst_le_last H
  rw [squarePrefix_eq_filter (by omega : squareThirdLast n h <= n),
    squarePrefix_eq_filter (by omega : squareThirdFirst n h-6 <= n)]
  simp only [Finset.sum_filter]
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hlo : r <= squareThirdFirst n h-6
  next =>
    have hhi : r <= squareThirdLast n h := by omega
    simp [hlo, hhi, show Not (squareThirdFirst n h-6 < r) by omega]
  next =>
    have hlt : squareThirdFirst n h-6 < r := by omega
    by_cases hhi : r <= squareThirdLast n h
    all_goals simp [hlo, hlt, hhi]

/-- Finite interchange turns all row prefix differences into actual fringe multiplicities. -/
theorem sum_squareThirdPrefix_eq_fringe (n : Nat) (F : Nat -> Real) :
    Finset.sum (squareThirdCenters n) (fun h =>
      squarePrefix F (squareThirdLast n h) - squarePrefix F (squareThirdFirst n h-6)) =
      Finset.sum (Finset.range (n+1)) (fun r => ((squareThirdFringeRows n r).card : Real)*F r) := by
  calc
    _ = Finset.sum (squareThirdCenters n) (fun h =>
        Finset.sum (Finset.range (n+1)) (fun r =>
          if squareThirdFirst n h-6 < r /\ r <= squareThirdLast n h then F r else 0)) := by
      apply Finset.sum_congr rfl
      intro h hh
      exact squareThirdPrefix_sub_eq_fringe (Finset.mem_filter.mp hh).2 F
    _ = Finset.sum (Finset.range (n+1)) (fun r =>
        Finset.sum (squareThirdCenters n) (fun h =>
          if squareThirdFirst n h-6 < r /\ r <= squareThirdLast n h then F r else 0)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [<- Finset.sum_filter]
      simp [squareThirdFringeRows]

/-- The full fringe correction is supported above the cube cutoff minus four. -/
theorem sum_squareThirdPrefix_eq_supported_fringe {n : Nat} (hn : 100 <= n) (F : Nat -> Real) :
    Finset.sum (squareThirdCenters n) (fun h =>
      squarePrefix F (squareThirdLast n h) - squarePrefix F (squareThirdFirst n h-6)) =
      Finset.sum (squareThirdFringeSupport n) (fun r => ((squareThirdFringeRows n r).card : Real)*F r) := by
  rw [sum_squareThirdPrefix_eq_fringe]
  symm
  apply Finset.sum_subset
  next =>
    intro r hr
    have hi := Finset.mem_Icc.mp hr
    exact Finset.mem_range.mpr (by omega)
  next =>
    intro r hr hout
    have hempty : squareThirdFringeRows n r = ({} : Finset Nat) := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro h hh
      exact hout (squareThirdFringeRows_bounds hn hh).2
    simp only [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]

/-- The complete signed endpoint correction equals its actual supported fringe mass. -/
theorem sum_squareThirdEndpointPrefix_eq_supported_fringe {n : Nat} (hn : 100 <= n)
    (F : Nat -> Real) :
    Finset.sum (squareThirdEndpointSupport n) (fun x =>
      (squareThirdEndpointCoefficient n x : Real)*squarePrefix F x.2) =
      Finset.sum (squareThirdFringeSupport n) (fun r => ((squareThirdFringeRows n r).card : Real)*F r) := by
  rw [sum_squareThirdEndpointCoefficient_mul]
  exact sum_squareThirdPrefix_eq_supported_fringe hn F

/-- The pointwise fringe capacity bounds arbitrary signed correction weights. -/
theorem abs_sum_squareThirdEndpointPrefix_le {n : Nat} (hn : 100 <= n) (F : Nat -> Real) :
    abs (Finset.sum (squareThirdEndpointSupport n) (fun x =>
      (squareThirdEndpointCoefficient n x : Real)*squarePrefix F x.2)) <=
      Finset.sum (squareThirdFringeSupport n) (fun r => (2*(n/(3*r)+1) : Nat)*abs (F r)) := by
  rw [sum_squareThirdEndpointPrefix_eq_supported_fringe hn]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum
  intro r hr
  by_cases hzero : (squareThirdFringeRows n r).card = 0
  next =>
    simp only [hzero, Nat.cast_zero, zero_mul, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  next =>
    have H := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
    choose h hh using H
    have hr0 := (squareThirdFringeRows_bounds hn hh).1
    have hbound := card_squareThirdFringeRows_le hn hr0
    have hcast : ((squareThirdFringeRows n r).card : Real) <= (2*(n/(3*r)+1) : Nat) := by
      exact_mod_cast hbound
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_right hcast (abs_nonneg _)

end Nat.PrimeSieve
