/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalEndpointFiber

/-!
# Exact merged endpoint mass for divisor-three quadratic rows

The actual cube-cutoff rows have contiguous modulus-six support. Their
class-rounded min/max endpoints give a complete signed coefficient ledger.
Every near-row endpoint survives merging, so its total absolute mass is at
least four times floor(n/300) for n >= 100. This restricts this direct
large-owner/cofactor-three encoding, not all possible signed combinations
in a Legendre criterion. No prime-supply or distribution claim is made.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- First actual row point, with zero only for an empty row. -/
noncomputable def squareThirdFirst (n h : Nat) : Nat :=
  if H : (squareThirdCofactorRow n h).Nonempty then (squareThirdCofactorRow n h).min' H else 0

/-- Last actual row point, with zero only for an empty row. -/
noncomputable def squareThirdLast (n h : Nat) : Nat :=
  if H : (squareThirdCofactorRow n h).Nonempty then (squareThirdCofactorRow n h).max' H else 0

/-- The first endpoint is an actual point of every nonempty row. -/
theorem squareThirdFirst_mem {n h : Nat} (H : (squareThirdCofactorRow n h).Nonempty) :
    Membership.mem (squareThirdCofactorRow n h) (squareThirdFirst n h) := by
  rw [squareThirdFirst, dif_pos H]
  exact Finset.min'_mem _ H

/-- The last endpoint is an actual point of every nonempty row. -/
theorem squareThirdLast_mem {n h : Nat} (H : (squareThirdCofactorRow n h).Nonempty) :
    Membership.mem (squareThirdCofactorRow n h) (squareThirdLast n h) := by
  rw [squareThirdLast, dif_pos H]
  exact Finset.max'_mem _ H

/-- Actual row extrema occur in their correct order. -/
theorem squareThirdFirst_le_last {n h : Nat} (H : (squareThirdCofactorRow n h).Nonempty) :
    squareThirdFirst n h <= squareThirdLast n h := by
  rw [squareThirdFirst, dif_pos H]
  exact Finset.min'_le _ _ (squareThirdLast_mem H)

/-- All near-row factors are beyond the modulus-six initial boundary. -/
theorem squareThirdCofactorRow_large_of_near {n h p : Nat}
    (hn : 100 <= n) (hh : 100*h <= n)
    (hp : Membership.mem (squareThirdCofactorRow n h) p) : 7 <= p := by
  have hd := (mem_squareThirdCofactorRow n h p).mp hp
  have hcenter : p+(n+h-p) = n+h := by omega
  have ht := square_small_center_halfGap_bound hh (hd.2.2.2.1.halfGap_sq_lt (by omega))
  omega

/-- Complete finite support of nonempty divisor-three rows. -/
noncomputable def squareThirdCenters (n : Nat) : Finset Nat :=
  (Finset.Icc 1 (n*n+2*n)).filter (fun h => (squareThirdCofactorRow n h).Nonempty)

/-- The admissible near centers in the exact two nonzero classes. -/
noncomputable def squareThirdNearCenters (n : Nat) : Finset Nat :=
  (Finset.Icc 1 (n/100)).filter (fun h => Not ((n+h)%3 = 0))

/-- Every selected near center belongs to the complete nonempty-row support. -/
theorem squareThirdNearCenters_subset {n : Nat} (hn : 100 <= n) :
    squareThirdNearCenters n <= squareThirdCenters n := by
  intro h hh
  have hd := Finset.mem_filter.mp hh
  have hi := Finset.mem_Icc.mp hd.1
  have hbound : 100*h <= n := by omega
  have hne := squareThirdCofactorRow_nonempty hn hi.1 hbound hd.2
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_Icc.mpr (And.intro hi.1 (by nlinarith [Nat.zero_le (n*n)]))) hne)

/-- The finite center support contains every actual divisor-three row. -/
theorem squareThirdCofactorRow_center_bound {n h p : Nat}
    (hp : Membership.mem (squareThirdCofactorRow n h) p) :
    1 <= h /\ h <= n*n+2*n := by
  have hd := (mem_squareThirdCofactorRow n h p).mp hp
  have hc := hd.2.2.2.1
  have hcenter : p+(n+h-p) = n+h := by omega
  have hp1 := hd.1.1
  have hmul := Nat.mul_le_mul_right (n+h-p) hp1
  have hpSq : p <= p*p := by nlinarith
  have hgt := hc.center_gt
  constructor
  next => omega
  next => nlinarith [hc.interval_upper]

/-- The actual min or max before class-rounding the lower prefix. -/
noncomputable def squareThirdEndpointBase (n h : Nat) (b : Bool) : Nat :=
  if b then squareThirdLast n h else squareThirdFirst n h

/-- Residue and class-rounded endpoint, retaining both endpoint roles. -/
noncomputable def squareThirdEndpointKey (n h : Nat) (b : Bool) : Prod Nat Nat :=
  let p := squareThirdEndpointBase n h b
  Prod.mk (p%6) (if b then p else p-6)

/-- Either endpoint base is an actual row member. -/
theorem squareThirdEndpointBase_mem {n h : Nat} (H : (squareThirdCofactorRow n h).Nonempty)
    (b : Bool) : Membership.mem (squareThirdCofactorRow n h) (squareThirdEndpointBase n h b) := by
  cases b
  next => exact squareThirdFirst_mem H
  next => exact squareThirdLast_mem H

/-- A selected near-row endpoint cannot merge with another row or opposite endpoint role. -/
theorem squareThirdEndpointKey_injective_near {n h j : Nat} {b c : Bool}
    (hn : 100 <= n) (hh : 100*h <= n)
    (H : (squareThirdCofactorRow n h).Nonempty) (J : (squareThirdCofactorRow n j).Nonempty)
    (heq : squareThirdEndpointKey n h b = squareThirdEndpointKey n j c) : h = j /\ b = c := by
  have hp := squareThirdEndpointBase_mem H b
  have hr := squareThirdEndpointBase_mem J c
  have hlarge := squareThirdCofactorRow_large_of_near hn hh hp
  have hfst := congrArg Prod.fst heq
  have hsnd := congrArg Prod.snd heq
  change (squareThirdEndpointBase n h b)%6 = (squareThirdEndpointBase n j c)%6 at hfst
  have hj : h = j := by
    by_contra hne
    have hsep := squareThirdCofactorRow_separated hn hh hp hr hfst hne
    cases b <;> cases c <;> simp only [squareThirdEndpointKey, Bool.false_eq_true,
      if_false, if_true] at hsnd <;> omega
  subst j
  refine And.intro rfl ?_
  have hfirst := squareThirdFirst_mem H
  have hfirstpos := ((mem_squareThirdCofactorRow n h _).mp hfirst).1.1
  have horder := squareThirdFirst_le_last H
  cases b <;> cases c <;> simp only [squareThirdEndpointKey, squareThirdEndpointBase,
    Bool.false_eq_true, if_false, if_true] at hsnd <;> first | rfl | omega

/-- The full signed sum at an endpoint key over every nonempty row. -/
noncomputable def squareThirdEndpointCoefficient (n : Nat) (x : Prod Nat Nat) : Int :=
  Finset.sum (squareThirdCenters n) (fun h =>
    (if squareThirdEndpointKey n h true = x then 1 else 0) -
    (if squareThirdEndpointKey n h false = x then 1 else 0))

/-- Both endpoints of every nonempty row, merged as a finite set. -/
noncomputable def squareThirdEndpointSupport (n : Nat) : Finset (Prod Nat Nat) :=
  ((squareThirdCenters n).product (Finset.univ : Finset Bool)).image
    (fun hb => squareThirdEndpointKey n hb.1 hb.2)

/-- The two endpoints of the selected near rows. -/
noncomputable def squareThirdNearEndpointSupport (n : Nat) : Finset (Prod Nat Nat) :=
  ((squareThirdNearCenters n).product (Finset.univ : Finset Bool)).image
    (fun hb => squareThirdEndpointKey n hb.1 hb.2)

/-- Total absolute coefficient mass after complete endpoint merging. -/
noncomputable def squareThirdEndpointMass (n : Nat) : Int :=
  Finset.sum (squareThirdEndpointSupport n) (fun x => abs (squareThirdEndpointCoefficient n x))

/-- Every selected near endpoint has exact coefficient plus or minus one after full merging. -/
theorem squareThirdEndpointCoefficient_at_near {n h : Nat} (hn : 100 <= n)
    (hh : Membership.mem (squareThirdNearCenters n) h) (b : Bool) :
    squareThirdEndpointCoefficient n (squareThirdEndpointKey n h b) = if b then 1 else -1 := by
  have hbound : 100*h <= n := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1).2; omega
  have hmem := squareThirdNearCenters_subset hn hh
  have H := (Finset.mem_filter.mp hmem).2
  unfold squareThirdEndpointCoefficient
  rw [Finset.sum_eq_single h]
  next =>
    have hsame (c : Bool) : squareThirdEndpointKey n h c = squareThirdEndpointKey n h b <-> c = b := by
      constructor
      next => intro heq; exact (squareThirdEndpointKey_injective_near hn hbound H H heq).2
      next => intro heq; rw [heq]
    cases b <;> simp [hsame]
  next =>
    intro j hj hne
    have J := (Finset.mem_filter.mp hj).2
    have hno (c : Bool) : Not (squareThirdEndpointKey n j c = squareThirdEndpointKey n h b) := by
      intro heq
      exact hne (squareThirdEndpointKey_injective_near hn hbound H J heq.symm).1.symm
    simp only [if_neg (hno true), if_neg (hno false), sub_self]
  next => intro hnot; exact False.elim (hnot hmem)

/-- The selected endpoint support is contained in the complete finite support. -/
theorem squareThirdNearEndpointSupport_subset {n : Nat} (hn : 100 <= n) :
    squareThirdNearEndpointSupport n <= squareThirdEndpointSupport n := by
  apply Finset.image_subset_image
  exact Finset.product_subset_product (squareThirdNearCenters_subset hn) (le_refl _)

/-- Both endpoints of every selected row remain distinct. -/
theorem squareThirdNearEndpointSupport_card {n : Nat} (hn : 100 <= n) :
    (squareThirdNearEndpointSupport n).card = 2*(squareThirdNearCenters n).card := by
  have hinj : Set.InjOn (fun hb : Prod Nat Bool => squareThirdEndpointKey n hb.1 hb.2)
      ((squareThirdNearCenters n).product (Finset.univ : Finset Bool)) := by
    intro x hx y hy heq
    have hxnear := (Finset.mem_product.mp hx).1
    have hynear := (Finset.mem_product.mp hy).1
    have hh : 100*x.1 <= n := by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hxnear).1).2
      omega
    have H := (Finset.mem_filter.mp (squareThirdNearCenters_subset hn hxnear)).2
    have J := (Finset.mem_filter.mp (squareThirdNearCenters_subset hn hynear)).2
    have hk := squareThirdEndpointKey_injective_near hn hh H J heq
    exact Prod.ext hk.1 hk.2
  unfold squareThirdNearEndpointSupport
  rw [Finset.card_image_iff.mpr hinj, Finset.product_eq_sprod, Finset.card_product]
  simp
  omega

/-- Complete merged mass is at least twice the actual selected-row count. -/
theorem squareThirdEndpointMass_lower {n : Nat} (hn : 100 <= n) :
    2*((squareThirdNearCenters n).card : Int) <= squareThirdEndpointMass n := by
  have heq : Finset.sum (squareThirdNearEndpointSupport n)
      (fun x => abs (squareThirdEndpointCoefficient n x)) =
      ((squareThirdNearEndpointSupport n).card : Int) := by
    calc
      _ = Finset.sum (squareThirdNearEndpointSupport n) (fun _ => (1:Int)) := by
        apply Finset.sum_congr rfl
        intro x hx
        choose hb hh using Finset.mem_image.mp hx
        rw [<- hh.2, squareThirdEndpointCoefficient_at_near hn (Finset.mem_product.mp hh.1).1]
        cases hb.2 <;> norm_num
      _ = _ := by simp
  have hle : Finset.sum (squareThirdNearEndpointSupport n)
      (fun x => abs (squareThirdEndpointCoefficient n x)) <= squareThirdEndpointMass n :=
    Finset.sum_le_sum_of_subset_of_nonneg (squareThirdNearEndpointSupport_subset hn)
      (fun _ _ _ => abs_nonneg _)
  rw [heq, squareThirdNearEndpointSupport_card hn] at hle
  exact_mod_cast hle

/-- Two explicit nonforbidden center residues in each block of three. -/
def thirdNearCenterResidue (n : Nat) (b : Bool) : Nat :=
  if n%3 = 0 then (if b then 1 else 2)
  else if n%3 = 1 then (if b then 1 else 3)
  else (if b then 2 else 3)

/-- Each selected residue is between one and three and avoids the forbidden center class. -/
theorem thirdNearCenterResidue_properties (n : Nat) (b : Bool) :
    1 <= thirdNearCenterResidue n b /\ thirdNearCenterResidue n b <= 3 /\
      Not ((n+thirdNearCenterResidue n b)%3 = 0) := by
  cases b <;> dsimp [thirdNearCenterResidue] <;> split_ifs <;> omega

/-- The two selected center residues are distinct. -/
theorem thirdNearCenterResidue_injective (n : Nat) : Function.Injective (thirdNearCenterResidue n) := by
  intro b c heq
  cases b <;> cases c <;> dsimp [thirdNearCenterResidue] at heq <;>
    split_ifs at heq <;> first | rfl | omega

/-- An explicit two-of-three injection gives a uniform linear selected-row count. -/
theorem squareThirdNearCenters_card_lower (n : Nat) :
    2*(n/300) <= (squareThirdNearCenters n).card := by
  let s := (Finset.range (n/300)).product (Finset.univ : Finset Bool)
  let f : Prod Nat Bool -> Nat := fun x => 3*x.1+thirdNearCenterResidue n x.2
  have hmap : forall x, Membership.mem s x -> Membership.mem (squareThirdNearCenters n) (f x) := by
    intro x hx
    have ht := Finset.mem_range.mp (Finset.mem_product.mp hx).1
    have hr := thirdNearCenterResidue_properties n x.2
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_Icc.mpr (And.intro ?_ ?_)) ?_ <;> dsimp [f] <;> omega
  have hinj : Set.InjOn f s := by
    intro x hx y hy heq
    have hr := thirdNearCenterResidue_properties n x.2
    have hs := thirdNearCenterResidue_properties n y.2
    dsimp [f] at heq
    have ht : x.1 = y.1 := by omega
    have hb : thirdNearCenterResidue n x.2 = thirdNearCenterResidue n y.2 := by omega
    exact Prod.ext ht (thirdNearCenterResidue_injective n hb)
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  simpa [s, Finset.product_eq_sprod, Nat.mul_comm] using hcard

/-- The complete merged endpoint mass has a uniform linear lower bound. -/
theorem squareThirdEndpointMass_linear_lower {n : Nat} (hn : 100 <= n) :
    4*((n/300 : Nat) : Int) <= squareThirdEndpointMass n := by
  have hcount : 2*((n/300 : Nat) : Int) <= ((squareThirdNearCenters n).card : Int) :=
    by exact_mod_cast squareThirdNearCenters_card_lower n
  have hmass := squareThirdEndpointMass_lower hn
  omega

/-- The quadratic product is monotone in its smaller factor through the interval index. -/
theorem square_quadratic_factor_monotone {n h p r : Nat} (hpr : p <= r) (hr : r <= n) :
    p*(p+2*(n+h-p)) <= r*(r+2*(n+h-r)) := by
  have hpNh : p <= n+h := by omega
  have hrNh : r <= n+h := by omega
  have hd : (0:Int) <= (r:Int)-p := by omega
  have hs : (0:Int) <= 2*((n:Int)+h)-r-p := by omega
  have hprod := mul_nonneg hd hs
  have hcast : ((p*(p+2*(n+h-p)) : Nat) : Int) <= ((r*(r+2*(n+h-r)) : Nat) : Int) := by
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_sub hpNh, Nat.cast_sub hrNh]
    nlinarith only [hprod]
  exact_mod_cast hcast

/-- An intermediate point in the same unit class remains in the exact row. -/
theorem squareThirdCofactorRow_convex_mod_six {n h p r s : Nat}
    (hp : Membership.mem (squareThirdCofactorRow n h) p)
    (hr : Membership.mem (squareThirdCofactorRow n h) r)
    (hps : p <= s) (hsr : s <= r) (hmod : s%6 = p%6) :
    Membership.mem (squareThirdCofactorRow n h) s := by
  have hpd := (mem_squareThirdCofactorRow n h p).mp hp
  have hrd := (mem_squareThirdCofactorRow n h r).mp hr
  have hh := (squareThirdCofactorRow_center_bound hp).1
  have hsn : s <= n := by omega
  have hlo := lt_of_lt_of_le hpd.2.2.2.1.interval_lower (square_quadratic_factor_monotone hps hsn)
  have hhi := lt_of_le_of_lt (square_quadratic_factor_monotone hsr hrd.1.2) hrd.2.2.2.1.interval_upper
  have hpodd := hpd.2.2.2.1.odd_left
  apply (mem_squareThirdCofactorRow n h s).mpr
  refine And.intro (And.intro (by omega) hsn) (And.intro (by omega) (And.intro (by omega) (And.intro ?_ ?_)))
  next => exact { odd_left := by omega, gap_pos := by omega, interval_lower := hlo, interval_upper := hhi }
  next => omega

/-- Every nonempty actual row is exactly the progression between its extrema. -/
theorem squareThirdCofactorRow_eq_progression {n h : Nat} (H : (squareThirdCofactorRow n h).Nonempty) :
    squareThirdCofactorRow n h =
      (Finset.Icc (squareThirdFirst n h) (squareThirdLast n h)).filter
        (fun p => p%6 = (squareThirdFirst n h)%6) := by
  apply Finset.ext
  intro p
  constructor
  next =>
    intro hp
    have hfirst : squareThirdFirst n h <= p := by
      rw [squareThirdFirst, dif_pos H]
      exact Finset.min'_le _ _ hp
    have hlast : p <= squareThirdLast n h := by
      rw [squareThirdLast, dif_pos H]
      exact Finset.le_max' _ _ hp
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_Icc.mpr (And.intro hfirst hlast))
      (squareThirdCofactorRow_mod_six hp (squareThirdFirst_mem H)))
  next =>
    intro hp
    have hd := Finset.mem_filter.mp hp
    have hi := Finset.mem_Icc.mp hd.1
    exact squareThirdCofactorRow_convex_mod_six (squareThirdFirst_mem H) (squareThirdLast_mem H)
      hi.1 hi.2 hd.2

end Nat.PrimeSieve
