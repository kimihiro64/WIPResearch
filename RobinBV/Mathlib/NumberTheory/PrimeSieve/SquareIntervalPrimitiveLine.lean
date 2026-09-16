/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.FieldSimp
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalClockBound
/-!
# Primitive-line pruning of square-interval composite allowances

A genuine least-prime-owner factorization survives every primitive line-content
test. Arbitrary finite families of such tests therefore refine the high-factor
allowance in the complete finite-clock prime-count bound. Enlarging the family
can only improve that same bound. The two-sided family uses both floor and
ceiling numerators and deduplicates exact quotients.

The family is an arbitrary parameter, not an unproved distribution hypothesis.
Sharp Dirichlet approximation supplies a rejection witness with denominator
below every smaller prime factor when the proposed owner does not divide its
cofactor. This gives an explicit guaranteed detection range; the repeated-owner
exception remains separate. No uniform positivity of the bound is asserted.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- The line-content test agrees exactly with the cofactor test on a primitive direction. -/
theorem primitive_line_content_gcd (a q u v : Nat) (haq : Nat.Coprime a q) :
    Nat.gcd a (a*u+q*v) = Nat.gcd a v := by
  calc
    Nat.gcd a (a*u+q*v) = Nat.gcd (q*v+a*u) a := by
      rw [Nat.add_comm (a*u) (q*v), Nat.gcd_comm a]
    _ = Nat.gcd (q*v) a := Nat.gcd_add_mul_left_left a (q*v) u
    _ = Nat.gcd (v*q) a := by rw [Nat.mul_comm q v]
    _ = Nat.gcd v a := haq.symm.gcd_mul_right_cancel v
    _ = Nat.gcd a v := Nat.gcd_comm v a

/-- Any finite selection of primitive line-content tests is admissible. -/
def OwnerLineFamilyCompatible (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) (u v : Nat) : Prop :=
  forall z, Membership.mem (Gamma u v) z -> Nat.Coprime z.1 z.2 ->
    1 < Nat.gcd z.1 (z.1*u+z.2*v) -> u <= Nat.gcd z.1 (z.1*u+z.2*v)

/-- The family parameter selects tests, not an additional analytic hypothesis. -/
noncomputable def ownerLineFamilyHighFactorCells
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) (n T : Nat) (S R : Finset Nat) :
    Finset (Prod Nat Nat) :=
  (primeOwnerHighFactorCells n T S R).filter (fun x =>
    OwnerLineFamilyCompatible Gamma x.1 x.2)

/-- Both bounding numerators, automatically deduplicated at an exact quotient. -/
noncomputable def twoSidedOwnerDirections (Q u v : Nat) : Finset (Prod Nat Nat) :=
  (Finset.Icc 1 Q).biUnion (fun q =>
    (Finset.range 2).image (fun j =>
      Prod.mk (if j = 0 then q*v/u else (q*v+u-1)/u) q))

theorem ownerLineFamilyHighFactorCells_card_le
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) (n T : Nat) (S R : Finset Nat) :
    (ownerLineFamilyHighFactorCells Gamma n T S R).card <=
      (primeOwnerHighFactorCells n T S R).card :=
  Finset.card_filter_le _ _

/-- Adding tests decreases the same composite allowance. -/
theorem ownerLineFamilyHighFactorCells_card_antitone
    (Gamma Delta : Nat -> Nat -> Finset (Prod Nat Nat))
    (hsub : forall u v, Gamma u v <= Delta u v) (n T : Nat) (S R : Finset Nat) :
    (ownerLineFamilyHighFactorCells Delta n T S R).card <=
      (ownerLineFamilyHighFactorCells Gamma n T S R).card := by
  classical
  apply Finset.card_le_card
  intro x hx
  have hd := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine And.intro hd.1 ?_
  intro z hz hcop hg
  exact hd.2 z (hsub x.1 x.2 hz) hcop hg

/-- The actual least-prime-owner witness survives every auxiliary pruning condition. -/
theorem prefix_composite_mem_owner_or_line_family {n T m : Nat} (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hm : Membership.mem (oddSievedOwnerInSquare n 1 S) m)
    (hnp : Not (Nat.Prime m)) :
    Membership.mem ((lowClockOwners S T).biUnion (fun p => oddSievedOwnerInSquare n p S)) m \/
      Membership.mem ((ownerLineFamilyHighFactorCells Gamma n T S R).image (fun x => x.1*x.2)) m := by
  classical
  have hs := Finset.mem_filter.mp hm
  have hi := Finset.mem_filter.mp hs.1
  have hu := Finset.mem_filter.mp hi.1
  have htop := Finset.mem_range.mp hu.1
  have hm2 : 2 <= m := by nlinarith [hi.2]
  choose r hr using exists_minFac_mul hm2 hnp
  let p := m.minFac
  have hp : Nat.Prime p := Nat.minFac_prime (by omega)
  have he : m = p*r := hr.2
  have hpd : Dvd.dvd p m := Nat.minFac_dvd m
  have hrd : Dvd.dvd r m := by rw [he]; exact dvd_mul_left r p
  have hpr : p <= r := Nat.minFac_le_of_dvd hr.1 hrd
  have hbounds := semiprime_straddles hpr
    (show n*n < p*r by rw [<- he]; exact hi.2)
    (show p*r < (n+1)*(n+1) by rw [<- he]; nlinarith)
  have hpo : p%2 = 1 := hp.eq_two_or_odd.resolve_left (by
    intro h2
    rw [h2] at hpd
    have hz := Nat.mod_eq_zero_of_dvd hpd
    omega)
  have hnotS : Not (Membership.mem S p) := fun h => hs.2.2 p h hpd
  by_cases hlow : p <= T
  next =>
    apply Or.inl
    apply Finset.mem_biUnion.mpr
    refine Exists.intro p (And.intro ?_ ?_)
    next =>
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
        (And.intro hp (And.intro hpo hnotS)))
    next => exact Finset.mem_filter.mpr (And.intro hs.1 (And.intro hpd hs.2.2))
  next =>
    apply Or.inr
    apply Finset.mem_image.mpr
    refine Exists.intro (Prod.mk p r) (And.intro ?_ he.symm)
    have hprimitive : OwnerLineFamilyCompatible Gamma p r := by
      intro z _ hcop hg
      have heq := primitive_line_content_gcd z.1 z.2 p r hcop
      rw [heq] at hg
      rw [heq]
      exact Nat.minFac_le_of_dvd (by omega)
        (dvd_trans (Nat.gcd_dvd_right z.1 r) hrd)
    apply Finset.mem_filter.mpr
    refine And.intro ?_ hprimitive
    have hrle := Nat.le_of_dvd (show 0 < m by omega) hrd
    have hro : r%2 = 1 := by
      have ho := hu.2.1
      rw [he, Nat.mul_mod, hpo] at ho
      simpa using ho
    have hcell : Membership.mem (siftedHighFactorCells n T S) (Prod.mk p r) := by
      apply Finset.mem_filter.mpr
      refine And.intro (Finset.mem_product.mpr (And.intro
        (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by nlinarith)))) ?_
      refine And.intro (by omega) (And.intro (by rw [<- he]; exact hi.2)
        (And.intro (by rw [<- he]; nlinarith) (And.intro hpo (And.intro hro ?_))))
      intro ell hell
      exact And.intro (fun h => hs.2.2 ell hell (dvd_trans h hpd))
        (fun h => hs.2.2 ell hell (dvd_trans h hrd))
    apply Finset.mem_filter.mpr
    refine And.intro ?_ hp
    apply Finset.mem_filter.mpr
    refine And.intro hcell ?_
    intro ell hell
    refine And.intro ?_ ?_
    next =>
      intro held
      have hlem := dvd_trans held hpd
      have hpl := Nat.minFac_le_of_dvd (hR ell hell) hlem
      have hlp := Nat.le_of_dvd hp.pos held
      exact Nat.le_antisymm hlp hpl
    next =>
      intro hlt held
      have hlem := dvd_trans held hrd
      have hpl := Nat.minFac_le_of_dvd (hR ell hell) hlem
      omega

/-- Prefix survivors are covered by primes, low owner windows, and owner-pruned high cells. -/
theorem prefix_survivors_le_prime_owner_line_family_capacity {n T W : Nat} (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    (oddSievedOwnerInSquare n 1 S).card <= (squareIntervalPrimes n).card +
      (lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) +
      (ownerLineFamilyHighFactorCells Gamma n T S R).card := by
  classical
  let F := oddSievedOwnerInSquare n 1 S
  let B := F.filter (fun m => Not (Nat.Prime m))
  let rows := (lowClockOwners S T).biUnion (fun p => oddSievedOwnerInSquare n p S)
  let cells := (ownerLineFamilyHighFactorCells Gamma n T S R).image (fun x => x.1*x.2)
  have hsub : B <= Union.union rows cells := by
    intro m hm
    have hd := Finset.mem_filter.mp hm
    exact Finset.mem_union.mpr (prefix_composite_mem_owner_or_line_family Gamma S R hR hn hd.1 hd.2)
  have hrows : rows.card <= (lowClockOwners S T).sum
      (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) := by
    have h1 : rows.card <= (lowClockOwners S T).sum
        (fun p => (oddSievedOwnerInSquare n p S).card) := Finset.card_biUnion_le
    apply h1.trans
    apply Finset.sum_le_sum
    intro p hp
    exact card_oddSievedOwner_le_windowCapacity S (Finset.mem_filter.mp hp).2.2.1 hW0 hW
  have hbad : B.card <= rows.card + (ownerLineFamilyHighFactorCells Gamma n T S R).card := by
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le rows cells)
    have h2 : cells.card <= (ownerLineFamilyHighFactorCells Gamma n T S R).card := Finset.card_image_le
    omega
  have hprime : (F.filter Nat.Prime).card <= (squareIntervalPrimes n).card := by
    apply Finset.card_le_card
    intro m hm
    have hd := Finset.mem_filter.mp hm
    have hs := Finset.mem_filter.mp hd.1
    have hi := Finset.mem_filter.mp hs.1
    have hu := Finset.mem_filter.mp hi.1
    have htop := Finset.mem_range.mp hu.1
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by nlinarith))
      (And.intro hi.2 hd.2))
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) Nat.Prime
  change _ + B.card = F.card at hsplit
  change F.card <= _
  omega

/-- Complete prime-count enclosure retaining auxiliary least-owner constraints in the high lattice. -/
theorem prime_count_line_family_clock_bound {n T W : Nat} (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell /\ ell%2 = 1)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    oddOwnerProductDrift S*(n : Int)+prefixClockMinimum S <=
      (oddOwnerPeriod 1 S : Int)*
        (((squareIntervalPrimes n).card : Int)+
          ((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
          ((ownerLineFamilyHighFactorCells Gamma n T S R).card : Int)) := by
  classical
  have hprefix := prefixClockMinimum_le_defect S n hS
  have hcover := prefix_survivors_le_prime_owner_line_family_capacity (T := T) Gamma S R hR hn hW0 hW
  have hcast : ((oddSievedOwnerInSquare n 1 S).card : Int) <=
      ((squareIntervalPrimes n).card : Int)+
        ((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
        ((ownerLineFamilyHighFactorCells Gamma n T S R).card : Int) := by exact_mod_cast hcover
  have hscale := _root_.mul_le_mul_of_nonneg_left hcast
    (show (0 : Int) <= oddOwnerPeriod 1 S by omega)
  linarith


/-- A reduced positive rational witness with the sharp small-factor error scale. -/
theorem exists_reduced_small_factor_approximation {p r t : Nat}
    (hp : 0 < p) (hr : 2 <= r) (ht : p < r*t) :
    exists j q : Nat, 0 < j /\ 0 < q /\ q < r /\ Nat.Coprime j q /\
      (r : Int)*((q : Int)*t-(j : Int)*p) <= p /\
      (r : Int)*((j : Int)*p-(q : Int)*t) <= p := by
  have hr0 : 0 < r-1 := by omega
  choose x hx using Real.exists_rat_abs_sub_le_and_den_le
    ((t : Real)/p) hr0
  have hden : 0 < x.den := x.pos
  have hq : x.den < r := by omega
  have hpR : (0 : Real) < p := by exact_mod_cast hp
  have hrR : (0 : Real) < r := by exact_mod_cast (by omega : 0 < r)
  have hqR : (0 : Real) < x.den := by exact_mod_cast hden
  have hrr : ((r-1 : Nat) : Real)+1 = (r : Real) := by
    exact_mod_cast (by omega : r-1+1 = r)
  have he := hx.1
  rw [hrr, Rat.cast_def] at he
  have he1 := _root_.mul_le_mul_of_nonneg_right he (le_of_lt (mul_pos hrR hqR))
  have hcancel : (1/((r : Real)*x.den))*((r : Real)*x.den) = 1 := by
    field_simp
  rw [hcancel] at he1
  have hu := le_abs_self ((t : Real)/p-(x.num : Real)/x.den)
  have hl := neg_abs_le ((t : Real)/p-(x.num : Real)/x.den)
  have hup : ((t : Real)/p-(x.num : Real)/x.den)*((r : Real)*x.den) <= 1 :=
    (_root_.mul_le_mul_of_nonneg_right hu (le_of_lt (mul_pos hrR hqR))).trans he1
  have hlo : -((t : Real)/p-(x.num : Real)/x.den)*((r : Real)*x.den) <= 1 := by
    have hn := _root_.mul_le_mul_of_nonneg_right
      (show -((t : Real)/p-(x.num : Real)/x.den) <=
        abs ((t : Real)/p-(x.num : Real)/x.den) by linarith)
      (le_of_lt (mul_pos hrR hqR))
    exact hn.trans he1
  have hupp := _root_.mul_le_mul_of_nonneg_right hup hpR.le
  have hlop := _root_.mul_le_mul_of_nonneg_right hlo hpR.le
  have hclean : (((t : Real)/p-(x.num : Real)/x.den)*((r : Real)*x.den))*p =
      (r : Real)*((x.den : Real)*t-(x.num : Real)*p) := by
    field_simp
    <;> ring
  have hcleanneg : (-((t : Real)/p-(x.num : Real)/x.den)*((r : Real)*x.den))*p =
      (r : Real)*((x.num : Real)*p-(x.den : Real)*t) := by
    field_simp
    <;> ring
  rw [hclean, one_mul] at hupp
  rw [hcleanneg, one_mul] at hlop
  have huI : (r : Int)*((x.den : Int)*t-x.num*p) <= p := by exact_mod_cast hupp
  have hlI : (r : Int)*(x.num*p-(x.den : Int)*t) <= p := by exact_mod_cast hlop
  have hxpos : 0 < x.num := by
    have htR : (p : Real) < (r : Real)*t := by exact_mod_cast ht
    have hq1 : (1 : Real) <= x.den := by exact_mod_cast hden
    have ht0 : (0 : Real) <= t := by positivity
    have hrt : (r : Real)*t <= (r : Real)*((x.den : Real)*t) := by
      nlinarith
    have hj : (0 : Real) < x.num := by
      by_contra hn
      have hj0 : (x.num : Real) <= 0 := le_of_not_gt hn
      have hneg := mul_nonpos_of_nonpos_of_nonneg hj0 (mul_pos hrR hpR).le
      nlinarith
    exact_mod_cast hj
  refine Exists.intro x.num.natAbs (Exists.intro x.den
    (And.intro ?_ (And.intro hden (And.intro hq (And.intro x.reduced ?_)))))
  next => omega
  next =>
    have hj := Int.natAbs_of_nonneg hxpos.le
    constructor
    next => simpa only [hj] using huI
    next => simpa only [hj] using hlI


/-- A smaller prime divisor produces a primitive direction with nonzero error below p. -/
theorem exists_small_factor_primitive_direction {p r v : Nat}
    (hp : Nat.Prime p) (hr : Nat.Prime r) (hrp : r < p)
    (hpv : p < v) (hrv : Dvd.dvd r v) (hnot : Not (Dvd.dvd p v)) :
    exists a q : Nat, 0 < a /\ 0 < q /\ q < r /\ Nat.Coprime a q /\
      Dvd.dvd r (Nat.gcd a v) /\
      0 < ((q : Int)*v-(a : Int)*p).natAbs /\
      ((q : Int)*v-(a : Int)*p).natAbs < p := by
  choose t ht using hrv
  have hpt : p < r*t := by simpa only [ht] using hpv
  choose j q hj hq hqr hjq hu hl using
    exists_reduced_small_factor_approximation hp.pos hr.two_le hpt
  have hqnp : Not (Dvd.dvd p q) := by
    intro h
    have hle := Nat.le_of_dvd hq h
    omega
  have htnp : Not (Dvd.dvd p t) := by
    intro h
    apply hnot
    rw [ht]
    exact dvd_mul_of_dvd_right h r
  have hz : Not ((q : Int)*t-(j : Int)*p = 0) := by
    intro he
    have heN : q*t = j*p := by exact_mod_cast (sub_eq_zero.mp he)
    have hd : Dvd.dvd p (q*t) := by rw [heN]; exact dvd_mul_left p j
    exact (hp.dvd_mul.mp hd).elim hqnp htnp
  let D := ((q : Int)*t-(j : Int)*p).natAbs
  have hD0 : 0 < D := Int.natAbs_pos.mpr hz
  have hE : abs ((r : Int)*((q : Int)*t-(j : Int)*p)) <= (p : Int) :=
    abs_le.mpr (And.intro (by nlinarith [hl]) hu)
  rw [abs_mul, abs_of_nonneg (show (0 : Int) <= r by omega)] at hE
  have hEN : r*D <= p := by
    have hcast : ((r*D : Nat) : Int) <= (p : Int) := by
      simpa only [D, Nat.cast_mul, Int.natCast_natAbs] using hE
    exact_mod_cast hcast
  have hrnp : Not (Dvd.dvd r p) := by
    intro h
    have hd := (Nat.dvd_prime hp).mp h
    rcases hd with h | h
    next => have := hr.two_le; omega
    next => omega
  have hlt : r*D < p := by
    apply lt_of_le_of_ne hEN
    intro he
    apply hrnp
    rw [<- he]
    exact dvd_mul_right r D
  have hrq : Nat.Coprime r q := hr.coprime_iff_not_dvd.mpr (by
    intro h
    have hle := Nat.le_of_dvd hq h
    omega)
  have heq : (q : Int)*v-((r*j : Nat) : Int)*p =
      (r : Int)*((q : Int)*t-(j : Int)*p) := by
    rw [ht]
    push_cast
    ring
  have habs : ((q : Int)*v-((r*j : Nat) : Int)*p).natAbs = r*D := by
    rw [heq, Int.natAbs_mul]
    simp only [Int.natAbs_natCast, D]
  refine Exists.intro (r*j) (Exists.intro q
    (And.intro (Nat.mul_pos hr.pos hj) (And.intro hq (And.intro hqr
      (And.intro (hrq.mul_left hjq) (And.intro ?_ (And.intro ?_ ?_)))))))
  next => exact Nat.dvd_gcd (dvd_mul_right r j) (Exists.intro t ht)
  next => rw [habs]; exact Nat.mul_pos hr.pos hD0
  next => rw [habs]; exact hlt


/-- Nonzero sub-unit line error bounds the line content itself. -/
theorem gcd_lt_of_primitive_line_error {p a q v : Nat}
    (he0 : 0 < ((q : Int)*v-(a : Int)*p).natAbs)
    (hep : ((q : Int)*v-(a : Int)*p).natAbs < p) :
    Nat.gcd a v < p := by
  have hdv : Dvd.dvd (Nat.gcd a v) v := Nat.gcd_dvd_right a v
  have hda : Dvd.dvd (Nat.gcd a v) a := Nat.gcd_dvd_left a v
  have hdvI : Dvd.dvd ((Nat.gcd a v : Nat) : Int) (v : Int) := by exact_mod_cast hdv
  have hdaI : Dvd.dvd ((Nat.gcd a v : Nat) : Int) (a : Int) := by exact_mod_cast hda
  have hde : Dvd.dvd ((Nat.gcd a v : Nat) : Int) ((q : Int)*v-(a : Int)*p) :=
    _root_.dvd_sub (dvd_mul_of_dvd_right hdvI (q : Int))
      (dvd_mul_of_dvd_left hdaI (p : Int))
  exact (Nat.le_of_dvd he0 (Int.natCast_dvd.mp hde)).trans_lt hep

/-- An integral numerator with error less than the denominator is a floor or ceiling. -/
theorem eq_floor_or_ceil_of_line_error {p a q v : Nat} (hp : 0 < p)
    (hep : ((q : Int)*v-(a : Int)*p).natAbs < p) :
    a = q*v/p \/ a = (q*v+p-1)/p := by
  have heI : (((q : Int)*v-(a : Int)*p).natAbs : Int) < p := by exact_mod_cast hep
  rw [Int.natCast_natAbs] at heI
  have he := abs_lt.mp heI
  have hupper : q*v < a*p+p := by
    exact_mod_cast (show (q : Int)*v < (a : Int)*p+p by linarith [he.2])
  have hlower : a*p < q*v+p := by
    exact_mod_cast (show (a : Int)*p < (q : Int)*v+p by linarith [he.1])
  by_cases hle : a*p <= q*v
  next =>
    apply Or.inl
    exact (Nat.div_eq_of_lt_le hle (by nlinarith : q*v < (a+1)*p)).symm
  next =>
    apply Or.inr
    apply Eq.symm
    apply Nat.div_eq_of_lt_le
    next => omega
    next => nlinarith [Nat.sub_le (q*v+p) 1]

/-- Every smaller prime divisor is exposed by a denominator below that prime,
except when the proposed owner divides the cofactor. -/
theorem exists_small_factor_two_sided_rejection {p r v : Nat}
    (hp : Nat.Prime p) (hr : Nat.Prime r) (hrp : r < p)
    (hpv : p < v) (hrv : Dvd.dvd r v) (hnot : Not (Dvd.dvd p v)) :
    exists a q : Nat, 0 < q /\ q < r /\
      (a = q*v/p \/ a = (q*v+p-1)/p) /\ Nat.Coprime a q /\
      1 < Nat.gcd a v /\ Nat.gcd a v < p := by
  choose a q ha hq hqr hcop hrd he0 hep using
    exists_small_factor_primitive_direction hp hr hrp hpv hrv hnot
  have hgpos := Nat.gcd_pos_of_pos_left v ha
  have hrg := Nat.le_of_dvd hgpos hrd
  refine Exists.intro a (Exists.intro q (And.intro hq (And.intro hqr
    (And.intro (eq_floor_or_ceil_of_line_error hp.pos hep)
      (And.intro hcop (And.intro ?_ (gcd_lt_of_primitive_line_error he0 hep)))))))
  have := hr.two_le
  omega


/-- The uniform witness removes the false owner from the actual finite test family. -/
theorem not_ownerLineFamilyCompatible_of_small_factor {p r v Q : Nat}
    (hp : Nat.Prime p) (hr : Nat.Prime r) (hrp : r < p)
    (hpv : p < v) (hrv : Dvd.dvd r v) (hnot : Not (Dvd.dvd p v))
    (hQ : r <= Q+1) :
    Not (OwnerLineFamilyCompatible (twoSidedOwnerDirections Q) p v) := by
  classical
  choose a q hq hqr hround hcop hg1 hgp using
    exists_small_factor_two_sided_rejection hp hr hrp hpv hrv hnot
  have hmem : Membership.mem (twoSidedOwnerDirections Q p v) (Prod.mk a q) := by
    apply Finset.mem_biUnion.mpr
    refine Exists.intro q (And.intro (Finset.mem_Icc.mpr (And.intro (by omega) (by omega))) ?_)
    apply Finset.mem_image.mpr
    rcases hround with hfloor | hceil
    next =>
      refine Exists.intro 0 (And.intro (Finset.mem_range.mpr (by omega)) ?_)
      simp only [if_pos rfl]
      exact congrArg (fun z => Prod.mk z q) hfloor.symm
    next =>
      refine Exists.intro 1 (And.intro (Finset.mem_range.mpr (by omega)) ?_)
      simp only [show Not (1 = (0 : Nat)) by omega, if_false]
      exact congrArg (fun z => Prod.mk z q) hceil.symm
  intro hcompatible
  have hcontent := primitive_line_content_gcd a q p v hcop
  have hbig := hcompatible (Prod.mk a q) hmem hcop
    (show 1 < Nat.gcd a (a*p+q*v) by rw [hcontent]; exact hg1)
  change p <= Nat.gcd a (a*p+q*v) at hbig
  rw [hcontent] at hbig
  omega


end Nat.PrimeSieve
