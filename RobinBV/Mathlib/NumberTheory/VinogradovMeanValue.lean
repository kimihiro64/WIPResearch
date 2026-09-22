/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Finite Vinogradov mean-value solution counts

This module defines the finite solution count for equal power sums and proves
the trivial cardinality estimate used as the small-parameter branch of the
degree-uniform Vinogradov mean-value induction.
-/

set_option autoImplicit false

open scoped BigOperators
open MvPolynomial

namespace MvPolynomial

/-- Evaluation of a symmetric power-sum polynomial is the corresponding finite
power sum. This is the Newton-identity bridge for finite vector data. -/
theorem aeval_psum_eq_finset_sum {sigma R S : Type*} [Fintype sigma]
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    (n : Nat) (f : sigma -> S) :
    aeval f (psum sigma R n) = Finset.univ.sum (fun i => f i ^ n) := by
  simp only [psum, aeval_sum, map_pow, aeval_X]

theorem aeval_mul_esymm_eq_of_lower {sigma R : Type*} [Fintype sigma]
    [CommRing R] (n : Nat) (f g : sigma -> R)
    (hesymm : forall i : Nat, i < n ->
      aeval f (esymm sigma R i) = aeval g (esymm sigma R i))
    (hpsum : forall i : Nat, i <= n ->
      aeval f (psum sigma R i) = aeval g (psum sigma R i)) :
    aeval f ((n : MvPolynomial sigma R) * esymm sigma R n) =
      aeval g ((n : MvPolynomial sigma R) * esymm sigma R n) := by
  rw [mul_esymm_eq_sum]
  simp only [map_mul, map_pow, map_neg, map_one, map_sum]
  apply congrArg (fun z : R => (-1) ^ (n + 1) * z)
  apply Finset.sum_congr rfl
  intro a ha
  have hlt : a.1 < n := (Finset.mem_filter.mp ha).2
  have hant : a.1 + a.2 = n := Finset.mem_antidiagonal.mp
    (Finset.mem_filter.mp ha).1
  have hle : a.2 <= n := by
    rw [<- hant]
    exact Nat.le_add_left _ _
  rw [hesymm a.1 hlt, hpsum a.2 hle]

theorem aeval_esymm_eq_of_lower_charZero {sigma R : Type*} [Fintype sigma]
    [CommRing R] [NoZeroDivisors R] [CharZero R]
    (n : Nat) (hn : 0 < n) (f g : sigma -> R)
    (hesymm : forall i : Nat, i < n ->
      aeval f (esymm sigma R i) = aeval g (esymm sigma R i))
    (hpsum : forall i : Nat, i <= n ->
      aeval f (psum sigma R i) = aeval g (psum sigma R i)) :
    aeval f (esymm sigma R n) = aeval g (esymm sigma R n) := by
  have hmul := aeval_mul_esymm_eq_of_lower n f g hesymm hpsum
  simp only [map_mul, map_natCast] at hmul
  have hz : (n : R) *
      (aeval f (esymm sigma R n) - aeval g (esymm sigma R n)) = 0 := by
    rw [mul_sub, hmul, sub_self]
  rcases mul_eq_zero.mp hz with hn0 | hzero
  next =>
    exact False.elim ((Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) hn0)
  next =>
    exact sub_eq_zero.mp hzero

/-- Newton recurrence cancellation over an arbitrary commutative ring when the
controlled degree is a unit. This is the modular replacement for the
characteristic-zero step in the p-adic Linnik argument. -/
theorem aeval_esymm_eq_of_lower_isUnit {sigma R : Type*} [Fintype sigma]
    [CommRing R] (n : Nat) (hn : IsUnit (n : R)) (f g : sigma -> R)
    (hesymm : forall i : Nat, i < n ->
      aeval f (esymm sigma R i) = aeval g (esymm sigma R i))
    (hpsum : forall i : Nat, i <= n ->
      aeval f (psum sigma R i) = aeval g (psum sigma R i)) :
    aeval f (esymm sigma R n) = aeval g (esymm sigma R n) := by
  have hmul := aeval_mul_esymm_eq_of_lower n f g hesymm hpsum
  simp only [map_mul, map_natCast] at hmul
  have hz : (n : R) *
      (aeval f (esymm sigma R n) - aeval g (esymm sigma R n)) = 0 := by
    rw [mul_sub, hmul, sub_self]
  exact sub_eq_zero.mp (hn.mul_right_eq_zero.mp hz)

/-- A positive degree below a prime is a unit modulo every positive power of
that prime. This supplies the unit hypothesis in modular Newton induction. -/
theorem zmod_natCast_isUnit_of_pos_lt_prime (p u n : Nat) (hp : p.Prime)
    (hu : 0 < u) (hn : 0 < n) (hnp : n < p) :
    IsUnit (n : ZMod (p ^ u)) := by
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp hu]
  intro hdiv
  exact (Nat.not_le_of_gt hnp) (Nat.le_of_dvd hn hdiv)

/-- Newton induction over a commutative ring in which every controlled
positive degree is a unit. This is the full symmetric-polynomial transport
needed for congruences modulo a prime power with prime larger than the degree. -/
theorem aeval_esymm_eq_of_power_sums_of_units {sigma R : Type*} [Fintype sigma]
    [CommRing R] (f g : sigma -> R)
    (hunit : forall n : Nat, 0 < n -> n <= Fintype.card sigma ->
      IsUnit (n : R))
    (hpsum : forall i : Nat, i <= Fintype.card sigma ->
      aeval f (psum sigma R i) = aeval g (psum sigma R i)) :
    forall n : Nat, n <= Fintype.card sigma ->
      aeval f (esymm sigma R n) = aeval g (esymm sigma R n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp [esymm]
    | succ n =>
      apply aeval_esymm_eq_of_lower_isUnit (n + 1)
        (hunit (n + 1) (Nat.succ_pos n) hn)
      next =>
        intro i hi
        exact ih i hi (Nat.le_trans (Nat.lt_succ_iff.mp hi)
          (Nat.le_trans (Nat.le_succ n) hn))
      next =>
        intro i hi
        exact hpsum i (Nat.le_trans hi hn)

/-- Modular Newton induction through a degree strictly below the prime.
This is the coefficient form of the congruence step in Lemma 24.2(b). -/
theorem zmod_aeval_esymm_eq_of_power_sums (p u q : Nat) (hp : p.Prime)
    (hu : 0 < u) (hqp : q < p) (f g : Fin q -> ZMod (p ^ u))
    (hpsum : forall i : Nat, i <= q ->
      aeval f (psum (Fin q) (ZMod (p ^ u)) i) =
        aeval g (psum (Fin q) (ZMod (p ^ u)) i)) :
    forall n : Nat, n <= q ->
      aeval f (esymm (Fin q) (ZMod (p ^ u)) n) =
        aeval g (esymm (Fin q) (ZMod (p ^ u)) n) := by
  have hunit : forall n : Nat, 0 < n -> n <= Fintype.card (Fin q) ->
      IsUnit (n : ZMod (p ^ u)) := by
    intro n hn hle
    apply zmod_natCast_isUnit_of_pos_lt_prime p u n hp hu hn
    exact Nat.lt_of_le_of_lt (by simpa only [Fintype.card_fin] using hle) hqp
  have hsum : forall i : Nat, i <= Fintype.card (Fin q) ->
      aeval f (psum (Fin q) (ZMod (p ^ u)) i) =
        aeval g (psum (Fin q) (ZMod (p ^ u)) i) := by
    intro i hi
    exact hpsum i (by simpa only [Fintype.card_fin] using hi)
  simpa only [Fintype.card_fin] using
    (aeval_esymm_eq_of_power_sums_of_units f g hunit hsum)

theorem aeval_esymm_eq_of_power_sums {sigma R : Type*} [Fintype sigma]
    [CommRing R] [NoZeroDivisors R] [CharZero R]
    (f g : sigma -> R)
    (hpsum : forall i : Nat, i <= Fintype.card sigma ->
      aeval f (psum sigma R i) = aeval g (psum sigma R i)) :
    forall n : Nat, n <= Fintype.card sigma ->
      aeval f (esymm sigma R n) = aeval g (esymm sigma R n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero =>
      simp [esymm]
    | succ n =>
      apply aeval_esymm_eq_of_lower_charZero (n + 1) (Nat.succ_pos n)
      intro i hi
      exact ih i hi (Nat.le_trans (Nat.lt_succ_iff.mp hi)
        (Nat.le_trans (Nat.le_succ n) hn))
      intro i hi
      exact hpsum i (Nat.le_trans hi hn)

theorem multiset_prod_X_sub_C_eq_of_esymm {sigma R : Type*} [Fintype sigma]
    [CommRing R] (f g : sigma -> R)
    (hesymm : forall n : Nat, n <= Fintype.card sigma ->
      aeval f (esymm sigma R n) = aeval g (esymm sigma R n)) :
    ((Finset.univ.val.map f).map (fun t => Polynomial.X - Polynomial.C t)).prod =
      ((Finset.univ.val.map g).map (fun t => Polynomial.X - Polynomial.C t)).prod := by
  rw [Multiset.prod_X_sub_X_eq_sum_esymm,
    Multiset.prod_X_sub_X_eq_sum_esymm]
  simp only [Multiset.card_map]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j <= Fintype.card sigma := Nat.lt_succ_iff.mp
    (Finset.mem_range.mp hj)
  have h := hesymm j hjle
  rw [aeval_esymm_eq_multiset_esymm] at h
  rw [aeval_esymm_eq_multiset_esymm] at h
  rw [h]

theorem multiset_eq_of_esymm {sigma R : Type*} [Fintype sigma]
    [CommRing R] [IsDomain R] (f g : sigma -> R)
    (hesymm : forall n : Nat, n <= Fintype.card sigma ->
      aeval f (esymm sigma R n) = aeval g (esymm sigma R n)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  have hprod := multiset_prod_X_sub_C_eq_of_esymm f g hesymm
  have hroots := congrArg Polynomial.roots hprod
  simpa only [Polynomial.roots_multiset_prod_X_sub_C] using hroots

/-- The root-polynomial congruence supplied by modular equal power sums.
This is the polynomial assertion used in Linnik's Lemma 24.4. -/
theorem zmod_multiset_prod_X_sub_C_eq_of_power_sums (p u q : Nat)
    (hp : p.Prime) (hu : 0 < u) (hqp : q < p)
    (f g : Fin q -> ZMod (p ^ u))
    (hpsum : forall i : Nat, i <= q ->
      aeval f (psum (Fin q) (ZMod (p ^ u)) i) =
        aeval g (psum (Fin q) (ZMod (p ^ u)) i)) :
    ((Finset.univ.val.map f).map
      (fun t => Polynomial.X - Polynomial.C t)).prod =
      ((Finset.univ.val.map g).map
        (fun t => Polynomial.X - Polynomial.C t)).prod := by
  apply multiset_prod_X_sub_C_eq_of_esymm f g
  simpa only [Fintype.card_fin] using
    (zmod_aeval_esymm_eq_of_power_sums p u q hp hu hqp f g hpsum)

/-- Evaluating the modular root-polynomial congruence at a coordinate of the
second tuple gives the product-zero relation used in Linnik's root lift. -/
theorem zmod_root_product_eq_zero_of_power_sums (p u q : Nat)
    (hp : p.Prime) (hu : 0 < u) (hqp : q < p)
    (f g : Fin q -> ZMod (p ^ u))
    (hpsum : forall i : Nat, i <= q ->
      aeval f (psum (Fin q) (ZMod (p ^ u)) i) =
        aeval g (psum (Fin q) (ZMod (p ^ u)) i)) (s : Fin q) :
    ((Finset.univ.val.map f).map (fun t => g s - t)).prod = 0 := by
  have hpoly := zmod_multiset_prod_X_sub_C_eq_of_power_sums
    p u q hp hu hqp f g hpsum
  have heval := congrArg (Polynomial.eval (g s)) hpoly
  have hzero : ((Finset.univ.val.map g).map (fun t => g s - t)).prod = 0 := by
    rw [Multiset.prod_eq_zero]
    apply Multiset.mem_map.mpr
    refine Exists.intro (g s) ?_
    constructor
    next =>
      apply Multiset.mem_map.mpr
      exact Exists.intro s (And.intro (Finset.mem_univ s) rfl)
    next => simp
  have heval' : ((Finset.univ.val.map f).map (fun t => g s - t)).prod =
      ((Finset.univ.val.map g).map (fun t => g s - t)).prod := by
    simpa only [Polynomial.eval_multiset_prod, Multiset.map_map,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Function.comp_apply] using heval
  exact heval'.trans hzero

end MvPolynomial

namespace Finset

/-- Pairs of finite vectors with the same value multiset have at most `m!`
second coordinates for each first coordinate. This is the finite-rearrangement
count in the diagonal branch of the Vinogradov mean-value argument. -/
theorem equal_multiset_pair_count_le_factorial (m X : Nat) :
    (((Finset.univ : Finset (Fin m -> Fin X)).product
      (Finset.univ : Finset (Fin m -> Fin X))).filter
      (fun fg : Prod (Fin m -> Fin X) (Fin m -> Fin X) =>
        Finset.univ.val.map fg.1 = Finset.univ.val.map fg.2)).card <=
      X ^ m * m.factorial := by
  classical
  let source : Finset (Prod (Fin m -> Fin X) (Fin m -> Fin X)) :=
    (Finset.univ : Finset (Fin m -> Fin X)).product
      (Finset.univ : Finset (Fin m -> Fin X))
  let target : Finset (Prod (Fin m -> Fin X) (Fin m.factorial)) :=
    (Finset.univ : Finset (Fin m -> Fin X)).product Finset.univ
  have htarget : target.card = X ^ m * m.factorial := by
    simp [target]
  rw [show ((Finset.univ : Finset (Fin m -> Fin X)).product
      (Finset.univ : Finset (Fin m -> Fin X))).filter
      (fun fg : Prod (Fin m -> Fin X) (Fin m -> Fin X) =>
        Finset.univ.val.map fg.1 = Finset.univ.val.map fg.2) =
      source.filter (fun fg : Prod (Fin m -> Fin X) (Fin m -> Fin X) =>
        Finset.univ.val.map fg.1 = Finset.univ.val.map fg.2) by rfl]
  rw [<- htarget]
  have hperm : forall fg : Prod (Fin m -> Fin X) (Fin m -> Fin X),
      Finset.univ.val.map fg.1 = Finset.univ.val.map fg.2 ->
      (List.ofFn fg.2).Perm (List.ofFn fg.1) := by
    intro fg hfg
    apply Multiset.coe_eq_coe.mp
    simpa only [Fin.univ_val_map] using hfg.symm
  let S : Type := {fg : Prod (Fin m -> Fin X) (Fin m -> Fin X) //
    Membership.mem (source.filter (fun z : Prod (Fin m -> Fin X) (Fin m -> Fin X) =>
      Finset.univ.val.map z.1 = Finset.univ.val.map z.2)) fg}
  let rawIndex : forall z : S,
      Fin ((List.ofFn z.val.1).permutations.length) := fun z =>
    Classical.choose (List.mem_iff_get.mp (List.mem_permutations.mpr
      (hperm z.val (Finset.mem_filter.mp z.property).2)))
  have rawIndex_spec : forall z : S,
      (List.ofFn z.val.1).permutations.get (rawIndex z) = List.ofFn z.val.2 := by
    intro z
    exact Classical.choose_spec (List.mem_iff_get.mp (List.mem_permutations.mpr
      (hperm z.val (Finset.mem_filter.mp z.property).2)))
  let index : forall z : S, Fin m.factorial := fun z =>
    Fin.cast (by
      rw [List.length_permutations]
      simp) (rawIndex z)
  let encode : S -> Prod (Fin m -> Fin X) (Fin m.factorial) := fun z =>
    (z.val.1, index z)
  have hencode : Function.Injective encode := by
    intro a b hab
    change (a.val.1, index a) = (b.val.1, index b) at hab
    have hfirst : a.val.1 = b.val.1 := congrArg
      (fun z : Prod (Fin m -> Fin X) (Fin m.factorial) => z.1) hab
    have hindex : (rawIndex a).val = (rawIndex b).val := by
      have h := congrArg
        (fun z : Prod (Fin m -> Fin X) (Fin m.factorial) => z.2.val) hab
      exact h
    apply Subtype.ext
    apply Prod.ext
    next => exact hfirst
    next =>
      apply List.ofFn_injective
      rw [<- rawIndex_spec a, <- rawIndex_spec b]
      have get_transport : forall {alpha : Type} (l1 l2 : List alpha)
          (hl : l1 = l2) (i : Fin l1.length) (j : Fin l2.length),
          i.val = j.val -> l1.get i = l2.get j := by
        intro alpha l1 l2 hl i j hij
        subst l2
        have hfin : i = j := Fin.ext hij
        rw [hfin]
      exact get_transport (List.ofFn a.val.1).permutations
        (List.ofFn b.val.1).permutations
        (congrArg List.permutations (congrArg List.ofFn hfirst))
        (rawIndex a) (rawIndex b) hindex
  have hcard := Fintype.card_le_of_injective encode hencode
  calc
    _ = Fintype.card S := (Fintype.card_coe _).symm
    _ <= Fintype.card (Prod (Fin m -> Fin X) (Fin m.factorial)) := hcard
    _ = target.card := by simp [target]

/-- Equality of the positive power sums through the vector length forces
equality of the original finite value multisets. The proof transports the
natural equations into the characteristic-zero Newton/Vieta argument. -/
theorem nat_multiset_eq_of_power_sums (k : Nat) (f g : Fin k -> Nat)
    (hpow : forall j : Fin k,
      Finset.univ.sum (fun i => f i ^ (j.val + 1)) =
        Finset.univ.sum (fun i => g i ^ (j.val + 1))) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  let fr : Fin k -> Int := fun i => (f i : Int)
  let gr : Fin k -> Int := fun i => (g i : Int)
  have hpsum : forall i : Nat, i <= k ->
      aeval fr (MvPolynomial.psum (Fin k) Int i) =
        aeval gr (MvPolynomial.psum (Fin k) Int i) := by
    intro i hi
    rw [MvPolynomial.aeval_psum_eq_finset_sum,
      MvPolynomial.aeval_psum_eq_finset_sum]
    cases i with
    | zero => simp
    | succ j =>
      have hj : j < k := Nat.lt_of_succ_le hi
      let jj : Fin k := Fin.mk j hj
      have h := hpow jj
      simpa only [jj, Fin.mk_val, Nat.cast_sum, Nat.cast_pow] using
        congrArg (fun z : Nat => (z : Int)) h
  have hesymm := MvPolynomial.aeval_esymm_eq_of_power_sums fr gr (fun i hi =>
    hpsum i (by simpa using hi))
  have hrat := MvPolynomial.multiset_eq_of_esymm fr gr hesymm
  apply (Multiset.map_eq_map (f := fun n : Nat => (n : Int))
    Nat.cast_injective).mp
  simpa only [Multiset.map_map, fr, gr, Function.comp_apply] using hrat

/-- The diagonal (`m = k`) affine transport: an affine change of variables
preserves equality of all positive power sums through the vector length.
The general Lemma 24.1(d) still requires its separate binomial proof. -/
theorem affine_nat_power_sums_eq_of_power_sums (k q r : Nat) (f g : Fin k -> Nat)
    (hpow : forall j : Fin k,
      Finset.univ.sum (fun i => f i ^ (j.val + 1)) =
        Finset.univ.sum (fun i => g i ^ (j.val + 1))) :
    forall j : Fin k,
      Finset.univ.sum (fun i => (q * f i + r) ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (q * g i + r) ^ (j.val + 1)) := by
  have hmultiset := nat_multiset_eq_of_power_sums k f g hpow
  intro j
  have hmap := congrArg (Multiset.map (fun x : Nat => (q * x + r) ^ (j.val + 1)))
    hmultiset
  have hmap' : Finset.univ.val.map (fun i => (q * f i + r) ^ (j.val + 1)) =
      Finset.univ.val.map (fun i => (q * g i + r) ^ (j.val + 1)) := by
    simpa only [Multiset.map_map, Function.comp_apply] using hmap
  change (Finset.univ.val.map (fun i => (q * f i + r) ^ (j.val + 1))).sum =
    (Finset.univ.val.map (fun i => (q * g i + r) ^ (j.val + 1))).sum
  exact congrArg Multiset.sum hmap'

/-- The inverse diagonal affine transport: for a positive dilation, equality
after the affine change forces equality before it. -/
theorem power_sums_eq_of_affine_nat_power_sums_eq (k q r : Nat) (hq : 0 < q)
    (f g : Fin k -> Nat)
    (hpow : forall j : Fin k,
      Finset.univ.sum (fun i => (q * f i + r) ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (q * g i + r) ^ (j.val + 1))) :
    forall j : Fin k,
      Finset.univ.sum (fun i => f i ^ (j.val + 1)) =
        Finset.univ.sum (fun i => g i ^ (j.val + 1)) := by
  have htrans := nat_multiset_eq_of_power_sums k
    (fun i => q * f i + r) (fun i => q * g i + r) hpow
  have hinj : Function.Injective (fun x : Nat => q * x + r) := by
    intro x y hxy
    apply Nat.eq_of_mul_eq_mul_left hq
    exact Nat.add_right_cancel hxy
  have hmult : Finset.univ.val.map f = Finset.univ.val.map g := by
    apply (Multiset.map_eq_map hinj).mp
    simpa only [Multiset.map_map, Function.comp_apply] using htrans
  intro j
  have hmap := congrArg (Multiset.map (fun x : Nat => x ^ (j.val + 1))) hmult
  have hmap' : Finset.univ.val.map (fun i => f i ^ (j.val + 1)) =
      Finset.univ.val.map (fun i => g i ^ (j.val + 1)) := by
    simpa only [Multiset.map_map, Function.comp_apply] using hmap
  change (Finset.univ.val.map (fun i => f i ^ (j.val + 1))).sum =
    (Finset.univ.val.map (fun i => g i ^ (j.val + 1))).sum
  exact congrArg Multiset.sum hmap'

/-- Affine embedding of a finite interval into the enclosing finite interval. -/
def affineFin (q r X : Nat) (x : Fin X) : Fin (q * X + r + 1) :=
  Fin.mk (q * x.val + r) (Nat.lt_succ_of_le
    (Nat.add_le_add_right (Nat.mul_le_mul_left q x.isLt.le) r))

/-- A positive affine map preserves and reflects the diagonal finite
equal-power-sum system. -/
theorem affineFin_power_sums_iff (k q r X : Nat) (hq : 0 < q)
    (f g : Fin k -> Fin X) :
    (forall j : Fin k,
      Finset.univ.sum (fun i => (f i).val ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (g i).val ^ (j.val + 1))) <->
    (forall j : Fin k,
      Finset.univ.sum (fun i => (affineFin q r X (f i)).val ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (affineFin q r X (g i)).val ^ (j.val + 1))) := by
  constructor
  next =>
    intro h
    simpa only [affineFin, Fin.mk_val] using
      affine_nat_power_sums_eq_of_power_sums k q r
        (fun i => (f i).val) (fun i => (g i).val) h
  next =>
    intro h
    simpa only [affineFin, Fin.mk_val] using
      power_sums_eq_of_affine_nat_power_sums_eq k q r hq
        (fun i => (f i).val) (fun i => (g i).val) h

/-- Pointwise affine map for a VMVT vector. -/
def affineFinVector (k q r X : Nat) (f : Fin k -> Fin X) :
    Fin k -> Fin (q * X + r + 1) := fun i => affineFin q r X (f i)

/-- A positive affine map is injective on diagonal VMVT vectors. -/
theorem affineFinVector_injective (k q r X : Nat) (hq : 0 < q) :
    Function.Injective (affineFinVector k q r X) := by
  intro f g hfg
  funext i
  apply Fin.ext
  have h := congrArg (fun z : Fin (q * X + r + 1) => z.val)
    (congrFun hfg i)
  dsimp only [affineFinVector, affineFin, Fin.mk_val] at h
  apply Nat.eq_of_mul_eq_mul_left hq
  exact Nat.add_right_cancel h

/-- Componentwise positive affine map on a pair of VMVT vectors. -/
def affineFinPair (m q r X : Nat) :
    Prod (Fin m -> Fin X) (Fin m -> Fin X) ->
      Prod (Fin m -> Fin (q * X + r + 1)) (Fin m -> Fin (q * X + r + 1)) :=
  fun fg => (affineFinVector m q r X fg.1, affineFinVector m q r X fg.2)

/-- The affine pair map is injective for positive dilation. -/
theorem affineFinPair_injective (m q r X : Nat) (hq : 0 < q) :
    Function.Injective (affineFinPair m q r X) := by
  intro a b hab
  apply Prod.ext
  next =>
    apply affineFinVector_injective m q r X hq
    exact congrArg Prod.fst hab
  next =>
    apply affineFinVector_injective m q r X hq
    exact congrArg Prod.snd hab

/-- The exact binomial expansion needed for the general (`m` arbitrary)
affine power-sum transport. Every coefficient and the zero-th power-sum term
is retained for the subsequent induction on the controlled degree. -/
theorem affine_power_sum_binomial (m q r j : Nat) (f : Fin m -> Nat) :
    Finset.univ.sum (fun i => (q * f i + r) ^ j) =
      Finset.sum (Finset.range (j + 1)) (fun l =>
        Nat.choose j l * q ^ l * r ^ (j - l) *
          Finset.univ.sum (fun i => f i ^ l)) := by
  simp_rw [add_pow, mul_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  calc
    Finset.sum Finset.univ (fun i => q ^ l * f i ^ l * r ^ (j - l) *
        Nat.choose j l) =
      Finset.sum Finset.univ (fun i =>
        Nat.choose j l * q ^ l * r ^ (j - l) * f i ^ l) := by
          apply Finset.sum_congr rfl
          intro i hi
          ac_rfl
    _ = Nat.choose j l * q ^ l * r ^ (j - l) *
        Finset.sum Finset.univ (fun i => f i ^ l) := by
          rw [Finset.mul_sum]

/-- The general forward transport in Lemma 24.1(d). The vector length `m`
is independent of the number `k` of controlled positive power sums. -/
theorem affine_nat_power_sums_eq_of_power_sums_general (m k q r : Nat)
    (f g : Fin m -> Nat)
    (hpow : forall j : Fin k,
      Finset.univ.sum (fun i => f i ^ (j.val + 1)) =
        Finset.univ.sum (fun i => g i ^ (j.val + 1))) :
    forall j : Fin k,
      Finset.univ.sum (fun i => (q * f i + r) ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (q * g i + r) ^ (j.val + 1)) := by
  intro j
  rw [affine_power_sum_binomial, affine_power_sum_binomial]
  apply Finset.sum_congr rfl
  intro l hl
  cases l with
  | zero => simp
  | succ t =>
    have ht : t < k := by
      have hle : t + 1 <= j.val + 1 := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hl)
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self t)
        (Nat.le_trans hle j.isLt)
    rw [hpow (Fin.mk t ht)]

/-- The triangular form of the binomial expansion: degree `t + 1` is its
positive leading coefficient times the original degree `t + 1` power sum,
plus only lower-degree terms. -/
theorem affine_power_sum_binomial_succ (m q r t : Nat) (f : Fin m -> Nat) :
    Finset.univ.sum (fun i => (q * f i + r) ^ (t + 1)) =
      Finset.sum (Finset.range (t + 1)) (fun l =>
        Nat.choose (t + 1) l * q ^ l * r ^ (t + 1 - l) *
          Finset.univ.sum (fun i => f i ^ l)) +
      q ^ (t + 1) * Finset.univ.sum (fun i => f i ^ (t + 1)) := by
  rw [affine_power_sum_binomial]
  rw [Finset.sum_range_succ]
  simp

/-- The general inverse transport in Lemma 24.1(d). For a positive dilation,
equality of the first `k` affine power sums implies equality of the original
power sums for vectors of arbitrary common length `m`. -/
theorem power_sums_eq_of_affine_nat_power_sums_eq_general (m k q r : Nat)
    (hq : 0 < q) (f g : Fin m -> Nat)
    (hpow : forall j : Fin k,
      Finset.univ.sum (fun i => (q * f i + r) ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (q * g i + r) ^ (j.val + 1))) :
    forall j : Fin k,
      Finset.univ.sum (fun i => f i ^ (j.val + 1)) =
        Finset.univ.sum (fun i => g i ^ (j.val + 1)) := by
  have hall : forall n : Nat, n <= k ->
      Finset.univ.sum (fun i => f i ^ n) =
        Finset.univ.sum (fun i => g i ^ n) := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simp
      | succ t =>
        have ht : t < k := Nat.lt_of_succ_le hn
        have htrans := hpow (Fin.mk t ht)
        change Finset.univ.sum (fun i => (q * f i + r) ^ (t + 1)) =
          Finset.univ.sum (fun i => (q * g i + r) ^ (t + 1)) at htrans
        rw [affine_power_sum_binomial_succ,
          affine_power_sum_binomial_succ] at htrans
        have hlow :
            Finset.sum (Finset.range (t + 1)) (fun l =>
              Nat.choose (t + 1) l * q ^ l * r ^ (t + 1 - l) *
                Finset.univ.sum (fun i => f i ^ l)) =
              Finset.sum (Finset.range (t + 1)) (fun l =>
              Nat.choose (t + 1) l * q ^ l * r ^ (t + 1 - l) *
                Finset.univ.sum (fun i => g i ^ l)) := by
          apply Finset.sum_congr rfl
          intro l hl
          have hlt : l < t + 1 := Finset.mem_range.mp hl
          have hle : l <= k := Nat.le_trans (Nat.le_of_lt hlt) hn
          have heq : Finset.univ.sum (fun i => f i ^ l) =
              Finset.univ.sum (fun i => g i ^ l) := ih l hlt hle
          exact congrArg (fun z : Nat =>
            Nat.choose (t + 1) l * q ^ l * r ^ (t + 1 - l) * z) heq
        have hsame := (congrArg (fun z : Nat => z +
          q ^ (t + 1) * Finset.univ.sum (fun i => f i ^ (t + 1)))
          hlow.symm).trans htrans
        have hlead := Nat.add_left_cancel hsame
        exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hq) hlead
  intro j
  exact hall (j.val + 1) (Nat.succ_le_of_lt j.isLt)

/-- Ordered pairs of length-`m` vectors in `Fin X` having equal sums of each
positive power through degree `k`. -/
noncomputable def vinogradovMeanValue (k m X : Nat) : Nat := by
  classical
  let pairs : Finset (Prod (Fin m -> Fin X) (Fin m -> Fin X)) :=
    (Finset.univ : Finset (Fin m -> Fin X)).product
      (Finset.univ : Finset (Fin m -> Fin X))
  exact (pairs.filter (fun fg : Prod (Fin m -> Fin X) (Fin m -> Fin X) =>
    forall j : Fin k,
      (Finset.univ.sum (fun i => (fg.1 i).val ^ (j.val + 1))) =
      (Finset.univ.sum (fun i => (fg.2 i).val ^ (j.val + 1))))).card

/-- The diagonal mean-value estimate `J(k,k;X) <= k! X^k`. Equal power sums
through degree `k` determine the finite value multiset, leaving only its
ordered rearrangements. This is Lemma 24.3(a)'s exact finite step. -/
theorem vinogradovMeanValue_le_diagonal_factorial (k X : Nat) :
    vinogradovMeanValue k k X <= X ^ k * k.factorial := by
  classical
  unfold vinogradovMeanValue
  apply Nat.le_trans (Finset.card_le_card ?_)
    (equal_multiset_pair_count_le_factorial k X)
  intro fg hfg
  rw [Finset.mem_filter] at hfg
  rw [Finset.mem_filter]
  constructor
  next => exact hfg.1
  next =>
    apply (Multiset.map_eq_map (f := fun x : Fin X => x.val)
      Fin.val_injective).mp
    rw [Multiset.map_map, Multiset.map_map]
    apply nat_multiset_eq_of_power_sums k
      (fun i => (fg.1 i).val) (fun i => (fg.2 i).val)
    intro j
    exact hfg.2 j

/-- The unconditioned cardinality of the two vector families bounds the
Vinogradov mean-value solution count. -/
theorem vinogradovMeanValue_le_trivial (k m X : Nat) :
    vinogradovMeanValue k m X <= X ^ (2 * m) := by
  classical
  unfold vinogradovMeanValue
  calc
    _ <= Fintype.card (Prod (Fin m -> Fin X) (Fin m -> Fin X)) :=
      Finset.card_le_univ _
    _ = (Fintype.card (Fin m -> Fin X)) ^ 2 := by
      rw [Fintype.card_prod, Nat.pow_two]
    _ = X ^ (2 * m) := by
      rw [Fintype.card_fun, Fintype.card_fin, <- Nat.pow_mul]
      simp only [Fintype.card_fin]
      rw [Nat.mul_comm]

/-- The diagonal pairs already supply X^m power-sum solutions. This is the
finite diagonal contribution in the Vinogradov mean-value count. -/
theorem pow_le_vinogradovMeanValue (k m X : Nat) :
    X ^ m <= vinogradovMeanValue k m X := by
  classical
  let pairs : Finset (Prod (Fin m -> Fin X) (Fin m -> Fin X)) :=
    (Finset.univ : Finset (Fin m -> Fin X)).product
      (Finset.univ : Finset (Fin m -> Fin X))
  let P : Prod (Fin m -> Fin X) (Fin m -> Fin X) -> Prop := fun fg =>
    forall j : Fin k,
      (Finset.univ.sum (fun i => (fg.1 i).val ^ (j.val + 1))) =
      (Finset.univ.sum (fun i => (fg.2 i).val ^ (j.val + 1)))
  let e : (Fin m -> Fin X) -> Prod (Fin m -> Fin X) (Fin m -> Fin X) :=
    fun f => (f, f)
  have he : Function.Injective e := by
    intro f g h
    exact congrArg Prod.fst h
  let emb : Function.Embedding (Fin m -> Fin X)
      (Prod (Fin m -> Fin X) (Fin m -> Fin X)) :=
    { toFun := e
      inj' := he }
  let D : Finset (Prod (Fin m -> Fin X) (Fin m -> Fin X)) :=
    (Finset.univ : Finset (Fin m -> Fin X)).map emb
  have hsub : D <= pairs.filter P := by
    intro fg hfg
    choose f hf hfe using Finset.mem_map.mp hfg
    subst fg
    rw [Finset.mem_filter]
    constructor
    next =>
      dsimp only [pairs, emb, e]
      exact Finset.mem_product.mpr
        (And.intro (Finset.mem_univ _) (Finset.mem_univ _))
    next =>
      dsimp only [P, emb, e]
      intro j
      rfl
  have hDcard : D.card = Fintype.card (Fin m -> Fin X) := by
    simp only [D, Finset.card_map, Finset.card_univ]
  change X ^ m <= (pairs.filter P).card
  calc
    X ^ m = Fintype.card (Fin m -> Fin X) := by
      rw [Fintype.card_fun, Fintype.card_fin]
      simp only [Fintype.card_fin]
    _ = D.card := hDcard.symm
    _ <= (pairs.filter P).card := Finset.card_le_card hsub
/-- The form of the trivial bound used when the moment length is `k*r`. -/
theorem vinogradovMeanValue_le_trivial_kr (k r X : Nat) :
    vinogradovMeanValue k (k * r) X <= X ^ (2 * k * r) := by
  simpa only [Nat.mul_assoc] using vinogradovMeanValue_le_trivial k (k * r) X

/-- A positive affine embedding sends every vector solution of the VMVT
system into the corresponding enlarged interval. This is the finite-count
transport used in the congruence-class restriction of Lemma 24.1(d). -/
theorem vinogradovMeanValue_le_affine (k m q r X : Nat) (hq : 0 < q) :
    vinogradovMeanValue k m X <= vinogradovMeanValue k m (q * X + r + 1) := by
  classical
  unfold vinogradovMeanValue
  let source : Finset (Prod (Fin m -> Fin X) (Fin m -> Fin X)) :=
    (Finset.univ : Finset (Fin m -> Fin X)).product
      (Finset.univ : Finset (Fin m -> Fin X))
  let target : Finset
      (Prod (Fin m -> Fin (q * X + r + 1)) (Fin m -> Fin (q * X + r + 1))) :=
    (Finset.univ : Finset (Fin m -> Fin (q * X + r + 1))).product
      (Finset.univ : Finset (Fin m -> Fin (q * X + r + 1)))
  let P : Prod (Fin m -> Fin X) (Fin m -> Fin X) -> Prop := fun fg =>
    forall j : Fin k,
      Finset.univ.sum (fun i => (fg.1 i).val ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (fg.2 i).val ^ (j.val + 1))
  let Q : Prod (Fin m -> Fin (q * X + r + 1))
      (Fin m -> Fin (q * X + r + 1)) -> Prop := fun fg =>
    forall j : Fin k,
      Finset.univ.sum (fun i => (fg.1 i).val ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (fg.2 i).val ^ (j.val + 1))
  let e : Function.Embedding (Prod (Fin m -> Fin X) (Fin m -> Fin X))
      (Prod (Fin m -> Fin (q * X + r + 1))
        (Fin m -> Fin (q * X + r + 1))) :=
    { toFun := affineFinPair m q r X
      inj' := affineFinPair_injective m q r X hq }
  have hsub : (source.filter P).map e <= target.filter Q := by
    intro fg hfg
    cases Finset.mem_map.mp hfg with
    | intro x hx =>
      have hxeq : e x = fg := hx.2
      subst fg
      apply Finset.mem_filter.mpr
      constructor
      next =>
        dsimp only [target]
        exact Finset.mem_product.mpr
          (And.intro (Finset.mem_univ _) (Finset.mem_univ _))
      next =>
        have hp : P x := (Finset.mem_filter.mp hx.1).2
        change forall j : Fin k,
          Finset.univ.sum (fun i =>
            (affineFin q r X (x.1 i)).val ^ (j.val + 1)) =
          Finset.univ.sum (fun i =>
            (affineFin q r X (x.2 i)).val ^ (j.val + 1))
        intro j
        simpa only [affineFin, Fin.mk_val] using
          affine_nat_power_sums_eq_of_power_sums_general m k q r
            (fun i => (x.1 i).val) (fun i => (x.2 i).val) hp j
  have hcard : (source.filter P).card <= (target.filter Q).card := by
    calc
      (source.filter P).card = ((source.filter P).map e).card :=
        (Finset.card_map _).symm
      _ <= (target.filter Q).card := Finset.card_le_card hsub
  simpa only [source, target, P, Q] using hcard

/-- A positive affine map preserves and reflects the equal-power-sum
predicate for an arbitrary pair of VMVT vectors. -/
theorem affineFinPair_power_sums_iff (k m q r X : Nat) (hq : 0 < q)
    (fg : Prod (Fin m -> Fin X) (Fin m -> Fin X)) :
    (forall j : Fin k,
      Finset.univ.sum (fun i => (fg.1 i).val ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (fg.2 i).val ^ (j.val + 1))) <->
    (forall j : Fin k,
      Finset.univ.sum (fun i =>
        ((affineFinPair m q r X fg).1 i).val ^ (j.val + 1)) =
        Finset.univ.sum (fun i =>
          ((affineFinPair m q r X fg).2 i).val ^ (j.val + 1))) := by
  constructor
  next =>
    intro h
    simpa only [affineFinPair, affineFinVector, affineFin, Fin.mk_val] using
      affine_nat_power_sums_eq_of_power_sums_general m k q r
        (fun i => (fg.1 i).val) (fun i => (fg.2 i).val) h
  next =>
    intro h
    have h' : forall j : Fin k,
        Finset.univ.sum (fun i => (q * (fg.1 i).val + r) ^ (j.val + 1)) =
          Finset.univ.sum (fun i =>
            (q * (fg.2 i).val + r) ^ (j.val + 1)) := by
      simpa only [affineFinPair, affineFinVector, affineFin, Fin.mk_val] using h
    exact power_sums_eq_of_affine_nat_power_sums_eq_general m k q r hq
      (fun i => (fg.1 i).val) (fun i => (fg.2 i).val) h'

/-- The injective affine map on vector pairs, packaged for finite-set maps. -/
noncomputable def affineFinPairEmbedding (m q r X : Nat) (hq : 0 < q) :
    Function.Embedding (Prod (Fin m -> Fin X) (Fin m -> Fin X))
      (Prod (Fin m -> Fin (q * X + r + 1))
        (Fin m -> Fin (q * X + r + 1))) :=
  { toFun := affineFinPair m q r X
    inj' := affineFinPair_injective m q r X hq }

/-- The exact finite-set affine transport of the VMVT equal-power-sum count.
This is the filtered-cardinality form needed for restricted interval and
residue-class packets in Lemma 24.1(d). -/
theorem card_filter_affineFinPair_eq (k m q r X : Nat) (hq : 0 < q)
    (s : Finset (Prod (Fin m -> Fin X) (Fin m -> Fin X))) :
    (s.filter (fun fg => forall j : Fin k,
      Finset.univ.sum (fun i => (fg.1 i).val ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (fg.2 i).val ^ (j.val + 1)))).card =
      ((s.map (affineFinPairEmbedding m q r X hq)).filter (fun fg =>
        forall j : Fin k,
          Finset.univ.sum (fun i => (fg.1 i).val ^ (j.val + 1)) =
            Finset.univ.sum (fun i => (fg.2 i).val ^ (j.val + 1)))).card := by
  classical
  let P : Prod (Fin m -> Fin X) (Fin m -> Fin X) -> Prop := fun fg =>
    forall j : Fin k,
      Finset.univ.sum (fun i => (fg.1 i).val ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (fg.2 i).val ^ (j.val + 1))
  let Q : Prod (Fin m -> Fin (q * X + r + 1))
      (Fin m -> Fin (q * X + r + 1)) -> Prop := fun fg =>
    forall j : Fin k,
      Finset.univ.sum (fun i => (fg.1 i).val ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (fg.2 i).val ^ (j.val + 1))
  let e := affineFinPairEmbedding m q r X hq
  have heq : (s.filter P).map e = (s.map e).filter Q := by
    ext y
    constructor
    next =>
      intro hy
      cases Finset.mem_map.mp hy with
      | intro x hx =>
        have hxs := (Finset.mem_filter.mp hx.1).1
        have hp : P x := (Finset.mem_filter.mp hx.1).2
        have hxy := hx.2
        subst y
        apply Finset.mem_filter.mpr
        constructor
        next =>
          apply Finset.mem_map.mpr
          exact Exists.intro x (And.intro hxs rfl)
        next =>
          exact (affineFinPair_power_sums_iff k m q r X hq x).mp hp
    next =>
      intro hy
      have hqcond : Q y := (Finset.mem_filter.mp hy).2
      cases Finset.mem_map.mp (Finset.mem_filter.mp hy).1 with
      | intro x hx =>
        have hxs := hx.1
        have hxy := hx.2
        subst y
        apply Finset.mem_map.mpr
        refine Exists.intro x ?_
        constructor
        next =>
          apply Finset.mem_filter.mpr
          constructor
          next => exact hxs
          next =>
            exact (affineFinPair_power_sums_iff k m q r X hq x).mpr hqcond
        next => rfl
  have hcard : (s.filter P).card = ((s.map e).filter Q).card := by
    calc
      (s.filter P).card = ((s.filter P).map e).card := (Finset.card_map _).symm
      _ = ((s.map e).filter Q).card := congrArg Finset.card heq
  simpa only [P, Q, e] using hcard

/-- Enlarging the interval cannot decrease the Vinogradov mean value. -/
theorem vinogradovMeanValue_mono
    (k m X Y : Nat) (hXY : X <= Y) :
    vinogradovMeanValue k m X <= vinogradovMeanValue k m Y := by
  by_cases heq : X = Y
  next => simpa [heq]
  next =>
    have hlt : X < Y := lt_of_le_of_ne hXY heq
    have h := vinogradovMeanValue_le_affine
      k m 1 (Y - X - 1) X (by decide)
    have hY : 1 * X + (Y - X - 1) + 1 = Y := by omega
    rw [hY] at h
    exact h

end Finset
