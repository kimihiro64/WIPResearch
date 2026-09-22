/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import RobinBV.Mathlib.NumberTheory.VinogradovMeanValue

/-!
# Local factor selection for Linnik's lemma
This module proves the modular factor-selection step used by Linnik's lemma.
-/

set_option autoImplicit false

namespace ZMod

/-- A zero multiset product modulo a positive prime power has a factor
that vanishes after reduction modulo the prime. -/
theorem multiset_product_eq_zero_selects_mod_prime (p u : Nat) (hp : p.Prime)
    (hu : 0 < u) (m : Multiset (ZMod (p ^ u))) (hprod : m.prod = 0) :
    Exists (fun x => And (Membership.mem m x)
      (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p) x = 0)) := by
  letI : Fact p.Prime := Fact.mk hp
  let phi : RingHom (ZMod (p ^ u)) (ZMod p) :=
    ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p)
  have hmap : (m.map phi).prod = 0 := by
    rw [<- map_multiset_prod]
    simp only [hprod, map_zero]
  rw [Multiset.prod_eq_zero_iff] at hmap
  cases Multiset.mem_map.mp hmap with
  | intro x hx =>
    exact Exists.intro x (And.intro hx.1 hx.2)

/-- A factor whose reduction modulo p is nonzero is a unit modulo p to the
power u. -/
theorem isUnit_of_reduction_ne_zero (p u : Nat) (hp : p.Prime)
    (hu : 0 < u) (x : ZMod (p ^ u))
    (h : Not (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p) x = 0)) :
    IsUnit x := by
  letI : NeZero (p ^ u) := NeZero.mk (Nat.ne_of_gt (Nat.pow_pos hp.pos))
  rw [<- ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp hu]
  intro hdiv
  apply h
  have hx : (x.val : ZMod p) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p x.val).mpr hdiv
  rw [ZMod.castHom_apply]
  rw [<- ZMod.natCast_val x]
  exact hx

/-- Cancelling a unit product of all factors except a selected one forces that
selected factor to vanish when the full product vanishes. -/
theorem eq_zero_of_multiset_prod_eq_zero_of_erase_isUnit (p u : Nat)
    (m : Multiset (ZMod (p ^ u))) (a : ZMod (p ^ u))
    (ha : Membership.mem m a) (hunit : IsUnit (m.erase a).prod)
    (hprod : m.prod = 0) : a = 0 := by
  have hmul : a * (m.erase a).prod = 0 := by
    rw [Multiset.prod_erase ha]
    exact hprod
  exact hunit.mul_left_eq_zero.mp hmul

/-- A multiset product is a unit when every multiset member is a unit. -/
theorem multiset_prod_isUnit {R : Type*} [CommMonoid R]
    (m : Multiset R) (h : forall x : R, Membership.mem m x -> IsUnit x) :
    IsUnit m.prod := by
  revert h
  refine Multiset.induction_on m (by intro h; simpa using isUnit_one) ?_
  intro a m ih h
  rw [Multiset.prod_cons]
  apply IsUnit.mul
  exact h a (by simp)
  apply ih
  intro x hx
  exact h x (by simp [hx])

/-- If every factor except a selected one stays nonzero after reduction modulo
p, the erased product is a unit modulo p to the power u. -/
theorem erase_prod_isUnit_of_reduction_ne_zero (p u : Nat)
    (hp : p.Prime) (hu : 0 < u) (m : Multiset (ZMod (p ^ u)))
    (a : ZMod (p ^ u))
    (h : forall x : ZMod (p ^ u), Membership.mem (m.erase a) x ->
      Not (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p) x = 0)) :
    IsUnit (m.erase a).prod := by
  apply multiset_prod_isUnit
  intro x hx
  exact isUnit_of_reduction_ne_zero p u hp hu x (h x hx)

/-- A selected factor in a zero product vanishes when every remaining factor
stays nonzero after reduction modulo the underlying prime. -/
theorem selected_factor_eq_zero_of_product_eq_zero (p u : Nat)
    (hp : p.Prime) (hu : 0 < u) (m : Multiset (ZMod (p ^ u)))
    (a : ZMod (p ^ u)) (ha : Membership.mem m a)
    (hall : forall x : ZMod (p ^ u), Membership.mem (m.erase a) x ->
      Not (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p) x = 0))
    (hprod : m.prod = 0) : a = 0 := by
  apply eq_zero_of_multiset_prod_eq_zero_of_erase_isUnit p u m a ha
  apply erase_prod_isUnit_of_reduction_ne_zero p u hp hu m a hall
  exact hprod

/-- Equal power sums modulo a prime power identify each coordinate of the
second tuple with a coordinate of the first tuple when the first reductions
are pairwise distinct modulo the underlying prime. This is Linnik's local
root-lifting step. -/
theorem exists_eq_of_power_sums_of_reduction_injective (p u q : Nat)
    (hp : p.Prime) (hu : 0 < u) (hqp : q < p)
    (f g : Fin q -> ZMod (p ^ u))
    (hinj : Function.Injective (fun t : Fin q =>
      ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p) (f t)))
    (hpsum : forall i : Nat, i <= q ->
      MvPolynomial.aeval f (MvPolynomial.psum (Fin q) (ZMod (p ^ u)) i) =
        MvPolynomial.aeval g (MvPolynomial.psum (Fin q) (ZMod (p ^ u)) i))
    (s : Fin q) : Exists (fun t : Fin q => g s = f t) := by
  let m : Multiset (ZMod (p ^ u)) :=
    (Finset.univ.val.map f).map (fun t => g s - t)
  let phi : RingHom (ZMod (p ^ u)) (ZMod p) :=
    ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p)
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    exact congrArg (fun z : ZMod (p ^ u) =>
      ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p) z) hij
  have hdiff : Function.Injective (fun x : ZMod (p ^ u) => g s - x) := by
    intro x y hxy
    exact sub_right_inj.mp hxy
  have hnodup : m.Nodup := by
    dsimp only [m]
    apply Multiset.Nodup.map hdiff
    apply Multiset.Nodup.map hf
    exact Finset.nodup _
  have hprod : m.prod = 0 := by
    dsimp only [m]
    exact MvPolynomial.zmod_root_product_eq_zero_of_power_sums
      p u q hp hu hqp f g hpsum s
  have hselect := multiset_product_eq_zero_selects_mod_prime p u hp hu m hprod
  choose a ha using hselect
  dsimp only [m] at ha
  choose y hy using Multiset.mem_map.mp ha.1
  choose t ht using Multiset.mem_map.mp hy.1
  have hta : g s - f t = a := by
    rw [ht.2]
    exact hy.2
  subst a
  refine Exists.intro t ?_
  have hmem : Membership.mem m (g s - f t) := by
    dsimp only [m]
    apply Multiset.mem_map.mpr
    exact Exists.intro (f t) (And.intro (Multiset.mem_map.mpr
      (Exists.intro t (And.intro (Finset.mem_univ t) rfl))) rfl)
  have hall : forall x : ZMod (p ^ u), Membership.mem (m.erase (g s - f t)) x ->
      Not (phi x = 0) := by
    intro x hx hzero
    have hxmem : Membership.mem m x := Multiset.mem_of_mem_erase hx
    dsimp only [m] at hxmem
    choose y hy using Multiset.mem_map.mp hxmem
    choose i hi using Multiset.mem_map.mp hy.1
    have hix : g s - f i = x := by
      rw [hi.2]
      exact hy.2
    subst x
    have hgi : phi (g s) = phi (f i) := by
      exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)
    have hgt : phi (g s) = phi (f t) := by
      exact sub_eq_zero.mp (by simpa only [phi, map_sub] using ha.2)
    have hfit : phi (f i) = phi (f t) := hgi.symm.trans hgt
    have hit : i = t := hinj hfit
    subst i
    exact hnodup.notMem_erase hx
  exact sub_eq_zero.mp
    (selected_factor_eq_zero_of_product_eq_zero p u hp hu m (g s - f t)
      hmem (by simpa only [phi] using hall) hprod)

/-- The local root lift identifies the two finite value multisets when both
tuples have pairwise distinct reductions modulo the underlying prime. -/
theorem multiset_eq_of_power_sums_of_reduction_injective (p u q : Nat)
    (hp : p.Prime) (hu : 0 < u) (hqp : q < p)
    (f g : Fin q -> ZMod (p ^ u))
    (hinjf : Function.Injective (fun t : Fin q =>
      ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p) (f t)))
    (hinjg : Function.Injective (fun t : Fin q =>
      ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p) (g t)))
    (hpsum : forall i : Nat, i <= q ->
      MvPolynomial.aeval f (MvPolynomial.psum (Fin q) (ZMod (p ^ u)) i) =
        MvPolynomial.aeval g (MvPolynomial.psum (Fin q) (ZMod (p ^ u)) i)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  have hg : Function.Injective g := by
    intro i j hij
    apply hinjg
    exact congrArg (fun z : ZMod (p ^ u) =>
      ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p) z) hij
  have hnodup : (Finset.univ.val.map g).Nodup := by
    apply Multiset.Nodup.map hg
    exact Finset.nodup _
  symm
  apply Multiset.eq_of_le_of_card_le
  apply (Multiset.le_iff_subset hnodup).mpr
  intro x hx
  choose s hs using Multiset.mem_map.mp hx
  choose t ht using exists_eq_of_power_sums_of_reduction_injective
    p u q hp hu hqp f g hinjf hpsum s
  have hxf : x = f t := hs.2.symm.trans ht
  subst x
  apply Multiset.mem_map.mpr
  exact Exists.intro t (And.intro (Finset.mem_univ t) rfl)
  simp only [Multiset.card_map]
  exact Nat.le_refl _

end ZMod

namespace Finset

/-- Independent quotient coordinates for lower-modulus right-hand sides in
Linnik's local congruence count. -/
def linnikLowerModulusChoices (p k : Nat) : Type :=
  forall j : Fin k, Fin (p ^ (k - (j.val + 1)))

instance (p k : Nat) : Fintype (linnikLowerModulusChoices p k) := by
  unfold linnikLowerModulusChoices
  infer_instance

/-- The exact product cardinality of the lower-modulus quotient choices. -/
theorem card_linnikLowerModulusChoices (p k : Nat) :
    Fintype.card (linnikLowerModulusChoices p k) =
      Finset.univ.prod (fun j : Fin k => p ^ (k - (j.val + 1))) := by
  simp only [linnikLowerModulusChoices, Fintype.card_pi, Fintype.card_fin]

/-- A quotient choice preserves the prescribed lower prime-power congruence.
This is the forward congruence half of the later representative bijection. -/
theorem lower_choice_modEq (p k : Nat) (h : Fin k -> Nat)
    (t : linnikLowerModulusChoices p k) (j : Fin k) :
    Nat.ModEq (p ^ (j.val + 1)) (h j + p ^ (j.val + 1) * (t j).val) (h j) := by
  unfold linnikLowerModulusChoices at t
  exact Nat.add_modulus_mul_modEq_iff.mpr (Nat.ModEq.refl (h j))

/-- The quotient modulus times its lower congruence modulus is the full
prime-power range modulus. -/
theorem lower_choice_modulus_product (p k : Nat) (j : Fin k) :
    p ^ (k - (j.val + 1)) * p ^ (j.val + 1) = p ^ k := by
  apply pow_sub_mul_pow
  exact Nat.succ_le_of_lt j.isLt

/-- A canonical lower-modulus representative plus a strict quotient choice
stays strictly below the full prime-power modulus. -/
theorem lower_choice_lt_full_modulus (p k : Nat) (j : Fin k) (a t : Nat)
    (hp : 0 < p) (ha : a < p ^ (j.val + 1))
    (ht : t < p ^ (k - (j.val + 1))) :
    a + p ^ (j.val + 1) * t < p ^ k := by
  have hpos : 0 < p ^ (j.val + 1) := Nat.pow_pos hp
  have hsucc : t + 1 <= p ^ (k - (j.val + 1)) := Nat.succ_le_of_lt ht
  have hmul : p ^ (j.val + 1) * (t + 1) <=
      p ^ (j.val + 1) * p ^ (k - (j.val + 1)) :=
    Nat.mul_le_mul_left _ hsucc
  have hadd : a + p ^ (j.val + 1) * t < p ^ (j.val + 1) * (t + 1) := by
    rw [Nat.mul_succ]
    rw [Nat.add_comm]
    exact Nat.add_lt_add_left ha _
  exact lt_of_lt_of_le hadd (by
    calc
      p ^ (j.val + 1) * (t + 1) <=
          p ^ (j.val + 1) * p ^ (k - (j.val + 1)) := hmul
      _ = p ^ k := by
        rw [Nat.mul_comm]
        exact lower_choice_modulus_product p k j)

/-- Division by a positive lower prime-power modulus recovers the quotient
from an exact canonical representative decomposition. -/
theorem lower_choice_div_recovers (d a t : Nat) (hd : 0 < d) :
    (a + d * t - a) / d = t := by
  rw [Nat.add_sub_cancel_left]
  rw [Nat.mul_comm]
  exact Nat.mul_div_left _ hd

/-- Every representative below `d * B` in the lower residue class of `h`
has a quotient coordinate below `B`. This is the reverse parametrization
needed for the exact Linnik local choice count. -/
theorem exists_lower_choice_quotient (d B h g : Nat)
    (hd : 0 < d) (hg : g < d * B) (hmod : g % d = h) :
    Exists (fun t : Fin B => g = h + d * t.val) := by
  have hq : g / d < B := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    simpa only [Nat.mul_comm] using hg
  refine Exists.intro (Fin.mk (g / d) hq) ?_
  rw [<- hmod]
  exact (Nat.mod_add_div g d).symm

/-- The canonical full-modulus representative determined by one lower
prime-power quotient choice. -/
def linnikLowerChoiceRepresentative (p k : Nat) (h : Fin k -> Nat)
    (hp : 0 < p) (t : linnikLowerModulusChoices p k) : Fin k -> Fin (p ^ k) :=
  fun j => Fin.mk (h j % p ^ (j.val + 1) +
      p ^ (j.val + 1) * (t j).val)
    (lower_choice_lt_full_modulus p k j _ _ hp
      (Nat.mod_lt _ (Nat.pow_pos hp)) (t j).isLt)

/-- Each constructed representative lies in its required lower congruence
class. -/
theorem linnikLowerChoiceRepresentative_modEq (p k : Nat) (h : Fin k -> Nat)
    (hp : 0 < p) (t : linnikLowerModulusChoices p k) (j : Fin k) :
    Nat.ModEq (p ^ (j.val + 1))
      ((linnikLowerChoiceRepresentative p k h hp t) j).val (h j) := by
  change Nat.ModEq (p ^ (j.val + 1))
    (h j % p ^ (j.val + 1) + p ^ (j.val + 1) * (t j).val) (h j)
  exact (lower_choice_modEq p k
    (fun i => h i % p ^ (i.val + 1)) t j).trans (Nat.mod_modEq _ _)

/-- Distinct lower quotient choices give distinct full representative
vectors. This is the injective half of the exact local counting bijection. -/
theorem linnikLowerChoiceRepresentative_injective (p k : Nat)
    (h : Fin k -> Nat) (hp : 0 < p) :
    Function.Injective (linnikLowerChoiceRepresentative p k h hp) := by
  intro t u htu
  funext j
  apply Fin.ext
  have hval := congrArg Fin.val (congrFun htu j)
  change h j % p ^ (j.val + 1) + p ^ (j.val + 1) * (t j).val =
    h j % p ^ (j.val + 1) + p ^ (j.val + 1) * (u j).val at hval
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hp)
  exact Nat.add_left_cancel hval

/-- Every compatible full-modulus representative is produced by a lower
quotient choice. This is the surjective half of the exact local counting
bijection, with the full range endpoint retained explicitly. -/
theorem exists_linnikLowerChoiceRepresentative_eq (p k : Nat)
    (h : Fin k -> Nat) (hp : 0 < p) (g : Fin k -> Fin (p ^ k))
    (hmod : forall j : Fin k, Nat.ModEq (p ^ (j.val + 1)) (g j).val (h j)) :
    Exists (fun t : linnikLowerModulusChoices p k =>
      linnikLowerChoiceRepresentative p k h hp t = g) := by
  have hrep : forall j : Fin k, Exists (fun t : Fin (p ^ (k - (j.val + 1))) =>
      (g j).val = h j % p ^ (j.val + 1) + p ^ (j.val + 1) * t.val) := by
    intro j
    apply exists_lower_choice_quotient (p ^ (j.val + 1))
      (p ^ (k - (j.val + 1))) (h j % p ^ (j.val + 1)) (g j).val
    exact Nat.pow_pos hp
    calc
      (g j).val < p ^ k := (g j).isLt
      _ = p ^ (k - (j.val + 1)) * p ^ (j.val + 1) :=
        (lower_choice_modulus_product p k j).symm
      _ = p ^ (j.val + 1) * p ^ (k - (j.val + 1)) := Nat.mul_comm _ _
    exact hmod j
  choose t ht using hrep
  refine Exists.intro t ?_
  funext j
  apply Fin.ext
  exact (ht j).symm

/-- Full-modulus representatives satisfying every prescribed lower
prime-power congruence in Linnik's local count. -/
def linnikCompatibleRepresentatives (p k : Nat) (h : Fin k -> Nat) : Type :=
  {g : Fin k -> Fin (p ^ k) //
    forall j : Fin k, Nat.ModEq (p ^ (j.val + 1)) (g j).val (h j)}

/-- The vector of exact power sums reduced to the full modulus p to the k. -/
def linnikPowerSumRepresentative (p k : Nat) (hp : 0 < p)
    (m : Fin k -> Fin (p ^ k)) : Fin k -> Fin (p ^ k) :=
  fun j => Fin.mk
    ((Finset.univ.sum fun r : Fin k => (m r).val ^ (j.val + 1)) % p ^ k)
    (Nat.mod_lt _ (Nat.pow_pos hp))

/-- Lower-modulus power-sum congruences force the full-modulus representative
vector to lie in the compatible right-hand-side space. -/
theorem linnikPowerSumRepresentative_mem_compatible (p k : Nat)
    (h : Fin k -> Nat) (hp : 0 < p) (m : Fin k -> Fin (p ^ k))
    (hmod : forall j : Fin k,
      Nat.ModEq (p ^ (j.val + 1))
        (Finset.univ.sum fun r : Fin k => (m r).val ^ (j.val + 1)) (h j)) :
    forall j : Fin k, Nat.ModEq (p ^ (j.val + 1))
      ((linnikPowerSumRepresentative p k hp m) j).val (h j) := by
  intro j
  have hdvd : Dvd.dvd (p ^ (j.val + 1)) (p ^ k) := by
    refine Dvd.intro (p ^ (k - (j.val + 1))) ?_
    rw [Nat.mul_comm]
    exact lower_choice_modulus_product p k j
  exact ((Nat.mod_modEq
    (Finset.univ.sum fun r : Fin k => (m r).val ^ (j.val + 1)) (p ^ k)).of_dvd
      hdvd).trans (hmod j)

/-- The actual local A(p,h) solution space: full-modulus tuples with distinct
reductions modulo p and the prescribed lower power-sum congruences. -/
def linnikCongruenceSolutions (p k : Nat) (h : Fin k -> Nat) : Type :=
  {m : Fin k -> Fin (p ^ k) //
    Function.Injective (fun r : Fin k => (m r).val % p) /\
    forall j : Fin k, Nat.ModEq (p ^ (j.val + 1))
      (Finset.univ.sum fun r : Fin k => (m r).val ^ (j.val + 1)) (h j)}

/-- The A(p,h) solution space is finite. -/
noncomputable instance linnikCongruenceSolutionsFintype
    (p k : Nat) (h : Fin k -> Nat) :
    Fintype (linnikCongruenceSolutions p k h) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Every A(p,h) solution determines its canonical compatible full-modulus
right-hand-side representative. -/
def linnikSolutionCompatibleRepresentative (p k : Nat) (h : Fin k -> Nat)
    (hp : 0 < p) :
    linnikCongruenceSolutions p k h -> linnikCompatibleRepresentatives p k h :=
  fun m => Subtype.mk (linnikPowerSumRepresentative p k hp m.val)
    (linnikPowerSumRepresentative_mem_compatible p k h hp m.val m.property.2)

/-- The solutions in A(p,h) with one fixed full-modulus power-sum
representative. -/
def linnikSolutionFiber (p k : Nat) (h : Fin k -> Nat) (hp : 0 < p)
    (g : linnikCompatibleRepresentatives p k h) : Type :=
  {m : linnikCongruenceSolutions p k h //
    linnikSolutionCompatibleRepresentative p k h hp m = g}

/-- Every fixed-representative solution fiber is finite. -/
noncomputable instance linnikSolutionFiberFintype
    (p k : Nat) (h : Fin k -> Nat) (hp : 0 < p)
    (g : linnikCompatibleRepresentatives p k h) :
    Fintype (linnikSolutionFiber p k h hp g) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Equal canonical representatives give equal power sums modulo the full
modulus, including the zeroth power sum. -/
theorem powerSum_modEq_of_linnikPowerSumRepresentative_eq
    (p k : Nat) (hp : 0 < p) (m n : Fin k -> Fin (p ^ k))
    (hrep : linnikPowerSumRepresentative p k hp m =
      linnikPowerSumRepresentative p k hp n)
    (i : Nat) (hi : i <= k) :
    Nat.ModEq (p ^ k)
      (Finset.univ.sum fun r : Fin k => (m r).val ^ i)
      (Finset.univ.sum fun r : Fin k => (n r).val ^ i) := by
  cases i with
  | zero =>
    exact Nat.ModEq.refl _
  | succ i =>
    have hik : i < k := Nat.lt_of_succ_le hi
    let j : Fin k := Fin.mk i hik
    have hval := congrArg (fun v : Fin k -> Fin (p ^ k) => (v j).val) hrep
    change
      (Finset.univ.sum fun r : Fin k => (m r).val ^ (i + 1)) % p ^ k =
        (Finset.univ.sum fun r : Fin k => (n r).val ^ (i + 1)) % p ^ k at hval
    exact hval

/-- Equal canonical representatives give equal polynomial power sums in the
full residue ring. -/
theorem zmod_powerSums_eq_of_linnikPowerSumRepresentative_eq
    (p k : Nat) (hp : 0 < p) (m n : Fin k -> Fin (p ^ k))
    (hrep : linnikPowerSumRepresentative p k hp m =
      linnikPowerSumRepresentative p k hp n)
    (i : Nat) (hi : i <= k) :
    MvPolynomial.aeval (fun r : Fin k => ((m r).val : ZMod (p ^ k)))
        (MvPolynomial.psum (Fin k) (ZMod (p ^ k)) i) =
      MvPolynomial.aeval (fun r : Fin k => ((n r).val : ZMod (p ^ k)))
        (MvPolynomial.psum (Fin k) (ZMod (p ^ k)) i) := by
  rw [MvPolynomial.aeval_psum_eq_finset_sum]
  rw [MvPolynomial.aeval_psum_eq_finset_sum]
  calc
    Finset.univ.sum (fun r : Fin k => (((m r).val : ZMod (p ^ k)) ^ i)) =
        ((Finset.univ.sum fun r : Fin k => (m r).val ^ i : Nat) :
          ZMod (p ^ k)) := by simp
    _ = ((Finset.univ.sum fun r : Fin k => (n r).val ^ i : Nat) :
          ZMod (p ^ k)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2
        (powerSum_modEq_of_linnikPowerSumRepresentative_eq
          p k hp m n hrep i hi)
    _ = Finset.univ.sum
        (fun r : Fin k => (((n r).val : ZMod (p ^ k)) ^ i)) := by simp

/-- Two solutions in one fixed representative fiber have the same value
multiset in the full residue ring. -/
theorem zmod_multiset_eq_of_linnikSolutionFiber
    (p k : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (h : Fin k -> Nat) (g : linnikCompatibleRepresentatives p k h)
    (a b : linnikSolutionFiber p k h hp.pos g) :
    Finset.univ.val.map
        (fun r : Fin k => ((a.val.val r).val : ZMod (p ^ k))) =
      Finset.univ.val.map
        (fun r : Fin k => ((b.val.val r).val : ZMod (p ^ k))) := by
  letI : NeZero (p ^ k) := NeZero.mk (Nat.ne_of_gt (Nat.pow_pos hp.pos))
  have hrep : linnikPowerSumRepresentative p k hp.pos a.val.val =
      linnikPowerSumRepresentative p k hp.pos b.val.val := by
    exact congrArg Subtype.val (a.property.trans b.property.symm)
  have hinja : Function.Injective (fun r : Fin k =>
      ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p)
        ((a.val.val r).val : ZMod (p ^ k))) := by
    intro r s hrs
    apply a.val.property.1
    have hval := congrArg ZMod.val hrs
    simpa only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
      Nat.mod_mod_of_dvd _ (dvd_pow_self p (Nat.ne_of_gt hk))] using hval
  have hinjb : Function.Injective (fun r : Fin k =>
      ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p)
        ((b.val.val r).val : ZMod (p ^ k))) := by
    intro r s hrs
    apply b.val.property.1
    have hval := congrArg ZMod.val hrs
    simpa only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast,
      Nat.mod_mod_of_dvd _ (dvd_pow_self p (Nat.ne_of_gt hk))] using hval
  apply ZMod.multiset_eq_of_power_sums_of_reduction_injective
    p k k hp hk hkp _ _ hinja hinjb
  intro i hi
  exact zmod_powerSums_eq_of_linnikPowerSumRepresentative_eq
    p k hp.pos a.val.val b.val.val hrep i hi

/-- Compatible representatives form a finite subtype of the finite full
representative function space. -/
noncomputable instance linnikCompatibleRepresentativesFintype
    (p k : Nat) (h : Fin k -> Nat) :
    Fintype (linnikCompatibleRepresentatives p k h) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The compatible representative space has exactly the product of its
independent quotient-coordinate cardinalities. -/
theorem card_linnikCompatibleRepresentatives (p k : Nat) (h : Fin k -> Nat)
    (hp : 0 < p) :
    Fintype.card (linnikCompatibleRepresentatives p k h) =
      Finset.univ.prod (fun j : Fin k => p ^ (k - (j.val + 1))) := by
  classical
  let f : linnikLowerModulusChoices p k ->
      linnikCompatibleRepresentatives p k h := fun t =>
    Subtype.mk (linnikLowerChoiceRepresentative p k h hp t)
      (fun j => linnikLowerChoiceRepresentative_modEq p k h hp t j)
  have hinj : Function.Injective f := by
    intro t u htu
    apply linnikLowerChoiceRepresentative_injective p k h hp
    exact congrArg Subtype.val htu
  have hsurj : Function.Surjective f := by
    intro g
    obtain h := exists_linnikLowerChoiceRepresentative_eq p k h hp g.val g.property
    choose t ht using h
    exact Exists.intro t (Subtype.ext ht)
  let e : Equiv (linnikLowerModulusChoices p k) (linnikCompatibleRepresentatives p k h) :=
    Equiv.ofBijective f (And.intro hinj hsurj)
  calc
    Fintype.card (linnikCompatibleRepresentatives p k h) =
        Fintype.card (linnikLowerModulusChoices p k) := Fintype.card_congr e.symm
    _ = Finset.univ.prod (fun j : Fin k => p ^ (k - (j.val + 1))) :=
      card_linnikLowerModulusChoices p k

/-- For a fixed length-`q` tuple, at most `q!` ordered tuples have the same
finite value multiset. This is the factorial fiber bound consumed after the
local root-lift step in Linnik's lemma. -/
theorem multiset_fiber_card_le_factorial {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha]
    (q : Nat) (f : Fin q -> alpha) :
    Fintype.card {g : Fin q -> alpha //
      Finset.univ.val.map g = Finset.univ.val.map f} <= q.factorial := by
  classical
  let S := {g : Fin q -> alpha //
    Finset.univ.val.map g = Finset.univ.val.map f}
  have hperm : forall z : S, (List.ofFn z.val).Perm (List.ofFn f) := by
    intro z
    apply Multiset.coe_eq_coe.mp
    simpa only [Fin.univ_val_map] using z.property
  let rawIndex : forall z : S, Fin ((List.ofFn f).permutations.length) := fun z =>
    Classical.choose (List.mem_iff_get.mp (List.mem_permutations.mpr (hperm z)))
  have rawIndex_spec : forall z : S,
      (List.ofFn f).permutations.get (rawIndex z) = List.ofFn z.val := by
    intro z
    exact Classical.choose_spec (List.mem_iff_get.mp
      (List.mem_permutations.mpr (hperm z)))
  let index : forall z : S, Fin q.factorial := fun z =>
    Fin.cast (by
      rw [List.length_permutations]
      simp) (rawIndex z)
  have hindex : Function.Injective index := by
    intro a b hab
    have hraw : rawIndex a = rawIndex b := by
      apply Fin.ext
      change (rawIndex a).val = (rawIndex b).val
      have hval : (index a).val = (index b).val :=
        congrArg (fun z : Fin q.factorial => z.val) hab
      exact hval
    apply Subtype.ext
    apply List.ofFn_injective
    calc
      List.ofFn a.val = (List.ofFn f).permutations.get (rawIndex a) :=
        (rawIndex_spec a).symm
      _ = (List.ofFn f).permutations.get (rawIndex b) := by rw [hraw]
      _ = List.ofFn b.val := rawIndex_spec b
  calc
    _ = Fintype.card S := rfl
    _ <= Fintype.card (Fin q.factorial) := Fintype.card_le_of_injective index hindex
    _ = q.factorial := Fintype.card_fin q.factorial

/-- Every fixed full-modulus representative fiber in A(p,h) has at most k
factorial solutions. -/
theorem card_linnikSolutionFiber_le_factorial
    (p k : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (h : Fin k -> Nat) (g : linnikCompatibleRepresentatives p k h) :
    Fintype.card (linnikSolutionFiber p k h hp.pos g) <= k.factorial := by
  classical
  letI : NeZero (p ^ k) := NeZero.mk (Nat.ne_of_gt (Nat.pow_pos hp.pos))
  by_cases hnon : Nonempty (linnikSolutionFiber p k h hp.pos g)
  case pos =>
    let a0 : linnikSolutionFiber p k h hp.pos g := Classical.choice hnon
    let target := {v : Fin k -> ZMod (p ^ k) //
      Finset.univ.val.map v =
        Finset.univ.val.map
          (fun r : Fin k => ((a0.val.val r).val : ZMod (p ^ k)))}
    let map : linnikSolutionFiber p k h hp.pos g -> target := fun a =>
      Subtype.mk (fun r : Fin k => ((a.val.val r).val : ZMod (p ^ k)))
        (zmod_multiset_eq_of_linnikSolutionFiber p k hp hk hkp h g a a0)
    have hmap : Function.Injective map := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      funext r
      apply Fin.ext
      have hfun : (fun s : Fin k => ((a.val.val s).val : ZMod (p ^ k))) =
          (fun s : Fin k => ((b.val.val s).val : ZMod (p ^ k))) :=
        congrArg (fun z : target => z.val) hab
      have hval := congrArg (fun v : Fin k -> ZMod (p ^ k) => (v r).val) hfun
      simpa only [ZMod.val_natCast_of_lt (a.val.val r).isLt,
        ZMod.val_natCast_of_lt (b.val.val r).isLt] using hval
    calc
      Fintype.card (linnikSolutionFiber p k h hp.pos g) <= Fintype.card target :=
        Fintype.card_le_of_injective map hmap
      _ <= k.factorial := multiset_fiber_card_le_factorial k
        (fun r : Fin k => ((a0.val.val r).val : ZMod (p ^ k)))
  case neg =>
    letI : IsEmpty (linnikSolutionFiber p k h hp.pos g) :=
      not_nonempty_iff.mp hnon
    rw [Fintype.card_eq_zero]
    exact Nat.zero_le _

/-- Linnik's complete local bound for A(p,h), with all compatible
full-modulus right-hand-side representatives retained. -/
theorem card_linnikCongruenceSolutions_le_factorial_mul_product
    (p k : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (h : Fin k -> Nat) :
    Fintype.card (linnikCongruenceSolutions p k h) <=
      k.factorial *
        Finset.univ.prod (fun j : Fin k => p ^ (k - (j.val + 1))) := by
  classical
  let ef : forall g : linnikCompatibleRepresentatives p k h,
      Equiv (linnikSolutionFiber p k h hp.pos g)
        {m : linnikCongruenceSolutions p k h //
          linnikSolutionCompatibleRepresentative p k h hp.pos m = g} :=
    fun _g => Equiv.refl _
  let e :
      Equiv
        (Sigma fun g : linnikCompatibleRepresentatives p k h =>
          linnikSolutionFiber p k h hp.pos g)
        (linnikCongruenceSolutions p k h) :=
    (Equiv.sigmaCongrRight ef).trans
      (Equiv.sigmaFiberEquiv
        (linnikSolutionCompatibleRepresentative p k h hp.pos))
  calc
    Fintype.card (linnikCongruenceSolutions p k h) =
        Fintype.card (Sigma fun g : linnikCompatibleRepresentatives p k h =>
          linnikSolutionFiber p k h hp.pos g) := by
      exact (Fintype.card_congr e).symm
    _ = Finset.univ.sum (fun g : linnikCompatibleRepresentatives p k h =>
        Fintype.card (linnikSolutionFiber p k h hp.pos g)) :=
      Fintype.card_sigma
    _ <= Finset.univ.sum
        (fun _g : linnikCompatibleRepresentatives p k h => k.factorial) := by
      apply Finset.sum_le_sum
      intro g hg
      exact card_linnikSolutionFiber_le_factorial p k hp hk hkp h g
    _ = Fintype.card (linnikCompatibleRepresentatives p k h) * k.factorial := by
      simp
    _ = (Finset.univ.prod fun j : Fin k => p ^ (k - (j.val + 1))) *
        k.factorial := by
      rw [card_linnikCompatibleRepresentatives p k h hp.pos]
    _ = k.factorial *
        Finset.univ.prod (fun j : Fin k => p ^ (k - (j.val + 1))) :=
      Nat.mul_comm _ _

/-- The local power-sum fiber with pairwise distinct reductions modulo the
underlying prime. This is the fixed-right-hand-side local fiber in Linnik's
argument. -/
def linnikPowerSumFiber (p u q : Nat) (hu : 0 < u)
    (f : Fin q -> ZMod (p ^ u)) : Type :=
  {g : Fin q -> ZMod (p ^ u) //
    Function.Injective (fun t : Fin q =>
      ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p) (g t)) /\
    forall i : Nat, i <= q ->
      MvPolynomial.aeval f (MvPolynomial.psum (Fin q) (ZMod (p ^ u)) i) =
        MvPolynomial.aeval g (MvPolynomial.psum (Fin q) (ZMod (p ^ u)) i)}

/-- The local fiber is finite when the prime-power modulus is nonzero. -/
noncomputable instance linnikPowerSumFiberFintype (p u q : Nat) (hu : 0 < u)
    (f : Fin q -> ZMod (p ^ u)) [NeZero (p ^ u)] :
    Fintype (linnikPowerSumFiber p u q hu f) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Linnik's fixed local power-sum fiber has at most q factorial members. -/
theorem card_linnikPowerSumFiber_le_factorial (p u q : Nat) (hp : p.Prime)
    (hu : 0 < u) [NeZero (p ^ u)] (hqp : q < p) (f : Fin q -> ZMod (p ^ u))
    (hinjf : Function.Injective (fun t : Fin q =>
      ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hu)) (ZMod p) (f t))) :
    Fintype.card (linnikPowerSumFiber p u q hu f) <= q.factorial := by
  classical
  let target := {g : Fin q -> ZMod (p ^ u) //
    Finset.univ.val.map g = Finset.univ.val.map f}
  let map : linnikPowerSumFiber p u q hu f -> target := fun g =>
    Subtype.mk g.val
      (ZMod.multiset_eq_of_power_sums_of_reduction_injective p u q hp hu hqp
        f g.val hinjf g.property.1 g.property.2).symm
  have hmap : Function.Injective map := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : target => z.val) hab
  calc
    Fintype.card (linnikPowerSumFiber p u q hu f) <= Fintype.card target :=
      Fintype.card_le_of_injective map hmap
    _ <= q.factorial := multiset_fiber_card_le_factorial q f

/-- A finite range product of powers of one base is that base raised to the
sum of the range exponents. -/
theorem prod_range_powers_eq_pow_sum (p k : Nat) (e : Nat -> Nat) :
    Finset.prod (Finset.range k) (fun i => p ^ (e i)) =
      p ^ (Finset.sum (Finset.range k) e) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, ih, pow_add]

/-- The exact Linnik quotient-coordinate product is a single power whose
exponent is the corresponding finite triangular sum. -/
theorem linnikLowerModulusChoices_product_eq_power_sum (p k : Nat) :
    Finset.univ.prod (fun j : Fin k => p ^ (k - (j.val + 1))) =
      p ^ (Finset.sum (Finset.range k) (fun j => k - (j + 1))) := by
  calc
    Finset.univ.prod (fun j : Fin k => p ^ (k - (j.val + 1))) =
        Finset.prod (Finset.range k) (fun j => p ^ (k - (j + 1))) :=
      (Finset.prod_range (fun j => p ^ (k - (j + 1)))).symm
    _ = p ^ (Finset.sum (Finset.range k) (fun j => k - (j + 1))) :=
      prod_range_powers_eq_pow_sum p k (fun j => k - (j + 1))

/-- The Linnik quotient-coordinate exponent is the usual triangular number. -/
theorem linnikLowerModulusChoices_exponent_sum (k : Nat) :
    Finset.sum (Finset.range k) (fun j => k - (j + 1)) =
      k * (k - 1) / 2 := by
  calc
    Finset.sum (Finset.range k) (fun j => k - (j + 1)) =
        Finset.sum (Finset.range k) (fun j => (k - 1) - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.sub_sub]
      rw [Nat.add_comm]
    _ = Finset.sum (Finset.range k) (fun j => j) :=
      Finset.sum_range_reflect (fun j => j) k
    _ = k * (k - 1) / 2 := Finset.sum_range_id k

/-- The exact Linnik quotient-coordinate count in its standard triangular
power form. -/
theorem linnikLowerModulusChoices_product_eq_standard_power (p k : Nat) :
    Finset.univ.prod (fun j : Fin k => p ^ (k - (j.val + 1))) =
      p ^ (k * (k - 1) / 2) := by
  rw [linnikLowerModulusChoices_product_eq_power_sum]
  rw [linnikLowerModulusChoices_exponent_sum]

/-- Linnik's complete local bound for A(p,h) in standard triangular-power
form. -/
theorem card_linnikCongruenceSolutions_le
    (p k : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (h : Fin k -> Nat) :
    Fintype.card (linnikCongruenceSolutions p k h) <=
      k.factorial * p ^ (k * (k - 1) / 2) := by
  calc
    Fintype.card (linnikCongruenceSolutions p k h) <=
        k.factorial *
          Finset.univ.prod (fun j : Fin k => p ^ (k - (j.val + 1))) :=
      card_linnikCongruenceSolutions_le_factorial_mul_product
        p k hp hk hkp h
    _ = k.factorial * p ^ (k * (k - 1) / 2) := by
      rw [linnikLowerModulusChoices_product_eq_standard_power]

end Finset
