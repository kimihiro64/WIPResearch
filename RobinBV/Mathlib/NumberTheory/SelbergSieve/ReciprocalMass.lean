/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# ReciprocalMass

Finite Selberg sieve input, proved from Mathlib primitives.
The classical sieve argument follows D. R. Heath-Brown, Lectures on sieves,
Sections 2-3 (https://arxiv.org/abs/math/0209360).
No prime-distribution or unproved analytic hypothesis is introduced.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat

noncomputable def reciprocalMonoidHom : MonoidHom Nat Real where
  toFun n := (n : Real)^(-1 : Int)
  map_one' := by simp
  map_mul' m n := by simp [Nat.cast_mul, mul_comm]

private theorem reciprocal_prime_norm_lt_one {p : Nat} (hp : Nat.Prime p) :
    norm (reciprocalMonoidHom p) < 1 := by
  change norm ((p : Real)^(-1 : Int)) < 1
  have hip : (0 : Real) <= Inv.inv (p : Real) := by positivity
  simp only [zpow_neg_one, Real.norm_eq_abs, abs_of_nonneg hip]
  have hp0 : Not ((p : Real) = 0) := by exact_mod_cast hp.ne_zero
  have hrec : (p : Real)*(p : Real)^(-1 : Int) = 1 := by field_simp
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  by_contra hh
  have hge : (1 : Real) <= (p : Real)^(-1 : Int) := by
    simpa only [zpow_neg_one] using (not_lt.mp hh)
  have hm := _root_.mul_le_mul_of_nonneg_left hge (show (0 : Real) <= p by positivity)
  nlinarith

/-- The reciprocal mass of any finite set supported on finitely many prime
factors is bounded by its exact finite Euler product. This will bound each
radical fiber in the Selberg denominator, not assume a sieve estimate. -/
theorem sum_reciprocal_le_euler_product (A s : Finset Nat)
    (hA : forall m, Membership.mem A m -> Membership.mem (Nat.factoredNumbers s) m) :
    A.sum (fun m => (m : Real)^(-1 : Int)) <=
      (s.filter Nat.Prime).prod (fun p => (1-(p : Real)^(-1 : Int))^(-1 : Int)) := by
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalMonoidHom) (fun {_} hp => reciprocal_prime_norm_lt_one hp) s
  let B : Finset (Nat.factoredNumbers s) := A.attach.image
    (fun m => (Subtype.mk m.val (hA m.val m.property) : Nat.factoredNumbers s))
  have he : B.sum (fun m => (m.val : Real)^(-1 : Int)) =
      A.sum (fun m => (m : Real)^(-1 : Int)) := by
    dsimp [B]
    rw [Finset.sum_image]
    next => exact Finset.sum_attach A (fun m : Nat => (m : Real)^(-1 : Int))
    next =>
      intro x _ y _ hxy
      apply Subtype.ext
      change x.val = y.val
      exact congrArg (fun v : Nat.factoredNumbers s => v.val) hxy
  have hle := Summable.sum_le_tsum B
    (fun (m : Nat.factoredNumbers s) _ =>
      (show (0 : Real) <= reciprocalMonoidHom m.val by
        change (0 : Real) <= (m.val : Real)^(-1 : Int)
        positivity))
    (Summable.of_norm hs.1)
  rw [hs.2.tsum_eq] at hle
  change B.sum (fun m => (m.val : Real)^(-1 : Int)) <= _ at hle
  rw [he] at hle
  simpa only [reciprocalMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk, zpow_neg_one] using hle

end Nat
