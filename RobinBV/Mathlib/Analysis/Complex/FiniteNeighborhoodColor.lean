/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Data.Fintype.Card

/-!
# Finite neighborhood coloring

Finite induction assigns one of exactly `K` colors when every neighborhood has
fewer than `K` elements. The result is the combinatorial input to the actual
zero-copy separation construction; it introduces no analytic or arithmetic
estimate.
-/

set_option autoImplicit false

namespace Finset

private theorem finiteColor_unused {K : Nat} (A : Finset (Fin K)) (hA : A.card < K) :
    exists c : Fin K, Not (Membership.mem A c) := by
  classical
  by_contra hnone
  have hcover : (Finset.univ : Finset (Fin K)) <= A := by
    intro c hc
    by_contra hnot
    exact hnone (Exists.intro c hnot)
  have hcard : K <= A.card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hcover
  exact (not_lt_of_ge hcard) hA

theorem exists_coloring_of_finite_neighborhood {u : Type*} [DecidableEq u]
    (S : Finset u) (r : u -> u -> Prop) [DecidableRel r]
    (hsym : forall x y, r x y -> r y x) (K : Nat) (hK : 0 < K)
    (hbound : forall x, Membership.mem S x -> (S.filter (r x)).card < K) :
    exists color : u -> Fin K,
      forall x, Membership.mem S x -> forall y, Membership.mem S y ->
      Not (x = y) -> color x = color y -> Not (r x y) := by
  classical
  revert hbound
  induction S using Finset.induction_on with
  | empty =>
    intro _hbound
    refine Exists.intro (fun _ => Fin.mk 0 hK) ?_
    intro x hx
    simp at hx
  | insert a S ha ih =>
    intro hbound
    have hsub (x : u) : S.filter (r x) <=
        (Insert.insert a S : Finset u).filter (r x) := by
      intro y hy
      have hp := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr
        (And.intro (Finset.mem_insert.mpr (Or.inr hp.1)) hp.2)
    have hboundOld : forall x, Membership.mem S x -> (S.filter (r x)).card < K := by
      intro x hx
      exact (Finset.card_le_card (hsub x)).trans_lt
        (hbound x (Finset.mem_insert.mpr (Or.inr hx)))
    cases ih hboundOld with
    | intro old hold =>
      let forbidden : Finset (Fin K) := (S.filter (r a)).image old
      have hbad : forbidden.card < K := by
        have himage : forbidden.card <= (S.filter (r a)).card := Finset.card_image_le
        exact himage.trans_lt ((Finset.card_le_card (hsub a)).trans_lt
          (hbound a (by simp)))
      cases finiteColor_unused forbidden hbad with
      | intro fresh hfresh =>
        let color : u -> Fin K := fun x => if x = a then fresh else old x
        have hfree (y : u) (hy : Membership.mem S y)
            (hcol : fresh = old y) : Not (r a y) := by
          intro hr
          have hm : Membership.mem forbidden (old y) :=
            Finset.mem_image.mpr (Exists.intro y
              (And.intro (Finset.mem_filter.mpr (And.intro hy hr)) rfl))
          apply hfresh
          rw [hcol]
          exact hm
        refine Exists.intro color ?_
        intro x hx y hy hne hcol hr
        by_cases hxa : x = a
        next =>
          subst x
          have hya : Not (y = a) := fun he => hne he.symm
          have hyS : Membership.mem S y := (Finset.mem_insert.mp hy).resolve_left hya
          have hc : fresh = old y := by
            simpa only [color, if_pos rfl, if_neg hya] using hcol
          exact hfree y hyS hc hr
        next =>
          have hxS : Membership.mem S x := (Finset.mem_insert.mp hx).resolve_left hxa
          by_cases hya : y = a
          next =>
            subst y
            have hc : old x = fresh := by
              simpa only [color, if_neg hxa, if_pos rfl] using hcol
            exact hfree x hxS hc.symm (hsym x a hr)
          next =>
            have hyS : Membership.mem S y := (Finset.mem_insert.mp hy).resolve_left hya
            have hc : old x = old y := by
              simpa only [color, if_neg hxa, if_neg hya] using hcol
            exact hold x hxS y hyS hne hc hr

end Finset
