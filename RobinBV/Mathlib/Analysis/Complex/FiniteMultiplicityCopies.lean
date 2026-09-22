/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import RobinBV.Mathlib.Analysis.Complex.RealNearColor

/-!
# Exact finite natural-multiplicity copies

The ambient sigma type is independent of the finite set and multiplicity.
Filtering preserves exact mass, and the ordered quadruple near-energy retains
repeated parents and repeated heights at both closed endpoints. These copies
are consumed by the actual zero-band reflection energy construction.
-/

set_option autoImplicit false

namespace Finset

def natMultiplicityCopies {u : Type*} (A : Finset u) (m : u -> Nat) :
    Finset (Sigma (fun _ : u => Nat)) :=
  A.sigma (fun x => Finset.range (m x))

theorem mem_natMultiplicityCopies {u : Type*} (A : Finset u) (m : u -> Nat)
    (p : Sigma (fun _ : u => Nat)) :
    Membership.mem (natMultiplicityCopies A m) p <->
      Membership.mem A p.1 /\ p.2 < m p.1 := by
  simp only [natMultiplicityCopies, Finset.mem_sigma, Finset.mem_range]

theorem filter_natMultiplicityCopies {u : Type*} [DecidableEq u]
    (A : Finset u) (m : u -> Nat) (Q : u -> Prop) [DecidablePred Q] :
    (natMultiplicityCopies A m).filter (fun p => Q p.1) =
      natMultiplicityCopies (A.filter Q) m := by
  ext p
  simp only [Finset.mem_filter, mem_natMultiplicityCopies]
  exact and_right_comm

theorem card_natMultiplicityCopies {u : Type*} (A : Finset u) (m : u -> Nat) :
    (natMultiplicityCopies A m).card = A.sum m := by
  simp only [natMultiplicityCopies, Finset.card_sigma, Finset.card_range]

theorem card_filter_natMultiplicityCopies {u : Type*} [DecidableEq u]
    (A : Finset u) (m : u -> Nat) (Q : u -> Prop) [DecidablePred Q] :
    ((natMultiplicityCopies A m).filter (fun p => Q p.1)).card =
      (A.filter Q).sum m := by
  rw [filter_natMultiplicityCopies, card_natMultiplicityCopies]

theorem sum_natMultiplicityCopies {u : Type*} (A : Finset u) (m : u -> Nat)
    (f : u -> Real) :
    (natMultiplicityCopies A m).sum (fun p => f p.1) =
      A.sum (fun x => (m x : Real)*f x) := by
  rw [natMultiplicityCopies, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem sum_four_natMultiplicityCopies {u : Type*} (A : Finset u) (m : u -> Nat)
    (f : u -> u -> u -> u -> Real) :
    (natMultiplicityCopies A m).sum (fun a =>
      (natMultiplicityCopies A m).sum (fun b =>
        (natMultiplicityCopies A m).sum (fun c =>
          (natMultiplicityCopies A m).sum (fun d => f a.1 b.1 c.1 d.1)))) =
      A.sum (fun a => A.sum (fun b => A.sum (fun c => A.sum (fun d =>
        (m a : Real)*((m b : Real)*((m c : Real)*((m d : Real)*f a b c d))))))) := by
  unfold natMultiplicityCopies
  simp only [Finset.sum_sigma]
  try dsimp only
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]

end Finset

namespace Real

theorem finiteNearEnergy_natMultiplicityCopies {u : Type*}
    (A : Finset u) (m : u -> Nat) (H : u -> Real) (r : Real) :
    finiteNearEnergy (Finset.natMultiplicityCopies A m) (fun p => H p.1) r =
      A.sum (fun a => A.sum (fun b => A.sum (fun c => A.sum (fun d =>
        if abs ((H a+H b)-(H c+H d)) <= r
        then ((m a : Real)*(m b : Real))*((m c : Real)*(m d : Real))
        else 0)))) := by
  classical
  calc
    _ = A.sum (fun a => A.sum (fun b => A.sum (fun c => A.sum (fun d =>
        (m a : Real)*((m b : Real)*((m c : Real)*((m d : Real)*
          (if abs ((H a+H b)-(H c+H d)) <= r then 1 else 0)))))))) := by
      have h := Finset.sum_four_natMultiplicityCopies A m
        (fun a b c d => if abs ((H a+H b)-(H c+H d)) <= r then 1 else 0)
      simpa only [finiteNearEnergy, finiteNearPairCount, Finset.sum_product] using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : abs ((H a+H b)-(H c+H d)) <= r
      next =>
        simp only [if_pos h]
        ring
      next =>
        simp only [if_neg h, mul_zero]

end Real
