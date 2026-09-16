/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Real.Basic
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalPrimeAtoms

/-!
# Exact loss obstruction for arbitrary fifth-degree moment minorants

The sixth finite difference retains its binomial coefficients fifteen, fifteen
and one on the positive even classes. The consumer uses actual corrected
square-interval counts, without restricting the minorant to one root family.
This concerns small-prime moment support, not the native medium-prime weight.
-/

set_option autoImplicit false
open scoped Classical

namespace Polynomial

/-- The exact sixth-difference identity for every real polynomial of degree at most five. -/
theorem eval_zero_degree_five (P : Polynomial Real) (hdeg : P.natDegree<=5) :
    P.eval 0=6*P.eval 1-15*P.eval 2+20*P.eval 3-15*P.eval 4+6*P.eval 5-P.eval 6 := by
  have hz := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    (P := P) (show P.natDegree<6 by omega)) (0:Real)
  have hf := fwdDiff_iter_eq_sum_shift (1:Real) P.eval 6 0
  rw [hz] at hf
  norm_num [Finset.sum_range_succ, Nat.choose, zsmul_eq_mul] at hf
  linarith

/-- The exact loss against the zero-multiplicity indicator. -/
noncomputable def naturalMinorantLoss (P : Polynomial Real) (r : Nat) : Real :=
  if r=0 then 0 else -P.eval (r:Real)

/-- A normalized natural minorant has nonnegative exact zero-indicator loss. -/
theorem naturalMinorantLoss_nonneg (P : Polynomial Real)
    (hneg : forall r : Nat, 1<=r -> P.eval (r:Real)<=0) (r : Nat) :
    0<=P.naturalMinorantLoss r := by
  unfold naturalMinorantLoss
  split_ifs with hr
  next => exact le_rfl
  next => have h := hneg r (by omega); linarith

/-- The value and exact loss recover the zero-multiplicity indicator. -/
theorem eval_add_naturalMinorantLoss (P : Polynomial Real) (hzero : P.eval 0=1) (r : Nat) :
    P.eval (r:Real)+P.naturalMinorantLoss r=if r=0 then 1 else 0 := by
  by_cases hr : r=0
  next => subst r; simp [naturalMinorantLoss, hzero]
  next => simp [naturalMinorantLoss, hr]

/-- The complete finite ledger retains every point's exact minorant loss. -/
theorem sum_eval_add_naturalMinorantLoss {alpha : Type*} (s : Finset alpha)
    (r : alpha -> Nat) (P : Polynomial Real) (hzero : P.eval 0=1) :
    s.sum (fun x => P.eval (r x : Real))+s.sum (fun x => P.naturalMinorantLoss (r x)) =
      ((s.filter (fun x => r x=0)).card : Real) := by
  rw [<- Finset.sum_add_distrib]
  simp_rw [eval_add_naturalMinorantLoss P hzero]
  simp

/-- The exact even binomial coefficients force loss at multiplicities two, four or six. -/
theorem degree_five_minorant_even_loss (P : Polynomial Real) (hdeg : P.natDegree<=5)
    (hzero : P.eval 0=1) (hneg : forall r : Nat, 1<=r -> P.eval (r:Real)<=0) :
    1<=15*P.naturalMinorantLoss 2+15*P.naturalMinorantLoss 4+P.naturalMinorantLoss 6 := by
  have hi := eval_zero_degree_five P hdeg
  have h1 := hneg 1 (by decide)
  have h3 := hneg 3 (by decide)
  have h5 := hneg 5 (by decide)
  norm_num [naturalMinorantLoss] at *
  linarith

/-- The full loss dominates the three disjoint actual multiplicity classes. -/
theorem sum_naturalMinorantLoss_ge_even_cells {alpha : Type*} (s : Finset alpha)
    (r : alpha -> Nat) (P : Polynomial Real)
    (hneg : forall j : Nat, 1<=j -> P.eval (j:Real)<=0) :
    ((s.filter (fun x => r x=2)).card : Real)*P.naturalMinorantLoss 2+
      ((s.filter (fun x => r x=4)).card : Real)*P.naturalMinorantLoss 4+
      ((s.filter (fun x => r x=6)).card : Real)*P.naturalMinorantLoss 6 <=
      s.sum (fun x => P.naturalMinorantLoss (r x)) := by
  have hs : s.sum (fun x =>
      (if r x=2 then P.naturalMinorantLoss 2 else 0)+
      (if r x=4 then P.naturalMinorantLoss 4 else 0)+
      (if r x=6 then P.naturalMinorantLoss 6 else 0)) <=
      s.sum (fun x => P.naturalMinorantLoss (r x)) := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases h2 : r x=2
    next => simp [h2]
    next =>
      by_cases h4 : r x=4
      next => simp [h4]
      next =>
        by_cases h6 : r x=6
        next => simp [h6]
        next => simpa [h2,h4,h6] using naturalMinorantLoss_nonneg P hneg (r x)
  simpa only [Finset.sum_add_distrib, <- Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul] using hs

/-- The exact class capacities force a uniform total loss, retaining coefficients fifteen, fifteen and one. -/
theorem degree_five_loss_lower {alpha : Type*} (s : Finset alpha) (r : alpha -> Nat)
    (P : Polynomial Real) (hdeg : P.natDegree<=5) (hzero : P.eval 0=1)
    (hneg : forall j : Nat, 1<=j -> P.eval (j:Real)<=0) (M : Nat)
    (h2 : M<=(s.filter (fun x => r x=2)).card)
    (h4 : M<=(s.filter (fun x => r x=4)).card)
    (h6 : M<=15*(s.filter (fun x => r x=6)).card) :
    (M:Real)<=15*s.sum (fun x => P.naturalMinorantLoss (r x)) := by
  have hc2 : (M:Real)<=((s.filter (fun x => r x=2)).card : Real) := by exact_mod_cast h2
  have hc4 : (M:Real)<=((s.filter (fun x => r x=4)).card : Real) := by exact_mod_cast h4
  have hc6 : (M:Real)<=15*((s.filter (fun x => r x=6)).card : Real) := by exact_mod_cast h6
  have hm2 := mul_le_mul_of_nonneg_right hc2 (naturalMinorantLoss_nonneg P hneg 2)
  have hm4 := mul_le_mul_of_nonneg_right hc4 (naturalMinorantLoss_nonneg P hneg 4)
  have hm6 := mul_le_mul_of_nonneg_right hc6 (naturalMinorantLoss_nonneg P hneg 6)
  have hdual := mul_le_mul_of_nonneg_left (degree_five_minorant_even_loss P hdeg hzero hneg)
    (show (0:Real)<=(M:Real) by positivity)
  have hsum := sum_naturalMinorantLoss_ge_even_cells s r P hneg
  nlinarith only [hm2,hm4,hm6,hdual,hsum]

/-- No degree-five natural minorant is positive when the exact even class counts exceed these thresholds. -/
theorem sum_eval_degree_five_neg_of_even_excess {alpha : Type*} (s : Finset alpha)
    (r : alpha -> Nat) (P : Polynomial Real) (hdeg : P.natDegree<=5)
    (hzero : P.eval 0=1) (hneg : forall j : Nat, 1<=j -> P.eval (j:Real)<=0)
    (h2 : 15*(s.filter (fun x => r x=0)).card<(s.filter (fun x => r x=2)).card)
    (h4 : 15*(s.filter (fun x => r x=0)).card<(s.filter (fun x => r x=4)).card)
    (h6 : (s.filter (fun x => r x=0)).card<(s.filter (fun x => r x=6)).card) :
    s.sum (fun x => P.eval (r x : Real))<0 := by
  have hloss := degree_five_loss_lower s r P hdeg hzero hneg
    (15*(s.filter (fun x => r x=0)).card+1) (by omega) (by omega) (by omega)
  have hid := sum_eval_add_naturalMinorantLoss s r P hzero
  push_cast at hloss
  linarith

end Polynomial

namespace Nat.PrimeSieve

/-- Actual corrected square-interval multiplicity counts can rule out every real degree-five minorant simultaneously. -/
theorem square_degree_five_minorant_negative {n z : Nat} (hn : 2<=n) (hz : z<=n)
    (P : Polynomial Real) (hdeg : P.natDegree<=5) (hzero : P.eval 0=1)
    (hneg : forall j : Nat, 1<=j -> P.eval (j:Real)<=0)
    (h2 : 15*(squareIntervalPrimes n).card <
      ((squareMomentSurvivors n z).filter (fun m => squareMomentMultiplicity z m=2)).card)
    (h4 : 15*(squareIntervalPrimes n).card <
      ((squareMomentSurvivors n z).filter (fun m => squareMomentMultiplicity z m=4)).card)
    (h6 : (squareIntervalPrimes n).card <
      ((squareMomentSurvivors n z).filter (fun m => squareMomentMultiplicity z m=6)).card) :
    (squareMomentSurvivors n z).sum (fun m => P.eval (squareMomentMultiplicity z m : Real))<0 := by
  apply Polynomial.sum_eval_degree_five_neg_of_even_excess
    (squareMomentSurvivors n z) (squareMomentMultiplicity z) P hdeg hzero hneg
  all_goals rw [squareMomentSurvivors_filter_zero hn hz]
  next => exact h2
  next => exact h4
  next => exact h6

end Nat.PrimeSieve
