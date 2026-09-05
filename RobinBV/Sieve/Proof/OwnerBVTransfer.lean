import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.Main
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# BV transfer with complete branch-coefficient budgets

This is a consequence of the dependency's centered maximal weighted BV
theorem. Classes and cutoffs may vary from branch to branch. The hypothesis
bounds the sum of absolute coefficients at EACH PRODUCT MODULUS, not each
individual coefficient. Constructing a sieve expansion with this budget is
a separate arithmetic obligation. No RH sign or improved distribution level
is asserted here.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

open BombieriVinogradov.WeightedBombieriVinogradov

/-- A single reduced-class error is bounded by the actual BV maximal error. -/
theorem abs_progressionError_le_maximal
    {X : Real} {q y : Nat} (a : Units (ZMod q))
    (hy : y <= Nat.floor X) :
    abs (psiProgression y q (a : ZMod q) -
      psiGlobal y / (q.totient : Real)) <= maximalWeightedDiscrepancy X q := by
  let F : Units (ZMod q) -> Real := fun b =>
    iSup (fun z : Fin (Nat.floor X + 1) =>
      abs (psiProgression z.val q (b : ZMod q) -
        psiGlobal z.val / (q.totient : Real)))
  let G : Fin (Nat.floor X + 1) -> Real := fun z =>
    abs (psiProgression z.val q (a : ZMod q) -
      psiGlobal z.val / (q.totient : Real))
  let z : Fin (Nat.floor X + 1) := {
    val := y
    isLt := Nat.lt_succ_of_le hy
  }
  have hInner : G z <= iSup G := le_ciSup (Set.finite_range G).bddAbove z
  have hOuter : F a <= iSup F := le_ciSup (Set.finite_range F).bddAbove a
  exact hInner.trans hOuter

/-- The total absolute error of finitely many weighted branches at each modulus. -/
noncomputable def branchWeightedDiscrepancy (Q : Nat)
    (branches : Nat -> Finset Nat) (c : Nat -> Nat -> Real)
    (a : (q : Nat) -> Nat -> Units (ZMod q)) (y : Nat -> Nat -> Nat) : Real :=
  Finset.sum (Finset.Icc 1 Q) (fun q =>
    abs (Finset.sum (branches q) (fun i => c q i *
      (psiProgression (y q i) q (a q i : ZMod q) -
        psiGlobal (y q i) / (q.totient : Real)))))

/-- Exact finite transfer retaining the complete coefficient fiber. -/
theorem branchWeightedDiscrepancy_le
    {X M : Real} {Q : Nat}
    (branches : Nat -> Finset Nat) (c : Nat -> Nat -> Real)
    (a : (q : Nat) -> Nat -> Units (ZMod q)) (y : Nat -> Nat -> Nat)
    (hy : forall q, Membership.mem (Finset.Icc 1 Q) q ->
      forall i, Membership.mem (branches q) i -> y q i <= Nat.floor X)
    (hBudget : forall q, Membership.mem (Finset.Icc 1 Q) q ->
      Finset.sum (branches q) (fun i => abs (c q i)) <= M) :
    branchWeightedDiscrepancy Q branches c a y <=
      M * averageWeightedDiscrepancy X Q := by
  unfold branchWeightedDiscrepancy averageWeightedDiscrepancy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  calc
    abs (Finset.sum (branches q) (fun i => c q i *
        (psiProgression (y q i) q (a q i : ZMod q) -
          psiGlobal (y q i) / (q.totient : Real)))) <=
        Finset.sum (branches q) (fun i => abs (c q i *
          (psiProgression (y q i) q (a q i : ZMod q) -
            psiGlobal (y q i) / (q.totient : Real)))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum (branches q) (fun i =>
        abs (c q i) * maximalWeightedDiscrepancy X q) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_progressionError_le_maximal (a q i) (hy q hq i hi)) (abs_nonneg _)
    _ = Finset.sum (branches q) (fun i => abs (c q i)) *
        maximalWeightedDiscrepancy X q := (Finset.sum_mul _ _ _).symm
    _ <= M * maximalWeightedDiscrepancy X q :=
      mul_le_mul_of_nonneg_right (hBudget q hq)
        (maximalWeightedDiscrepancy_nonneg X q)

/-- A polylogarithmic complete coefficient budget costs only logarithmic
saving. The BV constant is uniform in every branch, class, and cutoff choice. -/
theorem ownerWeightedBVTransfer
    (theta A B : Real) (hTheta : theta < 1 / 2) (hA : 1 <= A) (hB : 0 <= B) :
    exists C : Real, And (0 < C) (forall {X : Real}, 3 <= X ->
      forall (branches : Nat -> Finset Nat) (c : Nat -> Nat -> Real)
        (a : (q : Nat) -> Nat -> Units (ZMod q)) (y : Nat -> Nat -> Nat),
      (forall q, Membership.mem (Finset.Icc 1 (Nat.floor (X ^ theta))) q ->
        forall i, Membership.mem (branches q) i -> y q i <= Nat.floor X) ->
      (forall q, Membership.mem (Finset.Icc 1 (Nat.floor (X ^ theta))) q ->
        Finset.sum (branches q) (fun i => abs (c q i)) <= (Real.log X) ^ B) ->
      branchWeightedDiscrepancy (Nat.floor (X ^ theta)) branches c a y <=
        C * (X / (Real.log X) ^ A)) := by
  have hBV := weighted_bombieri_vinogradov theta hTheta (A + B) (by linarith)
  let C := Classical.choose hBV
  have hData := Classical.choose_spec hBV
  refine Exists.intro C (And.intro hData.1 ?_)
  intro X hX branches c a y hy hBudget
  have hLog : 0 < Real.log X := Real.log_pos (by linarith)
  have hPowA : Not ((Real.log X) ^ A = 0) := (Real.rpow_pos_of_pos hLog A).ne'
  have hPowB : Not ((Real.log X) ^ B = 0) := (Real.rpow_pos_of_pos hLog B).ne'
  calc
    branchWeightedDiscrepancy (Nat.floor (X ^ theta)) branches c a y <=
        (Real.log X) ^ B * averageWeightedDiscrepancy X (Nat.floor (X ^ theta)) :=
      branchWeightedDiscrepancy_le branches c a y hy hBudget
    _ <= (Real.log X) ^ B * (C * (X / (Real.log X) ^ (A + B))) :=
      mul_le_mul_of_nonneg_left (hData.2 hX) (Real.rpow_pos_of_pos hLog B).le
    _ = C * (X / (Real.log X) ^ A) := by
      rw [Real.rpow_add hLog]
      field_simp

end RobinBV.Sieve
