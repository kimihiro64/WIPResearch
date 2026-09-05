/-
Copyright (c) 2026 Jonas Whidden.
Ported from robin commit b6a7dff5f9546131cf668a9c8bfa436f4650bc0d.
Authors: Jonas Whidden
Released under Apache 2.0 license as described in the file LICENSE.
The original MIT copyright and permission notice is retained below.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Ring
import RobinBV.Mathlib.NumberTheory.PrimeSieve.Owner

/-!
# Least-prime owner telescope with arbitrary local densities

The complete future-weighted recurrence is extracted from
ExactLeastPrimeOwnerDefect in robin at the revision in the copyright header.
The density 1/p is generalized to an arbitrary real function g(p).
The error bounds retain all future factors and allow a factor to vanish;
no projective division or sign assumption on individual defects is used.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

noncomputable section

/-- Weighted mass before the owner fires. -/
def leastPrimeOwnerSurvivorMass (F : Nat -> Real) (p U : Nat) : Real :=
  Finset.sum (leastPrimeOwnerSurvivorsBefore p U) F

/-- The entire mass removed by the owner. -/
def leastPrimeOwnerActualMass (F : Nat -> Real) (p U : Nat) : Real :=
  Finset.sum (leastPrimeOwnerPacketAt p U) F

/-- Expected removal at local density g(p), minus actual removal. -/
def leastPrimeOwnerStageDefect (F g : Nat -> Real) (p U : Nat) : Real :=
  g p * leastPrimeOwnerSurvivorMass F p U -
    leastPrimeOwnerActualMass F p U

/-- Exact finite-horizon recurrence retaining every owner and future factor. -/
theorem survivorMass_eq_density_add_weightedDefects
    (F g : Nat -> Real) (U z : Nat) :
    Finset.sum
        (by
          classical
          exact (Finset.Icc 2 U).filter (NoPrimeDivisorUpTo z)) F =
      (Finset.prod (Nat.primesLE z) (fun p =>
          (1 : Real) - g p)) *
          Finset.sum (Finset.Icc 2 U) F +
        Finset.sum (Nat.primesLE z) (fun p =>
          (Finset.prod ((Nat.primesLE z).filter (fun q => p < q))
            (fun q => (1 : Real) - g q)) *
              leastPrimeOwnerStageDefect F g p U) := by
  classical
  induction z with
  | zero =>
      have hFilter :
          (Finset.Icc 2 U).filter (NoPrimeDivisorUpTo 0) =
            Finset.Icc 2 U := by
        apply Finset.filter_eq_self.mpr
        intro n hn q hqPrime hqLe hqDiv
        have hqTwo : 2 <= q := hqPrime.two_le
        omega
      rw [hFilter]
      simp [Nat.primesLE_zero]
  | succ z ih =>
      by_cases hp : Nat.Prime (z + 1)
      . let p := z + 1
        have hpPrime : Nat.Prime p := hp
        have hpNotMem : Not (Membership.mem (Nat.primesLE z) p) := by
          exact Nat.notMem_primesLE z
        have hBefore :
            leastPrimeOwnerSurvivorsBefore p U =
              (Finset.Icc 2 U).filter (NoPrimeDivisorUpTo z) := by
          unfold leastPrimeOwnerSurvivorsBefore p
          simp
        have hAfter :
            leastPrimeOwnerSurvivorsAfter p U =
              (Finset.Icc 2 U).filter (NoPrimeDivisorUpTo p) := by
          simpa using
            (leastPrimeOwnerSurvivorsAfter_eq_noPrimeDivisorUpTo
              (U := U) hpPrime)
        have hStage :=
          sum_leastPrimeOwnerSurvivorsBefore_eq_owner_add_after F p U
        have hRecRaw :
            Finset.sum (leastPrimeOwnerSurvivorsAfter p U) F =
              ((1 : Real) - g p) *
                  Finset.sum (leastPrimeOwnerSurvivorsBefore p U) F +
                leastPrimeOwnerStageDefect F g p U := by
          unfold leastPrimeOwnerStageDefect
          unfold leastPrimeOwnerSurvivorMass leastPrimeOwnerActualMass
          rw [hStage]
          ring
        have hRec :
            Finset.sum
                ((Finset.Icc 2 U).filter (NoPrimeDivisorUpTo p)) F =
              ((1 : Real) - g p) *
                  Finset.sum
                    ((Finset.Icc 2 U).filter
                      (NoPrimeDivisorUpTo z)) F +
                leastPrimeOwnerStageDefect F g p U := by
          rw [<- hAfter, <- hBefore]
          exact hRecRaw
        have hFutureOld : forall q : Nat,
            Membership.mem (Nat.primesLE z) q ->
            Finset.prod
                ((insert p (Nat.primesLE z)).filter (fun r => q < r))
                (fun r => (1 : Real) - g r) =
              ((1 : Real) - g p) *
                Finset.prod
                  ((Nat.primesLE z).filter (fun r => q < r))
                  (fun r => (1 : Real) - g r) := by
          intro q hq
          have hqLe : q <= z := Nat.le_of_mem_primesLE hq
          have hqp : q < p := by simp [p]; omega
          rw [Finset.filter_insert]
          simp only [if_pos hqp]
          rw [Finset.prod_insert]
          intro hpFiltered
          exact hpNotMem (Finset.mem_filter.mp hpFiltered).1
        have hFutureNew :
            Finset.prod
                ((insert p (Nat.primesLE z)).filter (fun r => p < r))
                (fun r => (1 : Real) - g r) = 1 := by
          apply Finset.prod_eq_one
          intro q hq
          have hqData := Finset.mem_filter.mp hq
          have hqLe : q <= p := by
            rcases Finset.mem_insert.mp hqData.1 with hEq | hqOld
            . omega
            . have hqOldLe : q <= z := Nat.le_of_mem_primesLE hqOld
              simp [p]
              omega
          exfalso
          omega
        have hSumFuture :
            Finset.sum (Nat.primesLE z) (fun q =>
                (Finset.prod
                  ((insert p (Nat.primesLE z)).filter (fun r => q < r))
                  (fun r => (1 : Real) - g r)) *
                    leastPrimeOwnerStageDefect F g q U) =
              ((1 : Real) - g p) *
                Finset.sum (Nat.primesLE z) (fun q =>
                  (Finset.prod
                    ((Nat.primesLE z).filter (fun r => q < r))
                    (fun r => (1 : Real) - g r)) *
                      leastPrimeOwnerStageDefect F g q U) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          rw [hFutureOld q hq]
          ring
        rw [show z + 1 = p by rfl]
        rw [hRec, ih]
        rw [show Nat.primesLE p = insert p (Nat.primesLE z) by
          simpa [p, Nat.primesLE_succ, hp]]
        rw [Finset.prod_insert hpNotMem, Finset.sum_insert hpNotMem]
        rw [hFutureNew]
        simp only [one_mul]
        rw [hSumFuture]
        ring
      . have hNoPrimeEq : forall n : Nat,
            NoPrimeDivisorUpTo (z + 1) n <->
              NoPrimeDivisorUpTo z n := by
          intro n
          constructor
          . intro h q hqPrime hqLe hqDiv
            exact h q hqPrime (by omega) hqDiv
          . intro h q hqPrime hqLe hqDiv
            have hqNe : Not (q = z + 1) := by
              intro hEq
              apply hp
              simpa [hEq] using hqPrime
            exact h q hqPrime (by omega) hqDiv
        have hFilterEq :
            (Finset.Icc 2 U).filter (NoPrimeDivisorUpTo (z + 1)) =
              (Finset.Icc 2 U).filter (NoPrimeDivisorUpTo z) := by
          ext n
          simp only [Finset.mem_filter]
          exact and_congr_right (fun _ => hNoPrimeEq n)
        rw [hFilterEq]
        simpa [Nat.primesLE_succ, hp] using ih


/-- The density factors strictly after owner p and through z. -/
def futureDensity (g : Nat -> Real) (z p : Nat) : Real :=
  Finset.prod ((Nat.primesLE z).filter (fun q => p < q))
    (fun q => (1 : Real) - g q)

/-- Complete survivor discrepancy from the chosen independent density. -/
def survivorError (F g : Nat -> Real) (U z : Nat) : Real := by
  classical
  exact Finset.sum ((Finset.Icc 2 U).filter (NoPrimeDivisorUpTo z)) F -
    (Finset.prod (Nat.primesLE z) (fun p => (1 : Real) - g p)) *
      Finset.sum (Finset.Icc 2 U) F

theorem survivorError_eq_weightedDefects
    (F g : Nat -> Real) (U z : Nat) :
    survivorError F g U z =
      Finset.sum (Nat.primesLE z) (fun p =>
        futureDensity g z p * leastPrimeOwnerStageDefect F g p U) := by
  classical
  unfold survivorError
  rw [survivorMass_eq_density_add_weightedDefects F g U z]
  simp [futureDensity]

theorem futureDensity_nonneg
    {g : Nat -> Real} {z : Nat}
    (hg : forall p, Membership.mem (Nat.primesLE z) p -> g p <= 1)
    (p : Nat) :
    0 <= futureDensity g z p := by
  apply Finset.prod_nonneg
  intro q hq
  exact sub_nonneg.mpr (hg q (Finset.mem_filter.mp hq).1)

theorem futureDensity_le_one
    {g : Nat -> Real} {z : Nat}
    (hg : forall p, Membership.mem (Nat.primesLE z) p ->
      And (0 <= g p) (g p <= 1)) (p : Nat) :
    futureDensity g z p <= 1 := by
  apply Finset.prod_le_one
  . intro q hq
    exact sub_nonneg.mpr (hg q (Finset.mem_filter.mp hq).1).2
  . intro q hq
    exact sub_le_self 1 (hg q (Finset.mem_filter.mp hq).1).1

/-- Complete weighted absolute error, with the actual future densities. -/
theorem abs_survivorError_le_weighted_abs_defects
    (F g : Nat -> Real) (U z : Nat)
    (hg : forall p, Membership.mem (Nat.primesLE z) p -> g p <= 1) :
    abs (survivorError F g U z) <=
      Finset.sum (Nat.primesLE z) (fun p =>
        futureDensity g z p * abs (leastPrimeOwnerStageDefect F g p U)) := by
  rw [survivorError_eq_weightedDefects]
  calc
    _ <= Finset.sum (Nat.primesLE z) (fun p =>
        abs (futureDensity g z p * leastPrimeOwnerStageDefect F g p U)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [abs_mul, abs_of_nonneg (futureDensity_nonneg hg p)]

/-- A complete error budget can be transported without losing future weights. -/
theorem abs_survivorError_le_weighted_budget
    (F g E : Nat -> Real) (U z : Nat)
    (hg : forall p, Membership.mem (Nat.primesLE z) p -> g p <= 1)
    (hE : forall p, Membership.mem (Nat.primesLE z) p ->
      abs (leastPrimeOwnerStageDefect F g p U) <= E p) :
    abs (survivorError F g U z) <=
      Finset.sum (Nat.primesLE z) (fun p => futureDensity g z p * E p) := by
  apply (abs_survivorError_le_weighted_abs_defects F g U z hg).trans
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left (hE p hp) (futureDensity_nonneg hg p)

/-- Coarse contraction when every local density lies in the unit interval. -/
theorem abs_survivorError_le_sum_abs_defects
    (F g : Nat -> Real) (U z : Nat)
    (hg : forall p, Membership.mem (Nat.primesLE z) p ->
      And (0 <= g p) (g p <= 1)) :
    abs (survivorError F g U z) <=
      Finset.sum (Nat.primesLE z)
        (fun p => abs (leastPrimeOwnerStageDefect F g p U)) := by
  apply (abs_survivorError_le_weighted_abs_defects F g U z
    (fun p hp => (hg p hp).2)).trans
  apply Finset.sum_le_sum
  intro p hp
  calc
    futureDensity g z p * abs (leastPrimeOwnerStageDefect F g p U) <=
        1 * abs (leastPrimeOwnerStageDefect F g p U) :=
      mul_le_mul_of_nonneg_right (futureDensity_le_one hg p) (abs_nonneg _)
    _ = _ := one_mul _

end

end Nat.PrimeSieve
