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

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite least-prime ownership

Project-independent extraction of CF4ClockSieve and ExactLeastPrimeOwnerStage
from the original robin repository. Every surviving multiple belongs to the
current prime's complete packet; arbitrary weights and all prime powers remain.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

noncomputable section

/-- No prime at most z divides n. -/
def NoPrimeDivisorUpTo (z n : Nat) : Prop :=
  forall p : Nat, Nat.Prime p -> p <= z -> Not (Dvd.dvd p n)

/-- Integers in `[2,U]` surviving every prime clock strictly below `p`. -/
noncomputable def leastPrimeOwnerSurvivorsBefore (p U : Nat) : Finset Nat :=
  by
    classical
    exact (Finset.Icc 2 U).filter (NoPrimeDivisorUpTo (p - 1))

/-- The complete packet owned at clock `p`: every current survivor divisible
by `p`. -/
noncomputable def leastPrimeOwnerPacketAt (p U : Nat) : Finset Nat :=
  by
    classical
    exact (leastPrimeOwnerSurvivorsBefore p U).filter (Dvd.dvd p)

/-- The survivors after clock `p`: every current survivor not divisible by
`p`. -/
noncomputable def leastPrimeOwnerSurvivorsAfter (p U : Nat) : Finset Nat :=
  by
    classical
    exact (leastPrimeOwnerSurvivorsBefore p U).filter
      (fun n => Not (Dvd.dvd p n))

/-- The owned packet and the next survivor set are disjoint. -/
theorem leastPrimeOwnerPacketAt_disjoint_survivorsAfter
    (p U : Nat) :
    Disjoint (leastPrimeOwnerPacketAt p U)
      (leastPrimeOwnerSurvivorsAfter p U) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro n hnOwner hnAfter
  have hDiv : Dvd.dvd p n := (Finset.mem_filter.mp hnOwner).2
  have hNotDiv : Not (Dvd.dvd p n) :=
    (Finset.mem_filter.mp hnAfter).2
  exact hNotDiv hDiv

/-- One ownership stage is an exact disjoint union of the owned packet and
the next survivor set. -/
theorem leastPrimeOwnerSurvivorsBefore_eq_owner_union_after
    (p U : Nat) :
    leastPrimeOwnerSurvivorsBefore p U =
      Finset.disjUnion (leastPrimeOwnerPacketAt p U)
        (leastPrimeOwnerSurvivorsAfter p U)
        (leastPrimeOwnerPacketAt_disjoint_survivorsAfter p U) := by
  classical
  ext n
  by_cases hDiv : Dvd.dvd p n <;>
    simp [leastPrimeOwnerSurvivorsBefore, leastPrimeOwnerPacketAt,
      leastPrimeOwnerSurvivorsAfter, hDiv]

/-- For prime `p`, the next survivor set is exactly the set surviving every
prime clock through `p`. -/
theorem leastPrimeOwnerSurvivorsAfter_eq_noPrimeDivisorUpTo
    {p U : Nat} (hp : Nat.Prime p) :
    leastPrimeOwnerSurvivorsAfter p U =
      (by
        classical
        exact (Finset.Icc 2 U).filter (NoPrimeDivisorUpTo p)) := by
  classical
  ext n
  simp only [leastPrimeOwnerSurvivorsAfter,
    leastPrimeOwnerSurvivorsBefore, Finset.mem_filter, Finset.mem_Icc]
  constructor
  . intro hn
    have hnBefore := hn.1
    have hnRange := hnBefore.1
    have hBefore := hnBefore.2
    have hNotDiv := hn.2
    apply And.intro hnRange
    intro q hqPrime hqLe hqDiv
    by_cases hqp : q = p
    . subst q
      exact hNotDiv hqDiv
    . exact hBefore q hqPrime (by omega) hqDiv
  . intro hn
    have hnRange := hn.1
    have hAfter := hn.2
    apply And.intro
    . apply And.intro hnRange
      intro q hqPrime hqLe hqDiv
      exact hAfter q hqPrime (by omega) hqDiv
    . exact hAfter p hp le_rfl

/-- The exact one-stage weighted telescope, valid for every additive target
and every kernel. -/
theorem sum_leastPrimeOwnerSurvivorsBefore_eq_owner_add_after
    {A : Type*} [AddCommMonoid A] (F : Nat -> A) (p U : Nat) :
    Finset.sum (leastPrimeOwnerSurvivorsBefore p U) F =
      Finset.sum (leastPrimeOwnerPacketAt p U) F +
        Finset.sum (leastPrimeOwnerSurvivorsAfter p U) F := by
  classical
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (leastPrimeOwnerSurvivorsBefore p U) (Dvd.dvd p) F
  simpa [leastPrimeOwnerPacketAt, leastPrimeOwnerSurvivorsAfter] using hSplit.symm

end

end Nat.PrimeSieve
