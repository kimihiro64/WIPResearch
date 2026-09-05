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

import RobinBV.Mathlib.NumberTheory.PrimeSieve.Owner

/-!
# Scaled least-prime owner packets

Extracted from ExactLeastPrimeOwnerScaledTelescope at the source revision in
the copyright header. The cofactor one and repeated powers of the owner prime
are retained. The weighted equality accepts an arbitrary additive target.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

noncomputable section

/-- Cofactors at the smaller cutoff which survive every prime clock below
`p`.  The cofactor `1` is retained, so multiplication by `p` includes the
prime atom itself. -/
noncomputable def leastPrimeOwnerScaledCofactorsBefore
    (p U : Nat) : Finset Nat :=
  by
    classical
    exact (Finset.Icc 1 (U / p)).filter
      (NoPrimeDivisorUpTo (p - 1))

private theorem mul_mem_leastPrimeOwnerPacketAt_iff_scaledCofactor
    {p U r : Nat} (hp : Nat.Prime p) :
    Membership.mem (leastPrimeOwnerPacketAt p U) (p * r) <->
      Membership.mem (leastPrimeOwnerScaledCofactorsBefore p U) r := by
  classical
  simp only [leastPrimeOwnerPacketAt, leastPrimeOwnerSurvivorsBefore,
    leastPrimeOwnerScaledCofactorsBefore, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  . intro hn
    have hnRange := hn.1.1
    have hnNo := hn.1.2
    have hrPos : 1 <= r := by
      by_contra hr
      have hrZero : r = 0 := by omega
      subst r
      simp at hnRange
    have hrUpper : r <= U / p :=
      (Nat.le_div_iff_mul_le hp.pos).2 (by
        simpa [Nat.mul_comm] using hnRange.2)
    apply And.intro (And.intro hrPos hrUpper)
    intro q hqPrime hqLe hqDiv
    exact hnNo q hqPrime hqLe (dvd_mul_of_dvd_right hqDiv p)
  . intro hr
    have hrRange := hr.1
    have hrNo := hr.2
    have hLower : 2 <= p * r := by
      have := Nat.mul_le_mul hp.two_le hrRange.1
      simpa using this
    have hUpper : p * r <= U := by
      have := (Nat.le_div_iff_mul_le hp.pos).1 hrRange.2
      simpa [Nat.mul_comm] using this
    apply And.intro
    . apply And.intro (And.intro hLower hUpper)
      intro q hqPrime hqLe hqDiv
      rcases hqPrime.dvd_mul.mp hqDiv with hqP | hqR
      . have hEq : q = p :=
          (Nat.prime_dvd_prime_iff_eq hqPrime hp).mp hqP
        subst q
        have hpPos := hp.pos
        omega
      . exact hrNo q hqPrime hqLe hqR
    . exact dvd_mul_right p r

/-- Exact scaled-cofactor image of the complete packet owned at `p`. -/
theorem leastPrimeOwnerPacketAt_eq_image_scaledCofactors
    {p U : Nat} (hp : Nat.Prime p) :
    leastPrimeOwnerPacketAt p U =
      (leastPrimeOwnerScaledCofactorsBefore p U).image
        (fun r => p * r) := by
  classical
  ext n
  constructor
  . intro hn
    have hpDiv : Dvd.dvd p n := (Finset.mem_filter.mp hn).2
    have hMul : p * (n / p) = n := Nat.mul_div_cancel' hpDiv
    apply Finset.mem_image.mpr
    refine Exists.intro (n / p) ?_
    apply And.intro
    . apply
        (mul_mem_leastPrimeOwnerPacketAt_iff_scaledCofactor hp).mp
      simpa [hMul] using hn
    . exact hMul
  . intro hn
    have hExists := Finset.mem_image.mp hn
    let r := Classical.choose hExists
    have hrData := Classical.choose_spec hExists
    have hr := hrData.1
    have hEq := hrData.2
    simpa [hEq] using
      (mul_mem_leastPrimeOwnerPacketAt_iff_scaledCofactor hp).mpr hr

/-- Arbitrary-kernel packet identity at the smaller cutoff `U / p`. -/
theorem sum_leastPrimeOwnerPacketAt_eq_scaledCofactors
    {A : Type*} [AddCommMonoid A] (F : Nat -> A)
    {p U : Nat} (hp : Nat.Prime p) :
    Finset.sum (leastPrimeOwnerPacketAt p U) F =
      Finset.sum (leastPrimeOwnerScaledCofactorsBefore p U)
        (fun r => F (p * r)) := by
  classical
  rw [leastPrimeOwnerPacketAt_eq_image_scaledCofactors hp,
    Finset.sum_image]
  intro r _ s _ hrs
  exact Nat.mul_left_cancel hp.pos hrs

/-- The exact one-clock telescope in scale-descending form. -/
theorem sum_leastPrimeOwnerSurvivorsBefore_eq_scaledCofactors_add_after
    {A : Type*} [AddCommMonoid A] (F : Nat -> A)
    {p U : Nat} (hp : Nat.Prime p) :
    Finset.sum (leastPrimeOwnerSurvivorsBefore p U) F =
      Finset.sum (leastPrimeOwnerScaledCofactorsBefore p U)
          (fun r => F (p * r)) +
        Finset.sum (leastPrimeOwnerSurvivorsAfter p U) F := by
  rw [sum_leastPrimeOwnerSurvivorsBefore_eq_owner_add_after,
    sum_leastPrimeOwnerPacketAt_eq_scaledCofactors F hp]


end

end Nat.PrimeSieve
