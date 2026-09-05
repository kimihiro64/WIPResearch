import RobinBV.Mathlib.NumberTheory.PrimeSieve.OwnerModuli
import RobinBV.Sieve.Proof.OwnerBVTransfer

/-!
# Owner-resolved Bombieri-Vinogradov

The index is an owner prime together with a finite set of smaller primes.
Its product modulus determines the entire index, so the multiplicity budget
is proved rather than assumed. Reduced classes and cutoffs may vary freely
with the branch. Every product modulus must remain inside the stated range.

This is an owner-resolved consequence of BV, not a larger distribution level.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

open BombieriVinogradov.WeightedBombieriVinogradov

/-- The full branch error sum charges each BV modulus at most once. -/
theorem ownerBranchErrors_le_average
    {X : Real} {Q : Nat} (branches : Finset (Prod Nat (Finset Nat)))
    (a : (b : Prod Nat (Finset Nat)) ->
      Units (ZMod (b.1 * Finset.prod b.2 (fun r => r))))
    (y : Prod Nat (Finset Nat) -> Nat)
    (hValid : forall b, Membership.mem branches b ->
      And (Nat.Prime b.1)
        (forall r, Membership.mem b.2 r -> And (Nat.Prime r) (r < b.1)))
    (hy : forall b, Membership.mem branches b -> y b <= Nat.floor X)
    (hRange : forall b, Membership.mem branches b ->
      b.1 * Finset.prod b.2 (fun r => r) <= Q) :
    Finset.sum branches (fun b =>
      abs (psiProgression (y b) (b.1 * Finset.prod b.2 (fun r => r)) (a b) -
        psiGlobal (y b) / ((b.1 * Finset.prod b.2 (fun r => r)).totient : Real))) <=
      averageWeightedDiscrepancy X Q := by
  classical
  let modulus : Prod Nat (Finset Nat) -> Nat :=
    fun b => b.1 * Finset.prod b.2 (fun r => r)
  have hInjective : forall b, Membership.mem branches b ->
      forall c, Membership.mem branches c -> modulus b = modulus c -> b = c := by
    intro b hb c hc hEq
    have hParts := Nat.PrimeSieve.ownerModulus_injective
      (hValid b hb).1 (hValid c hc).1 (hValid b hb).2 (hValid c hc).2 hEq
    exact Prod.ext hParts.1 hParts.2
  have hImageSum :
      Finset.sum (branches.image modulus) (maximalWeightedDiscrepancy X) =
        Finset.sum branches (fun b => maximalWeightedDiscrepancy X (modulus b)) := by
    apply Finset.sum_image
    intro b hb c hc hEq
    exact hInjective b hb c hc hEq
  have hImageRange : forall q, Membership.mem (branches.image modulus) q ->
      Membership.mem (Finset.Icc 1 Q) q := by
    intro q hq
    have hExists := Finset.mem_image.mp hq
    let b := Classical.choose hExists
    have hb : Membership.mem branches b := (Classical.choose_spec hExists).1
    have hEq : modulus b = q := (Classical.choose_spec hExists).2
    have hPos : 0 < modulus b :=
      Nat.mul_pos (hValid b hb).1.pos
        (Finset.prod_pos (fun r hr => ((hValid b hb).2 r hr).1.pos))
    have hMem : Membership.mem (Finset.Icc 1 Q) (modulus b) :=
      Finset.mem_Icc.mpr (And.intro (Nat.succ_le_iff.mpr hPos) (hRange b hb))
    simpa only [hEq] using hMem
  calc
    Finset.sum branches (fun b =>
        abs (psiProgression (y b) (b.1 * Finset.prod b.2 (fun r => r)) (a b) -
          psiGlobal (y b) / ((b.1 * Finset.prod b.2 (fun r => r)).totient : Real))) <=
        Finset.sum branches (fun b => maximalWeightedDiscrepancy X (modulus b)) := by
      apply Finset.sum_le_sum
      intro b hb
      exact abs_progressionError_le_maximal (a b) (hy b hb)
    _ = Finset.sum (branches.image modulus) (maximalWeightedDiscrepancy X) := hImageSum.symm
    _ <= averageWeightedDiscrepancy X Q := by
      unfold averageWeightedDiscrepancy
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun {q} hq => hImageRange q hq)
        (fun q _ _ => maximalWeightedDiscrepancy_nonneg X q)

/-- A uniform owner-resolved BV estimate. No total branch-multiplicity
hypothesis occurs: distinctness follows from the prime-owner geometry. -/
theorem ownerExpansionBV (theta A : Real) (hTheta : theta < 1 / 2) (hA : 1 <= A) :
    exists C : Real, And (0 < C) (forall {X : Real}, 3 <= X ->
      forall (branches : Finset (Prod Nat (Finset Nat)))
        (a : (b : Prod Nat (Finset Nat)) ->
          Units (ZMod (b.1 * Finset.prod b.2 (fun r => r))))
        (y : Prod Nat (Finset Nat) -> Nat),
      (forall b, Membership.mem branches b ->
        And (Nat.Prime b.1)
          (forall r, Membership.mem b.2 r -> And (Nat.Prime r) (r < b.1))) ->
      (forall b, Membership.mem branches b -> y b <= Nat.floor X) ->
      (forall b, Membership.mem branches b ->
        b.1 * Finset.prod b.2 (fun r => r) <= Nat.floor (X ^ theta)) ->
      Finset.sum branches (fun b =>
        abs (psiProgression (y b) (b.1 * Finset.prod b.2 (fun r => r)) (a b) -
          psiGlobal (y b) / ((b.1 * Finset.prod b.2 (fun r => r)).totient : Real))) <=
        C * (X / (Real.log X) ^ A)) := by
  have hBV := weighted_bombieri_vinogradov theta hTheta A hA
  let C := Classical.choose hBV
  have hData := Classical.choose_spec hBV
  refine Exists.intro C (And.intro hData.1 ?_)
  intro X hX branches a y hValid hy hRange
  exact (ownerBranchErrors_le_average branches a y hValid hy hRange).trans (hData.2 hX)

end RobinBV.Sieve
