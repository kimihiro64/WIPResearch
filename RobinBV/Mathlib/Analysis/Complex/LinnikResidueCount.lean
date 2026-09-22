/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LinnikDistinctCount

/-!
# Residue-tail orthogonality count in Linnik's distinct branch

This module identifies the right-hand residue moment in the distinct-prefix
Holder inequality with an exact finite pair count. Together with
`LinnikDistinctCount`, this removes both Fourier integrals from the
`I(p) <= p^(2L) I1(p,a)` step.
-/

set_option autoImplicit false

namespace Finset

/-- Length-`L` tails all of whose coordinates lie in one residue class. -/
noncomputable def linnikResidueTailTuples
    (p X L : Nat) (hp : 0 < p) (a : Fin p) :
    Finset (Fin L -> Fin X) :=
  Fintype.piFinset (fun _i : Fin L =>
    (Finset.univ : Finset (Fin X)).filter
      (fun x => linnikResidueIndex p X hp x = a))

/-- The Fourier sum over one-residue tails is the corresponding atom sum
raised to the tail length. -/
theorem linnikResidueTailFourierSum_eq_pow
    (p k r X L : Nat) (hp : 0 < p) (a : Fin p)
    (t : AddCircle (1 : Real)) :
    (linnikResidueTailTuples p X L hp a).sum (fun u =>
        fourier (linnikTailFrequency k r X L u : Int) t) =
      linnikResidueAtomFourierSum p k r X hp a t ^ L := by
  calc
    _ = (linnikResidueTailTuples p X L hp a).sum (fun u =>
        Finset.univ.prod (fun i => fourier
          (linnikMomentAtomFrequency k r X (u i) : Int) t)) := by
      apply Finset.sum_congr rfl
      intro u hu
      symm
      unfold linnikTailFrequency
      induction (Finset.univ : Finset (Fin L)) using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi]
          push_cast at ih
          push_cast
          rw [fourier_add, ih]
    _ = Finset.univ.prod (fun _i : Fin L =>
        linnikResidueAtomFourierSum p k r X hp a t) := by
      unfold linnikResidueTailTuples linnikResidueAtomFourierSum
      exact Finset.sum_prod_piFinset
        ((Finset.univ : Finset (Fin X)).filter
          (fun x => linnikResidueIndex p X hp x = a))
        (fun _i x => fourier
          (linnikMomentAtomFrequency k r X x : Int) t)
    _ = linnikResidueAtomFourierSum p k r X hp a t ^ L := by simp

/-- Prefix/residue-tail packet used by `I1(p,a)`. -/
noncomputable def linnikResiduePacket
    (p k X L : Nat) (hp : 0 < p) (a : Fin p) :
    Finset (Prod (Fin k -> Fin X) (Fin L -> Fin X)) :=
  (linnikModDistinctPrefixTuples p k X hp).product
    (linnikResidueTailTuples p X L hp a)

/-- Fourier factorization of the `I1(p,a)` packet. -/
theorem linnikResiduePacketFourierSum_eq
    (p k r X L : Nat) (hp : 0 < p) (a : Fin p)
    (t : AddCircle (1 : Real)) :
    (linnikResiduePacket p k X L hp a).sum (fun vu =>
        fourier (linnikModDistinctPacketFrequency k r X L vu : Int) t) =
      linnikModDistinctPrefixFourierSum p k r X hp t *
        linnikResidueAtomFourierSum p k r X hp a t ^ L := by
  unfold linnikResiduePacket linnikModDistinctPacketFrequency
  rw [Finset.product_eq_sprod, Finset.sum_product]
  simp_rw [Nat.cast_add, fourier_add]
  rw [show (fun v : Fin k -> Fin X =>
      (linnikResidueTailTuples p X L hp a).sum (fun u =>
        fourier (linnikPrefixFrequency k r X v : Int) t *
          fourier (linnikTailFrequency k r X L u : Int) t)) =
      (fun v : Fin k -> Fin X =>
        fourier (linnikPrefixFrequency k r X v : Int) t *
          (linnikResidueTailTuples p X L hp a).sum (fun u =>
            fourier (linnikTailFrequency k r X L u : Int) t)) by
    funext v
    rw [Finset.mul_sum]]
  rw [linnikResidueTailFourierSum_eq_pow]
  rw [<- Finset.sum_mul]
  rfl

/-- Exact equal-frequency pair count for `I1(p,a)`. -/
noncomputable def linnikResiduePacketPairCount
    (p k r X L : Nat) (hp : 0 < p) (a : Fin p) : Real :=
  AddCircle.integerPairCount
    (linnikResiduePacket p k X L hp a)
    (fun vu => (linnikModDistinctPacketFrequency k r X L vu : Int)) 0

/-- Orthogonality identifies the residue moment with the `I1(p,a)` packet
pair count. -/
theorem integral_linnikResiduePacket_eq_pairCount
    (p k r X L : Nat) (hp : 0 < p) (a : Fin p) :
    MeasureTheory.integral AddCircle.haarAddCircle
        (fun t : AddCircle (1 : Real) =>
          norm (linnikModDistinctPrefixFourierSum p k r X hp t) ^ 2 *
            norm (linnikResidueAtomFourierSum p k r X hp a t) ^ (2 * L)) =
      linnikResiduePacketPairCount p k r X L hp a := by
  have h := AddCircle.integerPairCount_zero_integral
    (linnikResiduePacket p k X L hp a)
    (fun vu => (linnikModDistinctPacketFrequency k r X L vu : Int))
  simp_rw [linnikResiduePacketFourierSum_eq p k r X L hp a] at h
  simp_rw [norm_mul, norm_pow, mul_pow] at h
  unfold linnikResiduePacketPairCount
  simpa only [pow_mul'] using h

/-- Fully discrete form of the residue Holder step. -/
theorem exists_residue_linnikModDistinctPairCount_le_residuePairCount
    (p k r X L : Nat) (hp : 0 < p) (hL : 0 < L) :
    exists a : Fin p,
      linnikModDistinctPacketPairCount p k r X L hp <=
        (p : Real) ^ (2 * L) *
          linnikResiduePacketPairCount p k r X L hp a := by
  have h := exists_residue_linnikModDistinctPacketPairCount_le
    p k r X L hp hL
  choose a ha using h
  refine Exists.intro a ?_
  rw [<- integral_linnikResiduePacket_eq_pairCount p k r X L hp a]
  exact ha

end Finset
