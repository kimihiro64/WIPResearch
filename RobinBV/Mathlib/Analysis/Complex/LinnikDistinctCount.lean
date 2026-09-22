/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LinnikDistinctFourier

/-!
# Orthogonality count for Linnik's distinct-prefix branch

This module identifies the left side of the distinct-prefix Holder inequality
with an exact finite equal-frequency pair count. Prefix tuples are restricted
to distinct residue classes, while the remaining coordinates are unrestricted.
-/

set_option autoImplicit false

namespace Finset

/-- Frequency contributed by an unrestricted tail tuple. -/
noncomputable def linnikTailFrequency
    (k r X L : Nat) (u : Fin L -> Fin X) : Nat :=
  Finset.univ.sum (fun i : Fin L =>
    linnikMomentAtomFrequency k r X (u i))

/-- The Fourier sum over all length-`L` tails factors as the `L`-th power
of the atom sum. -/
theorem linnikTailFourierSum_eq_pow
    (k r X L : Nat) (t : AddCircle (1 : Real)) :
    (Finset.univ : Finset (Fin L -> Fin X)).sum (fun u =>
        fourier (linnikTailFrequency k r X L u : Int) t) =
      linnikMomentAtomFourierSum k r X t ^ L := by
  calc
    _ = Finset.univ.sum (fun u : Fin L -> Fin X =>
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
    _ = linnikMomentAtomFourierSum k r X t ^ L := by
      unfold linnikMomentAtomFourierSum
      exact (Fintype.sum_pow (fun x : Fin X =>
        fourier (linnikMomentAtomFrequency k r X x : Int) t) L).symm

/-- Prefix/tail packet whose prefix is distinct modulo `p`. -/
noncomputable def linnikModDistinctPacket
    (p k X L : Nat) (hp : 0 < p) :
    Finset (Prod (Fin k -> Fin X) (Fin L -> Fin X)) :=
  (linnikModDistinctPrefixTuples p k X hp).product Finset.univ

/-- Combined frequency of a distinct prefix and unrestricted tail. -/
noncomputable def linnikModDistinctPacketFrequency
    (k r X L : Nat)
    (vu : Prod (Fin k -> Fin X) (Fin L -> Fin X)) : Nat :=
  linnikPrefixFrequency k r X vu.fst +
    linnikTailFrequency k r X L vu.snd

/-- The packet Fourier sum factors into the distinct-prefix amplitude and
the unrestricted tail power. -/
theorem linnikModDistinctPacketFourierSum_eq
    (p k r X L : Nat) (hp : 0 < p)
    (t : AddCircle (1 : Real)) :
    (linnikModDistinctPacket p k X L hp).sum (fun vu =>
        fourier (linnikModDistinctPacketFrequency k r X L vu : Int) t) =
      linnikModDistinctPrefixFourierSum p k r X hp t *
        linnikMomentAtomFourierSum k r X t ^ L := by
  unfold linnikModDistinctPacket linnikModDistinctPacketFrequency
  rw [Finset.product_eq_sprod, Finset.sum_product]
  simp_rw [Nat.cast_add, fourier_add]
  rw [show (fun v : Fin k -> Fin X =>
      Finset.univ.sum (fun u : Fin L -> Fin X =>
        fourier (linnikPrefixFrequency k r X v : Int) t *
          fourier (linnikTailFrequency k r X L u : Int) t)) =
      (fun v : Fin k -> Fin X =>
        fourier (linnikPrefixFrequency k r X v : Int) t *
          Finset.univ.sum (fun u : Fin L -> Fin X =>
            fourier (linnikTailFrequency k r X L u : Int) t)) by
    funext v
    rw [Finset.mul_sum]]
  rw [linnikTailFourierSum_eq_pow]
  rw [<- Finset.sum_mul]
  rfl

/-- Exact equal-frequency pair count for the distinct-prefix packet. -/
noncomputable def linnikModDistinctPacketPairCount
    (p k r X L : Nat) (hp : 0 < p) : Real :=
  AddCircle.integerPairCount
    (linnikModDistinctPacket p k X L hp)
    (fun vu => (linnikModDistinctPacketFrequency k r X L vu : Int)) 0

/-- Orthogonality identifies the distinct-prefix packet count with the
mixed Fourier moment used on the left side of Holder. -/
theorem integral_linnikModDistinctPacket_eq_pairCount
    (p k r X L : Nat) (hp : 0 < p) :
    MeasureTheory.integral AddCircle.haarAddCircle
        (fun t : AddCircle (1 : Real) =>
          norm (linnikModDistinctPrefixFourierSum p k r X hp t) ^ 2 *
            norm (linnikMomentAtomFourierSum k r X t) ^ (2 * L)) =
      linnikModDistinctPacketPairCount p k r X L hp := by
  have h := AddCircle.integerPairCount_zero_integral
    (linnikModDistinctPacket p k X L hp)
    (fun vu => (linnikModDistinctPacketFrequency k r X L vu : Int))
  simp_rw [linnikModDistinctPacketFourierSum_eq p k r X L hp] at h
  simp_rw [norm_mul, norm_pow, mul_pow] at h
  unfold linnikModDistinctPacketPairCount
  simpa only [pow_mul'] using h

/-- The exact distinct-prefix pair count is bounded by one residue-class
Fourier moment, with the source coefficient `p^(2*L)`. -/
theorem exists_residue_linnikModDistinctPacketPairCount_le
    (p k r X L : Nat) (hp : 0 < p) (hL : 0 < L) :
    exists a : Fin p,
      linnikModDistinctPacketPairCount p k r X L hp <=
        (p : Real) ^ (2 * L) *
          MeasureTheory.integral AddCircle.haarAddCircle
            (fun t : AddCircle (1 : Real) =>
              norm (linnikModDistinctPrefixFourierSum p k r X hp t) ^ 2 *
                norm
                  (linnikResidueAtomFourierSum p k r X hp a t) ^ (2 * L)) := by
  have hq : 0 < 2 * L := Nat.mul_pos (by omega) hL
  have hholder := exists_residue_integral_linnikDistinctPrefixHolder
    p k r X (2 * L) hp hq
  choose a ha using hholder
  refine Exists.intro a ?_
  rw [<- integral_linnikModDistinctPacket_eq_pairCount p k r X L hp]
  exact ha

end Finset
