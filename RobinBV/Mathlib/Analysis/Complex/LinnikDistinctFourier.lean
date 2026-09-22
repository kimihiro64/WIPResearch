/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LinnikResidueHolder

/-!
# Fourier amplitude for Linnik's distinct-prefix tuples

This module defines the exact distinct-prefix exponential sum and substitutes
its squared norm into the integrated residue-class Holder theorem. The result
is the source inequality from the fixed-prime count `I(p)` to one residue
moment `I1(p,a)`, pending only the two orthogonality identifications with
their finite tuple counts.
-/

set_option autoImplicit false

namespace Finset

/-- Prefix tuples whose interval values occupy pairwise distinct residue
classes modulo `p`. -/
noncomputable def linnikModDistinctPrefixTuples
    (p k X : Nat) (hp : 0 < p) : Finset (Fin k -> Fin X) :=
  (Finset.univ : Finset (Fin k -> Fin X)).filter (fun v =>
    Function.Injective (fun i : Fin k => linnikResidueIndex p X hp (v i)))

/-- The lossless integer frequency of one length-`k` prefix tuple. -/
noncomputable def linnikPrefixFrequency
    (k r X : Nat) (v : Fin k -> Fin X) : Nat :=
  Finset.univ.sum (fun i : Fin k =>
    linnikMomentAtomFrequency k r X (v i))

/-- Fourier amplitude of all prefix tuples that are distinct modulo `p`. -/
noncomputable def linnikModDistinctPrefixFourierSum
    (p k r X : Nat) (hp : 0 < p)
    (t : AddCircle (1 : Real)) : Complex :=
  (linnikModDistinctPrefixTuples p k X hp).sum (fun v =>
    fourier (linnikPrefixFrequency k r X v : Int) t)

/-- The distinct-prefix Fourier amplitude is continuous. -/
theorem continuous_linnikModDistinctPrefixFourierSum
    (p k r X : Nat) (hp : 0 < p) :
    Continuous (linnikModDistinctPrefixFourierSum p k r X hp) := by
  unfold linnikModDistinctPrefixFourierSum
  exact AddCircle.finite_fourier_continuous
    (linnikModDistinctPrefixTuples p k X hp)
    (fun v => (linnikPrefixFrequency k r X v : Int))

/-- The integrated Holder step with the exact squared distinct-prefix
amplitude substituted. -/
theorem exists_residue_integral_linnikDistinctPrefixHolder
    (p k r X q : Nat) (hp : 0 < p) (hq : 0 < q) :
    exists a : Fin p,
      MeasureTheory.integral AddCircle.haarAddCircle
          (fun t : AddCircle (1 : Real) =>
            norm (linnikModDistinctPrefixFourierSum p k r X hp t) ^ 2 *
              norm (linnikMomentAtomFourierSum k r X t) ^ q) <=
        (p : Real) ^ q *
          MeasureTheory.integral AddCircle.haarAddCircle
            (fun t : AddCircle (1 : Real) =>
              norm (linnikModDistinctPrefixFourierSum p k r X hp t) ^ 2 *
                norm
                  (linnikResidueAtomFourierSum p k r X hp a t) ^ q) := by
  let P : AddCircle (1 : Real) -> Real := fun t =>
    norm (linnikModDistinctPrefixFourierSum p k r X hp t) ^ 2
  have hP : Continuous P :=
    (continuous_linnikModDistinctPrefixFourierSum p k r X hp).norm.pow 2
  have hPnonneg : forall t, 0 <= P t := fun t => sq_nonneg _
  exact exists_residue_integral_linnikResidueAtomHolder
    p k r X q hp hq P hP hPnonneg

end Finset
