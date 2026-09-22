/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.MeanInequalities
import RobinBV.Mathlib.Analysis.Complex.FiniteMellinMoment

/-!
# Indexed integer energy and color comparison

Every original index is retained, including coincident integer frequencies and
all multiplicities. The finite color inequality is the discrete consumer used
by the reflection near-energy estimate in the almost-all zero-moment chain.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

namespace AddCircle

noncomputable def integerPairCount {I : Type*} (A : Finset I)
    (q : I -> Int) (k : Int) : Real := by
  classical
  exact A.sum (fun i => A.sum (fun j => if q i-q j = k then 1 else 0))

noncomputable def integerEnergy {I : Type*} (A : Finset I)
    (q : I -> Int) : Real :=
  integerPairCount (SProd.sprod A A : Finset (Prod I I))
    (fun p => q p.1+q p.2) 0

theorem integerPairCount_nonneg {I : Type*} (A : Finset I)
    (q : I -> Int) (k : Int) : 0 <= integerPairCount A q k := by
  classical
  unfold integerPairCount
  exact Finset.sum_nonneg (fun i hi =>
    Finset.sum_nonneg (fun j hj => by split_ifs <;> norm_num))

theorem integral_fourier_unit (k : Int) :
    MeasureTheory.integral haarAddCircle (@fourier 1 k) =
      (if k = 0 then 1 else 0 : Complex) := by
  change MeasureTheory.integral haarAddCircle (fun t : AddCircle 1 => fourier k t) = _
  have h := congrFun (fourierCoeff_fourier (T := 1) k) 0
  simpa [fourierCoeff, fourier_zero, Pi.single_apply, eq_comm] using h

theorem finite_fourier_continuous {I : Type*} (A : Finset I) (q : I -> Int) :
    Continuous (fun x : AddCircle 1 => A.sum (fun i => fourier (q i) x)) :=
  continuous_finsetSum A (fun i hi => (fourier (q i)).continuous)

theorem finite_fourier_integrable {I : Type*} (A : Finset I) (q : I -> Int) :
    Integrable (fun x : AddCircle 1 => A.sum (fun i => fourier (q i) x))
      haarAddCircle :=
  (finite_fourier_continuous A q).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integerPairCount_fourier {I : Type*} (A : Finset I) (q : I -> Int)
    (k : Int) :
    MeasureTheory.integral haarAddCircle (fun x : AddCircle 1 =>
      fourier (-k) x * ((norm (A.sum (fun i => fourier (q i) x))^2 : Real) : Complex)) =
      (integerPairCount A q k : Complex) := by
  classical
  have hpoint (x : AddCircle 1) :
      fourier (-k) x * ((norm (A.sum (fun i => fourier (q i) x))^2 : Real) : Complex) =
      A.sum (fun i => A.sum (fun j => fourier (q i-q j-k) x)) := by
    have h := Complex.finite_mellin_norm_sq_expansion A
      (fun i => fourier (q i) x) (fun _ => 0) 0
    simp only [Complex.ofReal_zero, map_zero, zero_add, zero_mul,
      Complex.exp_zero, mul_one] at h
    rw [h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [<- fourier_neg, <- fourier_add, <- fourier_add]
    rw [show -k+(q i + -q j) = q i-q j-k by omega]
  calc
    _ = MeasureTheory.integral haarAddCircle (fun x : AddCircle 1 =>
        A.sum (fun i => A.sum (fun j => fourier (q i-q j-k) x))) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = A.sum (fun i => A.sum (fun j =>
        MeasureTheory.integral haarAddCircle (@fourier 1 (q i-q j-k)))) := by
      rw [integral_finset_sum A (fun i hi =>
        finite_fourier_integrable A (fun j => q i-q j-k))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finset_sum A (fun j hj =>
        (fourier (T := 1) (q i-q j-k)).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
    _ = (integerPairCount A q k : Complex) := by
      simp only [integral_fourier_unit, sub_eq_zero, integerPairCount]
      norm_cast

theorem integerPairCount_zero_integral {I : Type*} (A : Finset I)
    (q : I -> Int) :
    MeasureTheory.integral haarAddCircle (fun x : AddCircle 1 =>
      norm (A.sum (fun i => fourier (q i) x))^2) = integerPairCount A q 0 := by
  have h := integerPairCount_fourier A q 0
  simp only [neg_zero, fourier_zero, one_mul, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem integerPairCount_le_zero {I : Type*} (A : Finset I)
    (q : I -> Int) (k : Int) :
    integerPairCount A q k <= integerPairCount A q 0 := by
  have h : norm (MeasureTheory.integral haarAddCircle (fun x : AddCircle 1 =>
      fourier (-k) x * ((norm (A.sum (fun i => fourier (q i) x))^2 : Real) : Complex))) <=
      MeasureTheory.integral haarAddCircle (fun x : AddCircle 1 =>
        norm (fourier (-k) x *
          ((norm (A.sum (fun i => fourier (q i) x))^2 : Real) : Complex))) :=
    norm_integral_le_integral_norm _
  rw [integerPairCount_fourier] at h
  have hn (x : AddCircle 1) :
      norm (fourier (-k) x *
        ((norm (A.sum (fun i => fourier (q i) x))^2 : Real) : Complex)) =
      norm (A.sum (fun i => fourier (q i) x))^2 := by
    rw [norm_mul, fourier_apply, Circle.norm_coe, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integerPairCount_nonneg A q k)] at h
  rwa [integerPairCount_zero_integral] at h

theorem integerEnergy_fourth_integral {I : Type*} (A : Finset I)
    (q : I -> Int) :
    MeasureTheory.integral haarAddCircle (fun x : AddCircle 1 =>
      norm (A.sum (fun i => fourier (q i) x))^4) = integerEnergy A q := by
  have h := integerPairCount_zero_integral
    (SProd.sprod A A : Finset (Prod I I)) (fun p => q p.1+q p.2)
  have hp (x : AddCircle 1) :
      (SProd.sprod A A : Finset (Prod I I)).sum
        (fun p => fourier (q p.1+q p.2) x) =
      (A.sum (fun i => fourier (q i) x))^2 := by
    simp only [Finset.sum_product, fourier_add, pow_two, Finset.sum_mul_sum]
  simp only [hp, norm_pow, <- pow_mul] at h
  exact h

theorem norm_finset_sum_fourth_le {I : Type*} (A : Finset I) (f : I -> Complex) :
    norm (A.sum f)^4 <= (A.card : Real)^3 * A.sum (fun i => norm (f i)^4) := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := A) (f := fun i => norm (f i)) (p := 4) (by norm_num)
    (fun i hi => norm_nonneg _)
  have h4 (x : Real) : x^(4 : Real) = x^(4 : Nat) := Real.rpow_natCast x 4
  have h3 (x : Real) : x^(3 : Real) = x^(3 : Nat) := Real.rpow_natCast x 3
  simp only [show (4 : Real)-1 = 3 by norm_num, h4, h3] at h
  have hn := Real.rpow_le_rpow (norm_nonneg _) (norm_sum_le A f)
    (by norm_num : (0 : Real) <= 4)
  simp only [h4] at hn
  exact hn.trans h

theorem integerEnergy_color_le {I J : Type*} [DecidableEq J] (A : Finset I) (C : Finset J)
    (q : I -> Int) (color : I -> J)
    (hc : forall i, Membership.mem A i -> Membership.mem C (color i)) :
    integerEnergy A q <= (C.card : Real)^3 *
      C.sum (fun c => integerEnergy (A.filter (fun i => color i = c)) q) := by
  classical
  have hcont (B : Finset I) :
      Continuous (fun x : AddCircle 1 => norm (B.sum (fun i => fourier (q i) x))^4) :=
    (finite_fourier_continuous B q).norm.pow 4
  have hint (B : Finset I) :
      Integrable (fun x : AddCircle 1 => norm (B.sum (fun i => fourier (q i) x))^4)
        haarAddCircle :=
    (hcont B).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (x : AddCircle 1) :
      norm (A.sum (fun i => fourier (q i) x))^4 <=
        (C.card : Real)^3 * C.sum (fun c =>
          norm ((A.filter (fun i => color i = c)).sum
            (fun i => fourier (q i) x))^4) := by
    have he := Finset.sum_fiberwise_of_maps_to (s := A) (t := C)
      (g := color) hc (fun i => fourier (q i) x)
    rw [<- he]
    exact norm_finset_sum_fourth_le C _
  have hsumCont : Continuous (fun x : AddCircle 1 =>
      (C.card : Real)^3 * C.sum (fun c =>
        norm ((A.filter (fun i => color i = c)).sum
          (fun i => fourier (q i) x))^4)) :=
    continuous_const.mul (continuous_finsetSum C
      (fun c hcc => hcont (A.filter (fun i => color i = c))))
  have hi := integral_mono (hint A)
    (hsumCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hpoint
  rw [integerEnergy_fourth_integral, integral_const_mul,
    integral_finset_sum C (fun c hcc => hint (A.filter (fun i => color i = c)))] at hi
  simpa only [integerEnergy_fourth_integral] using hi

end AddCircle
