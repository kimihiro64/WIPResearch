/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LinnikDistinct

/-!
# Residue-class Holder step for Linnik's distinct branch

This module formalizes the exact residue decomposition and pointwise Holder
inequality used to pass from the unrestricted atom sum to one distinguished
residue-class moment in Linnik's distinct-prefix argument.
-/

set_option autoImplicit false

namespace Finset

/-- The residue modulo a positive modulus of the interval value `x+1`. -/
def linnikResidueIndex (p X : Nat) (hp : 0 < p) (x : Fin X) : Fin p :=
  Fin.mk ((x.val + 1) % p) (Nat.mod_lt _ hp)

/-- The one-coordinate Fourier sum restricted to one residue class modulo
`p`. -/
noncomputable def linnikResidueAtomFourierSum
    (p k r X : Nat) (hp : 0 < p) (a : Fin p)
    (t : AddCircle (1 : Real)) : Complex :=
  ((Finset.univ : Finset (Fin X)).filter
      (fun x => linnikResidueIndex p X hp x = a)).sum
    (fun x => fourier (linnikMomentAtomFrequency k r X x : Int) t)

/-- Summing the residue-restricted atom sums recovers the unrestricted atom
sum exactly. -/
theorem sum_linnikResidueAtomFourierSum
    (p k r X : Nat) (hp : 0 < p) (t : AddCircle (1 : Real)) :
    Finset.univ.sum (fun a : Fin p =>
      linnikResidueAtomFourierSum p k r X hp a t) =
      linnikMomentAtomFourierSum k r X t := by
  classical
  let A : Finset (Fin X) := Finset.univ
  let g := linnikResidueIndex p X hp
  let f : Fin X -> Complex := fun x =>
    fourier (linnikMomentAtomFrequency k r X x : Int) t
  have h := Finset.sum_fiberwise A g f
  simpa only [A, g, f, linnikResidueAtomFourierSum,
    linnikMomentAtomFourierSum] using h

/-- Finite Holder/Jensen in the exact form needed for the residue sum. -/
theorem norm_sum_pow_le_card_pow_mul_sum_norm_pow
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I -> Complex) (q : Nat) (hq : 0 < q) :
    norm (Finset.univ.sum f) ^ q <=
      Fintype.card I ^ (q - 1) *
        Finset.univ.sum (fun i => norm (f i) ^ q) := by
  have hnorm : norm (Finset.univ.sum f) <=
      Finset.univ.sum (fun i => norm (f i)) := norm_sum_le _ _
  have hqeq : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq))
  calc
    norm (Finset.univ.sum f) ^ q <=
        (Finset.univ.sum (fun i => norm (f i))) ^ q := by
      gcongr
    _ <= (Finset.univ.card : Real) ^ (q - 1) *
        Finset.univ.sum (fun i => norm (f i) ^ q) := by
      simpa only [hqeq] using
        (pow_sum_le_card_mul_sum_pow
          (s := (Finset.univ : Finset I))
          (f := fun i => norm (f i))
          (fun i hi => norm_nonneg (f i)) (q - 1))
    _ = Fintype.card I ^ (q - 1) *
        Finset.univ.sum (fun i => norm (f i) ^ q) := by simp

/-- Weighted pointwise form of the residue Holder step. -/
theorem mul_norm_sum_pow_le_card_pow_mul_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I -> Complex) (q : Nat) (hq : 0 < q)
    (A : Real) (hA : 0 <= A) :
    A * norm (Finset.univ.sum f) ^ q <=
      Fintype.card I ^ (q - 1) *
        Finset.univ.sum (fun i => A * norm (f i) ^ q) := by
  calc
    A * norm (Finset.univ.sum f) ^ q <=
        A * (Fintype.card I ^ (q - 1) *
          Finset.univ.sum (fun i => norm (f i) ^ q)) := by
      exact mul_le_mul_of_nonneg_left
        (norm_sum_pow_le_card_pow_mul_sum_norm_pow f q hq) hA
    _ = Fintype.card I ^ (q - 1) *
        Finset.univ.sum (fun i => A * norm (f i) ^ q) := by
      let C : Real := Fintype.card I ^ (q - 1)
      calc
        A * (C * Finset.univ.sum (fun i => norm (f i) ^ q)) =
            (A * C) * Finset.univ.sum (fun i => norm (f i) ^ q) := by ring
        _ = Finset.univ.sum (fun i => (A * C) * norm (f i) ^ q) := by
          rw [Finset.mul_sum]
        _ = Finset.univ.sum (fun i => C * (A * norm (f i) ^ q)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = C * Finset.univ.sum (fun i => A * norm (f i) ^ q) := by
          rw [Finset.mul_sum]

/-- The source residue-class Holder inequality, with the exact modulus
coefficient and the unrestricted atom sum substituted. -/
theorem linnikResidueAtomHolder
    (p k r X q : Nat) (hp : 0 < p) (hq : 0 < q)
    (t : AddCircle (1 : Real)) (A : Real) (hA : 0 <= A) :
    A * norm (linnikMomentAtomFourierSum k r X t) ^ q <=
      p ^ (q - 1) *
        Finset.univ.sum (fun a : Fin p =>
          A * norm (linnikResidueAtomFourierSum p k r X hp a t) ^ q) := by
  rw [<- sum_linnikResidueAtomFourierSum p k r X hp t]
  simpa using mul_norm_sum_pow_le_card_pow_mul_sum
    (fun a : Fin p => linnikResidueAtomFourierSum p k r X hp a t)
    q hq A hA

/-- Integrated residue-class Holder inequality on the additive circle. This
is the exact analytic step that changes the unrestricted power into a sum of
one-residue moments. -/
theorem integral_linnikResidueAtomHolder
    (p k r X q : Nat) (hp : 0 < p) (hq : 0 < q)
    (P : AddCircle (1 : Real) -> Real) (hP : Continuous P)
    (hPnonneg : forall t, 0 <= P t) :
    MeasureTheory.integral AddCircle.haarAddCircle
        (fun t : AddCircle (1 : Real) =>
          P t * norm (linnikMomentAtomFourierSum k r X t) ^ q) <=
      p ^ (q - 1) * Finset.univ.sum (fun a : Fin p =>
        MeasureTheory.integral AddCircle.haarAddCircle
          (fun t : AddCircle (1 : Real) =>
            P t * norm
              (linnikResidueAtomFourierSum p k r X hp a t) ^ q)) := by
  have hS : Continuous (linnikMomentAtomFourierSum k r X) := by
    unfold linnikMomentAtomFourierSum
    exact AddCircle.finite_fourier_continuous
      (Finset.univ : Finset (Fin X))
      (fun x => (linnikMomentAtomFrequency k r X x : Int))
  have hG (a : Fin p) :
      Continuous (linnikResidueAtomFourierSum p k r X hp a) := by
    unfold linnikResidueAtomFourierSum
    exact AddCircle.finite_fourier_continuous
      ((Finset.univ : Finset (Fin X)).filter
        (fun x => linnikResidueIndex p X hp x = a))
      (fun x => (linnikMomentAtomFrequency k r X x : Int))
  have hleft : MeasureTheory.Integrable
      (fun t : AddCircle (1 : Real) =>
        P t * norm (linnikMomentAtomFourierSum k r X t) ^ q)
      AddCircle.haarAddCircle :=
    (hP.mul (hS.norm.pow q)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hterm (a : Fin p) : MeasureTheory.Integrable
      (fun t : AddCircle (1 : Real) =>
        P t * norm (linnikResidueAtomFourierSum p k r X hp a t) ^ q)
      AddCircle.haarAddCircle :=
    (hP.mul ((hG a).norm.pow q)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum : MeasureTheory.Integrable
      (fun t : AddCircle (1 : Real) =>
        Finset.univ.sum (fun a : Fin p =>
          P t * norm
            (linnikResidueAtomFourierSum p k r X hp a t) ^ q))
      AddCircle.haarAddCircle :=
    MeasureTheory.integrable_finset_sum Finset.univ (fun a ha => hterm a)
  have hright : MeasureTheory.Integrable
      (fun t : AddCircle (1 : Real) =>
        (p ^ (q - 1) : Real) * Finset.univ.sum (fun a : Fin p =>
          P t * norm
            (linnikResidueAtomFourierSum p k r X hp a t) ^ q))
      AddCircle.haarAddCircle := hsum.const_mul _
  have hmono := MeasureTheory.integral_mono hleft hright
    (fun t =>
      linnikResidueAtomHolder p k r X q hp hq t (P t) (hPnonneg t))
  calc
    MeasureTheory.integral AddCircle.haarAddCircle
        (fun t : AddCircle (1 : Real) =>
          P t * norm (linnikMomentAtomFourierSum k r X t) ^ q) <=
        MeasureTheory.integral AddCircle.haarAddCircle
          (fun t : AddCircle (1 : Real) =>
            (p ^ (q - 1) : Real) * Finset.univ.sum (fun a : Fin p =>
              P t * norm
                (linnikResidueAtomFourierSum p k r X hp a t) ^ q)) := hmono
    _ = p ^ (q - 1) * MeasureTheory.integral AddCircle.haarAddCircle
        (fun t : AddCircle (1 : Real) => Finset.univ.sum (fun a : Fin p =>
          P t * norm
            (linnikResidueAtomFourierSum p k r X hp a t) ^ q)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = p ^ (q - 1) * Finset.univ.sum (fun a : Fin p =>
        MeasureTheory.integral AddCircle.haarAddCircle
          (fun t : AddCircle (1 : Real) =>
            P t * norm
              (linnikResidueAtomFourierSum p k r X hp a t) ^ q)) := by
      rw [MeasureTheory.integral_finset_sum Finset.univ
        (fun a ha => hterm a)]

/-- After integration, one residue class attains the complete Holder bound.
This is the source inequality `I(p) <= p^q max_a I1(p,a)` with the maximizing
residue exhibited rather than hidden in a maximum. -/
theorem exists_residue_integral_linnikResidueAtomHolder
    (p k r X q : Nat) (hp : 0 < p) (hq : 0 < q)
    (P : AddCircle (1 : Real) -> Real) (hP : Continuous P)
    (hPnonneg : forall t, 0 <= P t) :
    exists a : Fin p,
      MeasureTheory.integral AddCircle.haarAddCircle
          (fun t : AddCircle (1 : Real) =>
            P t * norm (linnikMomentAtomFourierSum k r X t) ^ q) <=
        (p : Real) ^ q *
          MeasureTheory.integral AddCircle.haarAddCircle
            (fun t : AddCircle (1 : Real) =>
              P t * norm
                (linnikResidueAtomFourierSum p k r X hp a t) ^ q) := by
  let I : Fin p -> Real := fun a =>
    MeasureTheory.integral AddCircle.haarAddCircle
      (fun t : AddCircle (1 : Real) =>
        P t * norm
          (linnikResidueAtomFourierSum p k r X hp a t) ^ q)
  have huniv : (Finset.univ : Finset (Fin p)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr (Nonempty.intro (Fin.mk 0 hp))
  obtain ha : exists a : Fin p, forall b : Fin p, I b <= I a := by
    have hmax := Finset.exists_max_image
      (Finset.univ : Finset (Fin p)) I huniv
    choose a haMem haMax using hmax
    exact Exists.intro a (fun b => haMax b (Finset.mem_univ b))
  choose a ha using ha
  refine Exists.intro a ?_
  have hsum : Finset.univ.sum I <= p * I a := by
    calc
      Finset.univ.sum I <= Finset.univ.sum (fun _b : Fin p => I a) := by
        apply Finset.sum_le_sum
        intro b hb
        exact ha b
      _ = p * I a := by simp
  have hpq : (p : Real) ^ q =
      (p : Real) ^ (q - 1) * (p : Real) := by
    calc
      (p : Real) ^ q = (p : Real) ^ ((q - 1) + 1) := by
        congr 1
        omega
      _ = (p : Real) ^ (q - 1) * (p : Real) := by rw [pow_succ]
  calc
    MeasureTheory.integral AddCircle.haarAddCircle
        (fun t : AddCircle (1 : Real) =>
          P t * norm (linnikMomentAtomFourierSum k r X t) ^ q) <=
        (p : Real) ^ (q - 1) * Finset.univ.sum I := by
      exact integral_linnikResidueAtomHolder p k r X q hp hq P hP hPnonneg
    _ <= (p : Real) ^ (q - 1) * (p * I a) := by
      gcongr
    _ = (p : Real) ^ q * I a := by
      rw [hpq]
      ring

end Finset
