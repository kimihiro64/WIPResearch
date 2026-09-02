/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
module

public import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaSplitting

/-!
# Prime-power ideal-counting coefficients in quadratic fields

This file counts the exponent vectors in each quadratic splitting case
and proves the exact geometric-sum formula for every prime-power
Dedekind-zeta coefficient.
-/

@[expose] public section

namespace NumberField.OddFundamentalDiscriminant

noncomputable section

open UniqueFactorizationMonoid

theorem natCard_pair_sum_eq (k : Nat) :
    Nat.card {x : Prod Nat Nat // x.1 + x.2 = k} = k + 1 := by
  letI : Fintype {x : Prod Nat Nat // x.1 + x.2 = k} :=
    Fintype.ofFinset (Finset.antidiagonal k) (fun x => by
      rw [Finset.mem_antidiagonal]
      rfl)
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card {x : Prod Nat Nat // x.1 + x.2 = k} =
        (Finset.antidiagonal k).card := by
      apply Fintype.card_of_subtype
      intro x
      simp [Finset.mem_antidiagonal]
    _ = k + 1 := Finset.Nat.card_antidiagonal k

theorem split_exponentVectors_card
    (D : OddFundamentalDiscriminant) (p k : Nat) [Fact (Nat.Prime p)]
    (hchi : D.character p = 1) :
    Nat.card
      {f : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
        Finset.univ.sum
          (fun P => f P * Ideal.inertiaDeg P.val Int) = k} =
      k + 1 := by
  have hp : Nat.Prime p := Fact.out
  letI := Fintype.ofFinite
    (Ideal.primesOver
      (Ideal.span {(p : Int)})
      (NumberField.RingOfIntegers D.QuadraticField))
  have hSplit := D.split_prime_card_and_inertiaDeg p hp hchi
  have hCardF :
      Fintype.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 2 := by
    simpa only [Nat.card_eq_fintype_card] using hSplit.1
  let eIndex := Fintype.equivFinOfCardEq hCardF
  let eFun :=
    (Equiv.arrowCongr eIndex (Equiv.refl Nat)).trans
      (finTwoArrowEquiv Nat)
  let ePair :
      Equiv
        {f : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
          Finset.univ.sum
            (fun P => f P * Ideal.inertiaDeg P.val Int) = k}
        {x : Prod Nat Nat // x.1 + x.2 = k} :=
    Equiv.mk
      (fun f => Subtype.mk (eFun f.val) (by
        have hWeighted := f.property
        simp_rw [hSplit.2, mul_one] at hWeighted
        calc
          (eFun f.val).1 + (eFun f.val).2 =
              Finset.univ.sum
                (fun i : Fin 2 => f.val (eIndex.symm i)) := by
            simp [eFun, Fin.sum_univ_two]
          _ = Finset.univ.sum f.val := eIndex.symm.sum_comp f.val
          _ = k := hWeighted))
      (fun x => Subtype.mk (eFun.symm x.val) (by
        have hPair := eFun.apply_symm_apply x.val
        change
          ((eFun.symm x.val) (eIndex.symm 0),
            (eFun.symm x.val) (eIndex.symm 1)) = x.val at hPair
        calc
          Finset.univ.sum
              (fun P => (eFun.symm x.val) P *
                Ideal.inertiaDeg P.val Int) =
              Finset.univ.sum (eFun.symm x.val) := by
            apply Finset.sum_congr rfl
            intro P hP
            rw [hSplit.2 P, mul_one]
          _ = Finset.univ.sum
              (fun i : Fin 2 => (eFun.symm x.val) (eIndex.symm i)) :=
            (eIndex.symm.sum_comp (eFun.symm x.val)).symm
          _ = x.val.1 + x.val.2 := by
            rw [Fin.sum_univ_two]
            exact congrArg (fun z : Prod Nat Nat => z.1 + z.2) hPair
          _ = k := x.property))
      (by
        intro f
        apply Subtype.ext
        exact eFun.symm_apply_apply f.val)
      (by
        intro x
        apply Subtype.ext
        exact eFun.apply_symm_apply x.val)
  calc
    Nat.card
        {f : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
          Finset.univ.sum
            (fun P => f P * Ideal.inertiaDeg P.val Int) = k} =
        Nat.card {x : Prod Nat Nat // x.1 + x.2 = k} :=
      Nat.card_congr ePair
    _ = k + 1 := natCard_pair_sum_eq k

theorem ramified_exponentVectors_card
    (D : OddFundamentalDiscriminant) (p k : Nat) [Fact (Nat.Prime p)]
    (hchi : D.character p = 0) :
    Nat.card
      {f : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
        Finset.univ.sum
          (fun P => f P * Ideal.inertiaDeg P.val Int) = k} = 1 := by
  have hp : Nat.Prime p := Fact.out
  letI := Fintype.ofFinite
    (Ideal.primesOver
      (Ideal.span {(p : Int)})
      (NumberField.RingOfIntegers D.QuadraticField))
  have hRamified := D.ramified_prime_card_and_inertiaDeg p hp hchi
  have hCardF :
      Fintype.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 1 := by
    simpa only [Nat.card_eq_fintype_card] using hRamified.1
  letI : Unique
      (Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField)) :=
    Classical.choice
      ((Fintype.card_eq_one_iff_nonempty_unique).mp hCardF)
  let center :
      {f : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
        Finset.univ.sum
          (fun P => f P * Ideal.inertiaDeg P.val Int) = k} :=
    Subtype.mk (fun _ => k) (by
      simp [hRamified.2])
  have hUnique :
      forall f :
        {f : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
          Finset.univ.sum
            (fun P => f P * Ideal.inertiaDeg P.val Int) = k},
        f = center := by
    intro f
    apply Subtype.ext
    funext P
    have hWeighted := f.property
    simp [hRamified.2] at hWeighted
    have hPEq : P = default := Subsingleton.elim _ _
    rw [hPEq]
    exact hWeighted
  letI : Unique
      {f : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
        Finset.univ.sum
          (fun P => f P * Ideal.inertiaDeg P.val Int) = k} := {
    default := center
    uniq := hUnique }
  exact Nat.card_unique

theorem inert_exponentVectors_card
    (D : OddFundamentalDiscriminant) (p k : Nat) [Fact (Nat.Prime p)]
    (hchi : D.character p = -1) :
    Nat.card
      {f : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
        Finset.univ.sum
          (fun P => f P * Ideal.inertiaDeg P.val Int) = k} =
      if Even k then 1 else 0 := by
  have hp : Nat.Prime p := Fact.out
  letI := Fintype.ofFinite
    (Ideal.primesOver
      (Ideal.span {(p : Int)})
      (NumberField.RingOfIntegers D.QuadraticField))
  have hInert := D.inert_prime_card_and_inertiaDeg p hp hchi
  have hCardF :
      Fintype.card
        (Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField)) = 1 := by
    simpa only [Nat.card_eq_fintype_card] using hInert.1
  letI : Unique
      (Ideal.primesOver
        (Ideal.span {(p : Int)})
        (NumberField.RingOfIntegers D.QuadraticField)) :=
    Classical.choice
      ((Fintype.card_eq_one_iff_nonempty_unique).mp hCardF)
  by_cases hk : Even k
  next =>
    have hkCopy := hk
    choose m hm using hkCopy
    let center :
        {f : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
          Finset.univ.sum
            (fun P => f P * Ideal.inertiaDeg P.val Int) = k} :=
      Subtype.mk (fun _ => m) (by
        simp [hInert.2]
        omega)
    have hUnique :
        forall f :
          {f : Ideal.primesOver
              (Ideal.span {(p : Int)})
              (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
            Finset.univ.sum
              (fun P => f P * Ideal.inertiaDeg P.val Int) = k},
          f = center := by
      intro f
      apply Subtype.ext
      funext P
      have hWeighted := f.property
      simp [hInert.2] at hWeighted
      have hPEq : P = default := Subsingleton.elim _ _
      rw [hPEq]
      dsimp only [center]
      omega
    letI : Unique
        {f : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
          Finset.univ.sum
            (fun P => f P * Ideal.inertiaDeg P.val Int) = k} := {
      default := center
      uniq := hUnique }
    rw [if_pos hk]
    exact Nat.card_unique
  next =>
    have hEmpty :
        IsEmpty
          {f : Ideal.primesOver
              (Ideal.span {(p : Int)})
              (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
            Finset.univ.sum
              (fun P => f P * Ideal.inertiaDeg P.val Int) = k} :=
      IsEmpty.mk (fun f => by
        apply hk
        apply Exists.intro (f.val default)
        have hWeighted := f.property
        simp [hInert.2] at hWeighted
        omega)
    letI : IsEmpty
        {f : Ideal.primesOver
            (Ideal.span {(p : Int)})
            (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
          Finset.univ.sum
            (fun P => f P * Ideal.inertiaDeg P.val Int) = k} := hEmpty
    rw [if_neg hk]
    letI := Fintype.ofFinite
      {f : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) -> Nat //
        Finset.univ.sum
          (fun P => f P * Ideal.inertiaDeg P.val Int) = k}
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    exact hEmpty

theorem idealCountAtPrimePow_eq_geomSum
    (D : OddFundamentalDiscriminant) (p k : Nat) (hp : Nat.Prime p) :
    (Nat.card
      {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.absNorm I = p ^ k} : Complex) =
      (Finset.range (k + 1)).sum (fun j => D.character p ^ j) := by
  letI : Fact (Nat.Prime p) := Fact.mk hp
  have hcard := Nat.card_congr
    (idealNormPrimePowEquivExponentVectors D.QuadraticField p k)
  rcases D.character_isQuadratic p with hzero | hone | hneg
  next =>
    have hvectors := D.ramified_exponentVectors_card p k hzero
    have hcount :
        Nat.card
          {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
            Ideal.absNorm I = p ^ k} = 1 :=
      hcard.trans hvectors
    rw [hcount, hzero]
    simp
  next =>
    have hleft := D.split_exponentVectors_card p k hone
    have hcount :
        Nat.card
          {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
            Ideal.absNorm I = p ^ k} = k + 1 :=
      hcard.trans hleft
    rw [hcount, hone]
    simp
  next =>
    have hleft := D.inert_exponentVectors_card p k hneg
    have hcount :
        Nat.card
          {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
            Ideal.absNorm I = p ^ k} =
          if Even k then 1 else 0 :=
      hcard.trans hleft
    rw [hcount, hneg]
    by_cases hk : Even k
    next =>
      simp [hk, neg_one_geom_sum, Nat.even_add_one]
    next =>
      simp [hk, neg_one_geom_sum, Nat.even_add_one]


end

end NumberField.OddFundamentalDiscriminant
