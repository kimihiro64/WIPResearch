/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
module

public import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZeta

/-!
# The prime two in canonical quadratic fields

This file analyzes the canonical quadratic generator modulo two, proves the
exact ideal-count coefficient at two, combines it with the odd-prime result,
and records the corresponding square-root criterion.
-/

@[expose] public section

namespace NumberField.OddFundamentalDiscriminant

noncomputable section

open UniqueFactorizationMonoid

theorem value_mod_eight_eq_one_or_five
    (D : OddFundamentalDiscriminant) :
    Or (D.value % 8 = 1) (D.value % 8 = 5) := by
  have hnonneg := Int.emod_nonneg D.value (by norm_num : Not ((8 : Int) = 0))
  have hlt := Int.emod_lt_of_pos D.value (by norm_num : (0 : Int) < 8)
  have hcompat : (D.value % 8) % 4 = 1 := by
    rw [Int.emod_emod_of_dvd D.value (by norm_num : Dvd.dvd (4 : Int) 8)]
    exact D.mod_four
  omega

theorem character_two_eq_one_of_value_mod_eight_eq_one
    (D : OddFundamentalDiscriminant) (hD : D.value % 8 = 1) :
    D.character 2 = 1 := by
  have hne : Not (D.value = 0) := by
    intro hzero
    have hlarge := D.abs_gt_one
    rw [hzero] at hlarge
    norm_num at hlarge
  rcases lt_or_gt_of_ne hne with hneg | hpos
  next =>
    have hnot : Not (Dvd.dvd (8 : Int) D.value) := by
      intro hdvd
      have hzero := Int.emod_eq_zero_of_dvd hdvd
      omega
    have hnegmod : (-D.value) % 8 = 7 := by
      rw [Int.neg_emod, if_neg hnot, hD]
      norm_num
    have hmInt : ((D.modulus : Nat) : Int) % 8 = 7 := by
      change ((D.value.natAbs : Nat) : Int) % 8 = 7
      rw [Int.ofNat_natAbs_of_nonpos hneg.le]
      exact hnegmod
    have hm : D.modulus % 8 = 7 := by
      exact_mod_cast hmInt
    have hmCast : (D.modulus : ZMod 8) = 7 := by
      apply (ZMod.natCast_eq_natCast_iff' D.modulus 7 8).mpr
      simpa using hm
    have hodd : Odd D.modulus := by
      apply Nat.odd_iff.mpr
      omega
    have hchar := D.character_apply_int 2
    have hj := jacobiSym.at_two hodd
    rw [hj] at hchar
    simpa [hmCast] using hchar
  next =>
    have hmInt : ((D.modulus : Nat) : Int) % 8 = 1 := by
      change ((D.value.natAbs : Nat) : Int) % 8 = 1
      rw [Int.natAbs_of_nonneg hpos.le]
      exact hD
    have hm : D.modulus % 8 = 1 := by
      exact_mod_cast hmInt
    have hmCast : (D.modulus : ZMod 8) = 1 := by
      apply (ZMod.natCast_eq_natCast_iff' D.modulus 1 8).mpr
      simpa using hm
    have hodd : Odd D.modulus := by
      apply Nat.odd_iff.mpr
      omega
    have hchar := D.character_apply_int 2
    have hj := jacobiSym.at_two hodd
    rw [hj] at hchar
    simpa [hmCast] using hchar

theorem character_two_eq_neg_one_of_value_mod_eight_eq_five
    (D : OddFundamentalDiscriminant) (hD : D.value % 8 = 5) :
    D.character 2 = -1 := by
  have hne : Not (D.value = 0) := by
    intro hzero
    have hlarge := D.abs_gt_one
    rw [hzero] at hlarge
    norm_num at hlarge
  rcases lt_or_gt_of_ne hne with hneg | hpos
  next =>
    have hnot : Not (Dvd.dvd (8 : Int) D.value) := by
      intro hdvd
      have hzero := Int.emod_eq_zero_of_dvd hdvd
      omega
    have hnegmod : (-D.value) % 8 = 3 := by
      rw [Int.neg_emod, if_neg hnot, hD]
      norm_num
    have hmInt : ((D.modulus : Nat) : Int) % 8 = 3 := by
      change ((D.value.natAbs : Nat) : Int) % 8 = 3
      rw [Int.ofNat_natAbs_of_nonpos hneg.le]
      exact hnegmod
    have hm : D.modulus % 8 = 3 := by
      exact_mod_cast hmInt
    have hmCast : (D.modulus : ZMod 8) = 3 := by
      apply (ZMod.natCast_eq_natCast_iff' D.modulus 3 8).mpr
      simpa using hm
    have hodd : Odd D.modulus := by
      apply Nat.odd_iff.mpr
      omega
    have hchar := D.character_apply_int 2
    have hj := jacobiSym.at_two hodd
    rw [hj] at hchar
    simpa [hmCast] using hchar
  next =>
    have hmInt : ((D.modulus : Nat) : Int) % 8 = 5 := by
      change ((D.value.natAbs : Nat) : Int) % 8 = 5
      rw [Int.natAbs_of_nonneg hpos.le]
      exact hD
    have hm : D.modulus % 8 = 5 := by
      exact_mod_cast hmInt
    have hmCast : (D.modulus : ZMod 8) = 5 := by
      apply (ZMod.natCast_eq_natCast_iff' D.modulus 5 8).mpr
      simpa using hm
    have hodd : Odd D.modulus := by
      apply Nat.odd_iff.mpr
      omega
    have hchar := D.character_apply_int 2
    have hj := jacobiSym.at_two hodd
    rw [hj] at hchar
    simpa [hmCast] using hchar

theorem quadraticIntegerCoefficient_zmod_two_eq_zero
    (D : OddFundamentalDiscriminant) (hD : D.value % 8 = 1) :
    ((((D.value - 1) / 4 : Int) : ZMod 2)) = 0 := by
  have hzero : (D.value - 1) % 4 = 0 := by
    have hmod := D.mod_four
    omega
  have hcoeffInt : 4 * ((D.value - 1) / 4) + 1 = D.value := by
    rw [Int.mul_ediv_cancel_of_emod_eq_zero hzero]
    ring
  have haMod : ((D.value - 1) / 4) % 2 = 0 := by
    omega
  apply
    (ZMod.intCast_eq_intCast_iff'
      ((D.value - 1) / 4) 0 2).mpr
  simpa using haMod

theorem quadraticIntegerCoefficient_zmod_two_eq_one
    (D : OddFundamentalDiscriminant) (hD : D.value % 8 = 5) :
    ((((D.value - 1) / 4 : Int) : ZMod 2)) = 1 := by
  have hzero : (D.value - 1) % 4 = 0 := by
    have hmod := D.mod_four
    omega
  have hcoeffInt : 4 * ((D.value - 1) / 4) + 1 = D.value := by
    rw [Int.mul_ediv_cancel_of_emod_eq_zero hzero]
    ring
  have haMod : ((D.value - 1) / 4) % 2 = 1 := by
    omega
  apply
    (ZMod.intCast_eq_intCast_iff'
      ((D.value - 1) / 4) 1 2).mpr
  simpa using haMod

theorem quadraticIntegerPolynomial_isRoot_zmod_two_of_mod_eight_one
    (D : OddFundamentalDiscriminant) (hD : D.value % 8 = 1)
    (x : ZMod 2) :
    Polynomial.IsRoot
      (D.quadraticIntegerPolynomial.map
        (Int.castRingHom (ZMod 2))) x := by
  rw [Polynomial.IsRoot.def]
  simp [quadraticIntegerPolynomial,
    D.quadraticIntegerCoefficient_zmod_two_eq_zero hD]

theorem quadraticIntegerPolynomial_not_isRoot_zmod_two_of_mod_eight_five
    (D : OddFundamentalDiscriminant) (hD : D.value % 8 = 5)
    (x : ZMod 2) :
    Not (Polynomial.IsRoot
      (D.quadraticIntegerPolynomial.map
        (Int.castRingHom (ZMod 2))) x) := by
  rw [Polynomial.IsRoot.def]
  simp [quadraticIntegerPolynomial,
    D.quadraticIntegerCoefficient_zmod_two_eq_one hD]

theorem card_monicLinearFactors_zmod_two_of_mod_eight_one
    (D : OddFundamentalDiscriminant) (hD : D.value % 8 = 1) :
    Nat.card
      {Q : Polynomial (ZMod 2) //
        And
          (Membership.mem
            (normalizedFactors
              (D.quadraticIntegerPolynomial.map
                (Int.castRingHom (ZMod 2)))) Q)
          (Q.natDegree = 1)} = 2 := by
  let P :=
    D.quadraticIntegerPolynomial.map (Int.castRingHom (ZMod 2))
  have hP : Not (P = 0) :=
    Polynomial.map_monic_ne_zero D.quadraticIntegerPolynomial_monic
  let eFactorRoot := monicLinearFactorEquivRoot P hP
  let eRootAll :
      Equiv {x : ZMod 2 // Polynomial.IsRoot P x} (ZMod 2) := {
    toFun x := x.val
    invFun x := Subtype.mk x
      (D.quadraticIntegerPolynomial_isRoot_zmod_two_of_mod_eight_one
        hD x)
    left_inv x := by apply Subtype.ext; rfl
    right_inv x := rfl }
  have hcard := Nat.card_congr (eFactorRoot.trans eRootAll)
  simpa [ZMod.card] using hcard

theorem card_monicLinearFactors_zmod_two_of_mod_eight_five
    (D : OddFundamentalDiscriminant) (hD : D.value % 8 = 5) :
    Nat.card
      {Q : Polynomial (ZMod 2) //
        And
          (Membership.mem
            (normalizedFactors
              (D.quadraticIntegerPolynomial.map
                (Int.castRingHom (ZMod 2)))) Q)
          (Q.natDegree = 1)} = 0 := by
  let P :=
    D.quadraticIntegerPolynomial.map (Int.castRingHom (ZMod 2))
  have hP : Not (P = 0) :=
    Polynomial.map_monic_ne_zero D.quadraticIntegerPolynomial_monic
  let eFactorRoot := monicLinearFactorEquivRoot P hP
  have hEmpty : IsEmpty {x : ZMod 2 // Polynomial.IsRoot P x} :=
    IsEmpty.mk (fun x =>
      D.quadraticIntegerPolynomial_not_isRoot_zmod_two_of_mod_eight_five
        hD x.val x.property)
  have hrootCard :
      Nat.card {x : ZMod 2 // Polynomial.IsRoot P x} = 0 := by
    letI : IsEmpty {x : ZMod 2 // Polynomial.IsRoot P x} := hEmpty
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    exact inferInstance
  rw [Nat.card_congr eFactorRoot]
  exact hrootCard

theorem idealCountAtTwo_eq_one_add_character
    (D : OddFundamentalDiscriminant) :
    (Nat.card
      {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.absNorm I = 2} : Complex) =
      1 + D.character 2 := by
  letI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  let e :=
    (idealNormPrimeEquivPrimesOverInertiaOne D.QuadraticField 2).trans
      (D.primesOverInertiaOneEquivMonicLinearFactors 2)
  have hcard := Nat.card_congr e
  rcases D.value_mod_eight_eq_one_or_five with hD | hD
  next =>
    have hfactor :=
      D.card_monicLinearFactors_zmod_two_of_mod_eight_one hD
    have hcount :
        Nat.card
          {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
            Ideal.absNorm I = 2} = 2 :=
      hcard.trans hfactor
    rw [hcount, D.character_two_eq_one_of_value_mod_eight_eq_one hD]
    norm_num
  next =>
    have hfactor :=
      D.card_monicLinearFactors_zmod_two_of_mod_eight_five hD
    have hcount :
        Nat.card
          {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
            Ideal.absNorm I = 2} = 0 :=
      hcard.trans hfactor
    rw [hcount,
      D.character_two_eq_neg_one_of_value_mod_eight_eq_five hD]
    norm_num

theorem idealCountAtPrime_eq_one_add_character
    (D : OddFundamentalDiscriminant) (p : Nat) (hp : Nat.Prime p) :
    (Nat.card
      {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.absNorm I = p} : Complex) =
      1 + D.character p := by
  letI : Fact (Nat.Prime p) := Fact.mk hp
  rcases hp.eq_two_or_odd' with hpTwo | hpOdd
  next =>
    subst p
    exact D.idealCountAtTwo_eq_one_add_character
  next =>
    exact D.idealCountAtOddPrime_eq_one_add_character p hpOdd

theorem quadraticIntegerPolynomial_hasRoot_iff_isSquare
    (D : OddFundamentalDiscriminant) (p : Nat) [Fact (Nat.Prime p)]
    (hpOdd : Odd p) :
    (exists x : ZMod p,
      Polynomial.IsRoot
        (D.quadraticIntegerPolynomial.map (Int.castRingHom (ZMod p))) x) <->
      IsSquare (D.value : ZMod p) := by
  have hmod := D.mod_four
  have hzero : (D.value - 1) % 4 = 0 := by omega
  have hcoeffInt : 4 * ((D.value - 1) / 4) + 1 = D.value := by
    rw [Int.mul_ediv_cancel_of_emod_eq_zero hzero]
    ring
  have hcoeff :
      (4 : ZMod p) * (((D.value - 1) / 4 : Int) : ZMod p) + 1 =
        (D.value : ZMod p) := by
    have hcast := congrArg (fun z : Int => (z : ZMod p)) hcoeffInt
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
      using hcast
  have hpNeTwo : Not (p = 2) := by
    intro hpTwo
    rw [hpTwo] at hpOdd
    choose k hk using hpOdd
    omega
  have htwo : Not ((2 : ZMod p) = 0) := by
    intro h
    have hdiv : Dvd.dvd p 2 := by
      exact (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hcases : Or (p = 1) (p = 2) :=
      (Nat.dvd_prime Nat.prime_two).mp hdiv
    cases hcases with
    | inl hpOne =>
        exact (Fact.out : Nat.Prime p).ne_one hpOne
    | inr hpTwo =>
        exact hpNeTwo hpTwo
  constructor
  next =>
    intro hroot
    choose x hx using hroot
    apply Exists.intro (2 * x - 1)
    rw [<- hcoeff]
    rw [Polynomial.IsRoot.def] at hx
    simp [quadraticIntegerPolynomial] at hx
    linear_combination -4 * hx
  next =>
    intro hsquare
    choose y hy using hsquare
    apply Exists.intro ((y + 1) / 2)
    rw [Polynomial.IsRoot.def]
    simp [quadraticIntegerPolynomial]
    rw [<- hcoeff] at hy
    field_simp [htwo]
    linear_combination -hy


end

end NumberField.OddFundamentalDiscriminant
