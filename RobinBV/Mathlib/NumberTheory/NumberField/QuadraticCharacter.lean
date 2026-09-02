/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

@[expose] public section

/-!
# Quadratic characters of odd fundamental discriminants

This file constructs the Jacobi-symbol Dirichlet character of an odd
fundamental discriminant.  It proves that the character is quadratic,
self-dual, primitive with conductor equal to the absolute discriminant, and
has the parity determined by the sign of the discriminant.
-/

namespace NumberField

noncomputable section

private def modFourCharacter : MulChar (ZMod 4) Int where
  toFun a :=
    match a with
    | 0 | 2 => 0
    | 1 => 1
    | 3 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

private theorem modFourCharacter_nat_mod_four (n : Nat) :
    modFourCharacter n = modFourCharacter (n % 4 : Nat) := by
  grind

private theorem modFourCharacter_nat_one_mod_four {n : Nat}
    (hn : n % 4 = 1) : modFourCharacter n = 1 := by
  rw [modFourCharacter_nat_mod_four, hn]
  rfl

private theorem modFourCharacter_nat_three_mod_four {n : Nat}
    (hn : n % 4 = 3) : modFourCharacter n = -1 := by
  rw [modFourCharacter_nat_mod_four, hn]
  rfl

private theorem legendreSym_neg_one_eq_modFourCharacter (p : Nat)
    (hp : p.Prime) (hp2 : Not (p = 2)) :
    @legendreSym p (Fact.mk hp) (-1) = modFourCharacter p := by
  let _ : Fact p.Prime := Fact.mk hp
  have hchar : Not (ringChar (ZMod p) = 2) := by
    simpa [ZMod.ringChar_zmod_n] using hp2
  rw [legendreSym, Int.cast_neg, Int.cast_one,
    quadraticChar_eq_pow_of_char_ne_two hchar
    (neg_ne_zero.mpr one_ne_zero)]
  rw [ZMod.card p]
  rcases Nat.odd_mod_four_iff.mp
      (Nat.odd_iff.mp (hp.odd_of_ne_two hp2)) with hp1 | hp3
  next =>
    have hpow : (-1 : ZMod p) ^ (p / 2) = 1 := by
      have hpowInt := ZMod.neg_one_pow_div_two_of_one_mod_four hp1
      have hcast := congrArg (fun z : Int => (z : ZMod p)) hpowInt
      simpa only [Int.cast_neg, Int.cast_one, Int.cast_pow] using hcast
    rw [if_pos hpow, modFourCharacter_nat_one_mod_four hp1]
  next =>
    have hpow : (-1 : ZMod p) ^ (p / 2) = -1 := by
      have hpowInt := ZMod.neg_one_pow_div_two_of_three_mod_four hp3
      have hcast := congrArg (fun z : Int => (z : ZMod p)) hpowInt
      simpa only [Int.cast_neg, Int.cast_one, Int.cast_pow] using hcast
    have hne : Not ((-1 : ZMod p) ^ (p / 2) = 1) := by
      rw [hpow]
      exact Ring.neg_one_ne_one_of_char_ne_two hchar
    rw [if_neg hne, modFourCharacter_nat_three_mod_four hp3]

theorem jacobiSym_neg_one_eq_one_of_mod_four_eq_one {m : Nat}
    (hm : m % 4 = 1) : jacobiSym (-1) m = 1 := by
  have hodd : Odd m := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hm)
  calc
    jacobiSym (-1) m = modFourCharacter m :=
      jacobiSym.value_at (-1) modFourCharacter.toMonoidHom
        legendreSym_neg_one_eq_modFourCharacter hodd
    _ = 1 := modFourCharacter_nat_one_mod_four hm

theorem jacobiSym_neg_one_eq_neg_one_of_mod_four_eq_three {m : Nat}
    (hm : m % 4 = 3) : jacobiSym (-1) m = -1 := by
  have hodd : Odd m := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hm)
  calc
    jacobiSym (-1) m = modFourCharacter m :=
      jacobiSym.value_at (-1) modFourCharacter.toMonoidHom
        legendreSym_neg_one_eq_modFourCharacter hodd
    _ = -1 := modFourCharacter_nat_three_mod_four hm

theorem Int.natAbs_mod_four_eq_one_of_pos {D : Int} (hpos : 0 < D)
    (hmod : D % 4 = 1) : D.natAbs % 4 = 1 := by
  have hmodInt : ((D.natAbs : Nat) : Int) % 4 = 1 := by
    rw [Int.natAbs_of_nonneg hpos.le]
    exact hmod
  exact_mod_cast hmodInt

theorem Int.natAbs_mod_four_eq_three_of_neg {D : Int} (hneg : D < 0)
    (hmod : D % 4 = 1) : D.natAbs % 4 = 3 := by
  have hnot : Not (Dvd.dvd (4 : Int) D) := by
    intro hdvd
    have hz : D % 4 = 0 := Int.emod_eq_zero_of_dvd hdvd
    omega
  have hnegmod : (-D) % 4 = 3 := by
    rw [Int.neg_emod, if_neg hnot, hmod]
    norm_num
  have hmodInt : ((D.natAbs : Nat) : Int) % 4 = 3 := by
    rw [Int.ofNat_natAbs_of_nonpos hneg.le]
    exact hnegmod
  exact_mod_cast hmodInt

def oddJacobiCharacter (m : Nat) [NeZero m] (hm : 1 < m) :
    DirichletCharacter Int m where
  toFun x := jacobiSym (x.val : Int) m
  map_one' := by
    rw [ZMod.val_one'' (by omega)]
    exact jacobiSym.one_left m
  map_mul' x y := by
    rw [ZMod.val_mul]
    have hmod :
        jacobiSym (((x.val * y.val) % m : Nat) : Int) m =
          jacobiSym (((x.val * y.val : Nat) : Int)) m := by
      exact (jacobiSym.mod_left
        (((x.val * y.val : Nat) : Int)) m).symm
    rw [hmod]
    simpa [Nat.cast_mul] using
      jacobiSym.mul_left (x.val : Int) (y.val : Int) m
  map_nonunit' x hx := by
    have hNotCoprime : Not (Nat.Coprime x.val m) := by
      intro hCoprime
      apply hx
      rw [<- ZMod.natCast_zmod_val x]
      exact (ZMod.isUnit_iff_coprime x.val m).mpr hCoprime
    rw [jacobiSym.eq_zero_iff_not_coprime]
    exact_mod_cast hNotCoprime

theorem oddJacobiCharacter_apply_nat (m : Nat) [NeZero m]
    (hm : 1 < m) (n : Nat) :
  oddJacobiCharacter m hm n = jacobiSym (n : Int) m := by
  rw [oddJacobiCharacter]
  change jacobiSym (((n : ZMod m).val : Nat) : Int) m =
    jacobiSym (n : Int) m
  rw [ZMod.val_natCast]
  symm
  exact jacobiSym.mod_left (n : Int) m

theorem oddJacobiCharacter_apply_int (m : Nat) [NeZero m]
    (hm : 1 < m) (z : Int) :
    oddJacobiCharacter m hm z = jacobiSym z m := by
  rw [oddJacobiCharacter]
  change jacobiSym ((((z : ZMod m).val : Nat) : Int)) m =
    jacobiSym z m
  rw [ZMod.val_intCast]
  symm
  exact jacobiSym.mod_left z m

theorem oddJacobiCharacter_isQuadratic (m : Nat) [NeZero m]
    (hm : 1 < m) :
    MulChar.IsQuadratic (oddJacobiCharacter m hm) := by
  intro x
  exact jacobiSym.trichotomy (x.val : Int) m

def oddJacobiCharacterComplex (m : Nat) [NeZero m] (hm : 1 < m) :
    DirichletCharacter Complex m :=
  (oddJacobiCharacter m hm).ringHomComp (Int.castRingHom Complex)

theorem oddJacobiCharacterComplex_isQuadratic (m : Nat) [NeZero m]
    (hm : 1 < m) :
    MulChar.IsQuadratic (oddJacobiCharacterComplex m hm) :=
  (oddJacobiCharacter_isQuadratic m hm).comp (Int.castRingHom Complex)

theorem oddJacobiCharacterComplex_inv (m : Nat) [NeZero m]
    (hm : 1 < m) :
    Inv.inv (oddJacobiCharacterComplex m hm) =
      oddJacobiCharacterComplex m hm :=
  (oddJacobiCharacterComplex_isQuadratic m hm).inv

theorem oddJacobiCharacterComplex_sq (m : Nat) [NeZero m]
    (hm : 1 < m) :
    oddJacobiCharacterComplex m hm ^ 2 = 1 :=
  (oddJacobiCharacterComplex_isQuadratic m hm).sq_eq_one

theorem oddJacobiCharacterComplex_apply_int (m : Nat) [NeZero m]
    (hm : 1 < m) (z : Int) :
    oddJacobiCharacterComplex m hm z = jacobiSym z m := by
  rw [oddJacobiCharacterComplex, MulChar.ringHomComp_apply,
    oddJacobiCharacter_apply_int]
  norm_cast

theorem oddJacobiCharacter_eq_quadraticChar (p : Nat)
    [Fact p.Prime] :
    oddJacobiCharacter p ((show p.Prime from Fact.out).one_lt) =
      quadraticChar (ZMod p) := by
  apply MulChar.ext'
  intro x
  change jacobiSym (x.val : Int) p = quadraticChar (ZMod p) x
  rw [<- jacobiSym.legendreSym.to_jacobiSym p (x.val : Int)]
  change quadraticChar (ZMod p) ((x.val : Int) : ZMod p) =
    quadraticChar (ZMod p) x
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem oddJacobiCharacterComplex_ne_one_of_prime (p : Nat)
    [Fact p.Prime] (hp2 : Not (p = 2)) :
    Not (oddJacobiCharacterComplex p
      ((show p.Prime from Fact.out).one_lt) = 1) := by
  have hChar : Not (ringChar (ZMod p) = 2) := by
    simpa [ZMod.ringChar_zmod_n] using hp2
  have hInt : Not (oddJacobiCharacter p
      ((show p.Prime from Fact.out).one_lt) = 1) := by
    rw [oddJacobiCharacter_eq_quadraticChar p]
    exact quadraticChar_ne_one hChar
  exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr hInt

theorem oddJacobiCharacterComplex_isPrimitive_of_prime (p : Nat)
    [Fact p.Prime] (hp2 : Not (p = 2)) :
    DirichletCharacter.IsPrimitive
      (oddJacobiCharacterComplex p
        ((show p.Prime from Fact.out).one_lt)) := by
  have hp : p.Prime := Fact.out
  let chi := oddJacobiCharacterComplex p hp.one_lt
  have hne : Not (chi = 1) :=
    oddJacobiCharacterComplex_ne_one_of_prime p hp2
  rw [DirichletCharacter.IsPrimitive]
  have hdvd : Dvd.dvd chi.conductor p := chi.conductor_dvd_level
  rcases (Nat.dvd_prime hp).mp hdvd with hOne | hP
  next =>
    have htrivial : chi = 1 := by
      exact (DirichletCharacter.eq_one_iff_conductor_eq_one).mpr hOne
    exact (hne htrivial).elim
  next => exact hP

theorem prime_dvd_conductor_oddJacobiCharacterComplex (m : Nat)
    [NeZero m] (hm : 1 < m) (hodd : Odd m) (hsq : Squarefree m)
    {p : Nat} (hp : p.Prime) (hpm : Dvd.dvd p m) :
    Dvd.dvd p (oddJacobiCharacterComplex m hm).conductor := by
  by_contra hpd
  let q := m / p
  have hp0 : Not (p = 0) := hp.ne_zero
  have hmul : p * q = m := by
    exact Nat.mul_div_cancel' hpm
  have hq0 : Not (q = 0) := by
    intro hq
    apply NeZero.ne m
    rw [<- hmul, hq, mul_zero]
  have hpq : p.Coprime q := by
    apply Nat.coprime_of_squarefree_mul
    simpa [hmul] using hsq
  have hp2 : Not (p = 2) := by
    intro hp2
    subst p
    exact hodd.not_two_dvd_nat hpm
  let _ : Fact p.Prime := Fact.mk hp
  let _ : NeZero p := NeZero.mk hp0
  let _ : NeZero q := NeZero.mk hq0
  have hchar : Not (ringChar (ZMod p) = 2) := by
    simpa [ZMod.ringChar_zmod_n] using hp2
  choose g hg using quadraticChar_exists_neg_one' hchar
  let crt := Nat.chineseRemainder hpq (g : ZMod p).val 1
  let a : Nat := crt
  have hapmod : Nat.ModEq p a (g : ZMod p).val := by
    exact crt.prop.1
  have haqmod : Nat.ModEq q a 1 := by
    exact crt.prop.2
  have hcastp : (a : ZMod p) = (g : ZMod p) := by
    calc
      (a : ZMod p) = ((g : ZMod p).val : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff a (g : ZMod p).val p).mpr hapmod
      _ = (g : ZMod p) := ZMod.natCast_zmod_val _
  have hcastq : (a : ZMod q) = 1 := by
    rw [<- Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact haqmod
  have hap : a.Coprime p := by
    apply (ZMod.isUnit_iff_coprime a p).mp
    rw [hcastp]
    exact g.isUnit
  have haq : a.Coprime q := by
    apply (ZMod.isUnit_iff_coprime a q).mp
    rw [hcastq]
    exact isUnit_one
  have ham : a.Coprime m := by
    rw [<- hmul]
    exact Nat.Coprime.mul_right hap haq
  have hJap : jacobiSym (a : Int) p = -1 := by
    rw [<- jacobiSym.legendreSym.to_jacobiSym p (a : Int)]
    change quadraticChar (ZMod p) ((a : Int) : ZMod p) = -1
    rw [Int.cast_natCast, hcastp]
    exact hg
  have hJaq : jacobiSym (a : Int) q = 1 := by
    calc
      jacobiSym (a : Int) q = jacobiSym 1 q :=
        jacobiSym.mod_left' ((Int.natCast_modEq_iff).mpr haqmod).eq
      _ = 1 := jacobiSym.one_left q
  have hJam : jacobiSym (a : Int) m = -1 := by
    calc
      jacobiSym (a : Int) m = jacobiSym (a : Int) (p * q) := by rw [hmul]
      _ = jacobiSym (a : Int) p * jacobiSym (a : Int) q :=
        jacobiSym.mul_right' (a : Int) hp0 hq0
      _ = -1 := by rw [hJap, hJaq, mul_one]
  let chi := oddJacobiCharacterComplex m hm
  let d := chi.conductor
  have hdvd : Dvd.dvd d m := chi.conductor_dvd_level
  have hcopdp : d.Coprime p := by
    exact (hp.coprime_iff_not_dvd.mpr hpd).symm
  have hdq : Dvd.dvd d q := by
    apply hcopdp.dvd_of_dvd_mul_left
    rw [hmul]
    exact hdvd
  have hadmod : Nat.ModEq d a 1 := haqmod.of_dvd hdq
  have hcastd : (a : ZMod d) = 1 := by
    rw [<- Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact hadmod
  have hfac : chi.FactorsThrough d := by
    simpa [d] using chi.factorsThrough_conductor
  choose hd chi0 hchi using hfac
  have hamInt : IsCoprime (a : Int) m := by
    exact Nat.isCoprime_iff_coprime.mpr ham
  have hchange : chi (a : Int) = chi0 (a : Int) := by
    rw [hchi]
    exact DirichletCharacter.changeLevel_eq_cast_of_dvd' chi0 hd hamInt
  have hchi0 : chi0 (a : Int) = 1 := by
    rw [Int.cast_natCast, hcastd, map_one]
  have hminus : chi (a : Int) = -1 := by
    change oddJacobiCharacterComplex m hm (a : Int) = -1
    rw [oddJacobiCharacterComplex_apply_int, hJam]
    norm_num
  have hfalse : (-1 : Complex) = 1 := hminus.symm.trans (hchange.trans hchi0)
  norm_num at hfalse

theorem oddJacobiCharacterComplex_isPrimitive_of_odd_squarefree (m : Nat)
    [NeZero m] (hm : 1 < m) (hodd : Odd m) (hsq : Squarefree m) :
    DirichletCharacter.IsPrimitive (oddJacobiCharacterComplex m hm) := by
  rw [DirichletCharacter.isPrimitive_def]
  let chi := oddJacobiCharacterComplex m hm
  change chi.conductor = m
  have hdvd : Dvd.dvd chi.conductor m := chi.conductor_dvd_level
  have hcondSq : Squarefree chi.conductor :=
    hsq.squarefree_of_dvd hdvd
  apply (Nat.Squarefree.ext_iff hcondSq hsq).mpr
  intro p hp
  constructor
  next =>
    intro hpc
    exact Dvd.dvd.trans hpc hdvd
  next =>
    intro hpm
    exact prime_dvd_conductor_oddJacobiCharacterComplex m hm hodd hsq hp hpm

theorem oddJacobiCharacterComplex_even_of_mod_four_eq_one (m : Nat)
    [NeZero m] (hm : 1 < m) (hmod : m % 4 = 1) :
    (oddJacobiCharacterComplex m hm).Even := by
  rw [DirichletCharacter.Even]
  have hval := oddJacobiCharacterComplex_apply_int m hm (-1)
  rw [Int.cast_neg, Int.cast_one] at hval
  rw [hval,
    jacobiSym_neg_one_eq_one_of_mod_four_eq_one hmod]
  norm_num

theorem oddJacobiCharacterComplex_odd_of_mod_four_eq_three (m : Nat)
    [NeZero m] (hm : 1 < m) (hmod : m % 4 = 3) :
    (oddJacobiCharacterComplex m hm).Odd := by
  rw [DirichletCharacter.Odd]
  have hval := oddJacobiCharacterComplex_apply_int m hm (-1)
  rw [Int.cast_neg, Int.cast_one] at hval
  rw [hval,
    jacobiSym_neg_one_eq_neg_one_of_mod_four_eq_three hmod]
  norm_num

structure OddFundamentalDiscriminant where
  value : Int
  abs_gt_one : 1 < value.natAbs
  squarefree_natAbs : Squarefree value.natAbs
  mod_four : value % 4 = 1

namespace OddFundamentalDiscriminant

def modulus (D : OddFundamentalDiscriminant) : Nat := D.value.natAbs

instance modulus_neZero (D : OddFundamentalDiscriminant) : NeZero D.modulus :=
  NeZero.mk (Nat.ne_zero_of_lt D.abs_gt_one)

def character (D : OddFundamentalDiscriminant) :
    DirichletCharacter Complex D.modulus :=
  oddJacobiCharacterComplex D.modulus D.abs_gt_one

theorem character_apply_int (D : OddFundamentalDiscriminant) (z : Int) :
    D.character z = jacobiSym z D.modulus :=
  oddJacobiCharacterComplex_apply_int D.modulus D.abs_gt_one z

theorem character_isQuadratic (D : OddFundamentalDiscriminant) :
    MulChar.IsQuadratic D.character :=
  oddJacobiCharacterComplex_isQuadratic D.modulus D.abs_gt_one

theorem character_inv (D : OddFundamentalDiscriminant) :
    Inv.inv D.character = D.character :=
  oddJacobiCharacterComplex_inv D.modulus D.abs_gt_one

theorem character_sq (D : OddFundamentalDiscriminant) :
    D.character ^ 2 = 1 :=
  oddJacobiCharacterComplex_sq D.modulus D.abs_gt_one

theorem character_isPrimitive (D : OddFundamentalDiscriminant) :
    DirichletCharacter.IsPrimitive D.character := by
  have hne : Not (D.value = 0) := by
    intro hzero
    have hlarge := D.abs_gt_one
    rw [hzero] at hlarge
    norm_num at hlarge
  rcases lt_or_gt_of_ne hne with hneg | hpos
  next =>
    have hmod : D.modulus % 4 = 3 :=
      Int.natAbs_mod_four_eq_three_of_neg hneg D.mod_four
    have hodd : Odd D.modulus :=
      Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hmod)
    exact oddJacobiCharacterComplex_isPrimitive_of_odd_squarefree
      D.modulus D.abs_gt_one hodd D.squarefree_natAbs
  next =>
    have hmod : D.modulus % 4 = 1 :=
      Int.natAbs_mod_four_eq_one_of_pos hpos D.mod_four
    have hodd : Odd D.modulus :=
      Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hmod)
    exact oddJacobiCharacterComplex_isPrimitive_of_odd_squarefree
      D.modulus D.abs_gt_one hodd D.squarefree_natAbs

theorem conductor_eq_modulus (D : OddFundamentalDiscriminant) :
    D.character.conductor = D.modulus :=
  (DirichletCharacter.isPrimitive_def D.character).mp D.character_isPrimitive

theorem character_even_of_pos (D : OddFundamentalDiscriminant)
    (hpos : 0 < D.value) : D.character.Even := by
  exact oddJacobiCharacterComplex_even_of_mod_four_eq_one
    D.modulus D.abs_gt_one
      (Int.natAbs_mod_four_eq_one_of_pos hpos D.mod_four)

theorem character_odd_of_neg (D : OddFundamentalDiscriminant)
    (hneg : D.value < 0) : D.character.Odd := by
  exact oddJacobiCharacterComplex_odd_of_mod_four_eq_three
    D.modulus D.abs_gt_one
      (Int.natAbs_mod_four_eq_three_of_neg hneg D.mod_four)

end OddFundamentalDiscriminant

end

end NumberField
