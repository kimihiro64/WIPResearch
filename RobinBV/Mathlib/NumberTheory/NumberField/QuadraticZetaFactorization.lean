/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaPrimePowers

/-!
# Quadratic Dedekind zeta factorization

This file proves multiplicativity of the ideal-counting coefficients,
identifies their arithmetic function with the zeta-character convolution,
and deduces the zeta-times-L factorization in the half-plane of absolute
convergence.
-/

@[expose] public section

namespace NumberField.OddFundamentalDiscriminant

noncomputable section

open UniqueFactorizationMonoid

noncomputable def idealCoprimeNormPart
    (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (n : Nat) :
    Ideal (NumberField.RingOfIntegers K) :=
  ((normalizedFactors I).filter
    (fun P => Nat.Coprime (Ideal.absNorm P) n)).prod

noncomputable def idealNoncoprimeNormPart
    (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (n : Nat) :
    Ideal (NumberField.RingOfIntegers K) :=
  ((normalizedFactors I).filter
    (fun P => Not (Nat.Coprime (Ideal.absNorm P) n))).prod

theorem idealCoprimeNormPart_mul_idealNoncoprimeNormPart
    (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (n : Nat)
    (hI : Not (I = 0)) :
    idealCoprimeNormPart K I n * idealNoncoprimeNormPart K I n = I := by
  unfold idealCoprimeNormPart idealNoncoprimeNormPart
  rw [<- Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem absNorm_idealCoprimeNormPart_coprime
    (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (n : Nat) :
    Nat.Coprime (Ideal.absNorm (idealCoprimeNormPart K I n)) n := by
  unfold idealCoprimeNormPart
  rw [map_multiset_prod Ideal.absNorm]
  apply Nat.coprime_multiset_prod_left_iff.mpr
  intro a ha
  choose P hP hPa using Multiset.mem_map.mp ha
  rw [<- hPa]
  exact (Multiset.mem_filter.mp hP).2

theorem absNorm_normalizedFactor_coprime_left_of_not_coprime_right
    (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) {P : Ideal
      (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (normalizedFactors I) P)
    (m n : Nat) (hcop : Nat.Coprime m n)
    (hNot : Not (Nat.Coprime (Ideal.absNorm P) n)) :
    Nat.Coprime (Ideal.absNorm P) m := by
  have hCount : 0 < Multiset.count P (normalizedFactors I) :=
    Multiset.count_pos.mpr hP
  choose q r hr hqMem hqPrime hNorm using
    Ideal.exists_prime_and_absNorm_eq_pow_of_count_pos hCount
  have hqDvdN : Dvd.dvd q n := by
    by_contra hqNot
    have hqCop : Nat.Coprime q n :=
      hqPrime.coprime_iff_not_dvd.mpr hqNot
    apply hNot
    rw [hNorm]
    exact hqCop.pow_left r
  have hqNotDvdM : Not (Dvd.dvd q m) := by
    intro hqDvdM
    apply hqPrime.not_dvd_one
    rw [<- hcop.gcd_eq_one]
    exact Nat.dvd_gcd hqDvdM hqDvdN
  rw [hNorm]
  exact (hqPrime.coprime_iff_not_dvd.mpr hqNotDvdM).pow_left r

theorem absNorm_idealNoncoprimeNormPart_coprime
    (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K))
    (m n : Nat) (hcop : Nat.Coprime m n) :
    Nat.Coprime (Ideal.absNorm (idealNoncoprimeNormPart K I n)) m := by
  unfold idealNoncoprimeNormPart
  rw [map_multiset_prod Ideal.absNorm]
  apply Nat.coprime_multiset_prod_left_iff.mpr
  intro a ha
  choose P hP hPa using Multiset.mem_map.mp ha
  rw [<- hPa]
  have hFilter := Multiset.mem_filter.mp hP
  exact absNorm_normalizedFactor_coprime_left_of_not_coprime_right
    K I hFilter.1 m n hcop hFilter.2

theorem absNorm_idealCoprimeNormPart_eq_and_nonpart_eq
    (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K))
    (m n : Nat) (hm : Not (m = 0)) (hn : Not (n = 0))
    (hcop : Nat.Coprime m n)
    (hNorm : Ideal.absNorm I = m * n) :
    And
      (Ideal.absNorm (idealCoprimeNormPart K I n) = m)
      (Ideal.absNorm (idealNoncoprimeNormPart K I n) = n) := by
  have hI : Not (I = 0) := by
    intro hzero
    subst I
    have hmn : Not (m * n = 0) := mul_ne_zero hm hn
    exact hmn (by simpa using hNorm.symm)
  let A := Ideal.absNorm (idealCoprimeNormPart K I n)
  let B := Ideal.absNorm (idealNoncoprimeNormPart K I n)
  have hParts :=
    idealCoprimeNormPart_mul_idealNoncoprimeNormPart K I n hI
  have hProd : A * B = m * n := by
    calc
      A * B = Ideal.absNorm
          (idealCoprimeNormPart K I n *
            idealNoncoprimeNormPart K I n) := by
        exact (map_mul Ideal.absNorm _ _).symm
      _ = Ideal.absNorm I := congrArg Ideal.absNorm hParts
      _ = m * n := hNorm
  have hACop : Nat.Coprime A n :=
    absNorm_idealCoprimeNormPart_coprime K I n
  have hBCop : Nat.Coprime B m :=
    absNorm_idealNoncoprimeNormPart_coprime K I m n hcop
  have hADvdProd : Dvd.dvd A (m * n) := by
    rw [<- hProd]
    exact dvd_mul_right A B
  have hBDvdProd : Dvd.dvd B (m * n) := by
    rw [<- hProd]
    exact dvd_mul_left B A
  have hADvdM : Dvd.dvd A m :=
    hACop.dvd_of_dvd_mul_right hADvdProd
  have hBDvdN : Dvd.dvd B n :=
    hBCop.dvd_of_dvd_mul_left hBDvdProd
  choose x hx using hADvdM
  choose y hy using hBDvdN
  have hAPos : 0 < A := by
    by_contra hzero
    have hAZero : A = 0 := by omega
    rw [hAZero, zero_mul] at hProd
    exact (mul_ne_zero hm hn) hProd.symm
  have hBPos : 0 < B := by
    by_contra hzero
    have hBZero : B = 0 := by omega
    rw [hBZero, mul_zero] at hProd
    exact (mul_ne_zero hm hn) hProd.symm
  have hCancel :
      (A * B) * 1 = (A * B) * (x * y) := by
    calc
      (A * B) * 1 = A * B := by ring
      _ = m * n := hProd
      _ = (A * x) * (B * y) := by rw [<- hx, <- hy]
      _ = (A * B) * (x * y) := by ring
  have hxy : x * y = 1 :=
    Nat.mul_left_cancel (Nat.mul_pos hAPos hBPos) hCancel.symm
  have hxOne : x = 1 := by
    apply Nat.dvd_one.mp
    apply Exists.intro y
    exact hxy.symm
  have hyOne : y = 1 := by
    apply Nat.dvd_one.mp
    apply Exists.intro x
    rw [mul_comm]
    exact hxy.symm
  apply And.intro
  next =>
    change A = m
    rw [hx, hxOne, mul_one]
  next =>
    change B = n
    rw [hy, hyOne, mul_one]

theorem absNorm_normalizedFactor_coprime_of_coprime_norm
    (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K))
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (normalizedFactors I) P)
    (m n : Nat) (hNorm : Ideal.absNorm I = m)
    (hcop : Nat.Coprime m n) :
    Nat.Coprime (Ideal.absNorm P) n := by
  have hDvd : Dvd.dvd (Ideal.absNorm P) m := by
    rw [<- hNorm]
    exact Ideal.absNorm_dvd_absNorm_of_le
      (Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hP))
  exact hcop.of_dvd_left hDvd

theorem not_absNorm_normalizedFactor_coprime_norm
    (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K))
    {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (normalizedFactors I) P)
    (n : Nat) (hNorm : Ideal.absNorm I = n) :
    Not (Nat.Coprime (Ideal.absNorm P) n) := by
  intro hcop
  have hDvd : Dvd.dvd (Ideal.absNorm P) n := by
    rw [<- hNorm]
    exact Ideal.absNorm_dvd_absNorm_of_le
      (Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hP))
  have hOne : Ideal.absNorm P = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hDvd
  have hPrime : P.IsPrime :=
    Ideal.isPrime_of_prime (prime_of_normalized_factor P hP)
  exact (Ideal.absNorm_eq_one_iff.not.mpr hPrime.ne_top) hOne

theorem idealCoprimeNormPart_mul_eq_left
    (K : Type*) [Field K] [NumberField K]
    (I J : Ideal (NumberField.RingOfIntegers K))
    (m n : Nat) (hI : Not (I = 0)) (hJ : Not (J = 0))
    (hNormI : Ideal.absNorm I = m)
    (hNormJ : Ideal.absNorm J = n)
    (hcop : Nat.Coprime m n) :
    idealCoprimeNormPart K (I * J) n = I := by
  unfold idealCoprimeNormPart
  rw [normalizedFactors_mul hI hJ, Multiset.filter_add]
  have hLeft :
      (normalizedFactors I).filter
          (fun P => Nat.Coprime (Ideal.absNorm P) n) =
        normalizedFactors I := by
    apply Multiset.filter_eq_self.mpr
    intro P hP
    exact absNorm_normalizedFactor_coprime_of_coprime_norm
      K I hP m n hNormI hcop
  have hRight :
      (normalizedFactors J).filter
          (fun P => Nat.Coprime (Ideal.absNorm P) n) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact not_absNorm_normalizedFactor_coprime_norm K J hP n hNormJ
  rw [hLeft, hRight, add_zero]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem idealNoncoprimeNormPart_mul_eq_right
    (K : Type*) [Field K] [NumberField K]
    (I J : Ideal (NumberField.RingOfIntegers K))
    (m n : Nat) (hI : Not (I = 0)) (hJ : Not (J = 0))
    (hNormI : Ideal.absNorm I = m)
    (hNormJ : Ideal.absNorm J = n)
    (hcop : Nat.Coprime m n) :
    idealNoncoprimeNormPart K (I * J) n = J := by
  unfold idealNoncoprimeNormPart
  rw [normalizedFactors_mul hI hJ, Multiset.filter_add]
  have hLeft :
      (normalizedFactors I).filter
          (fun P => Not (Nat.Coprime (Ideal.absNorm P) n)) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    simp only [not_not]
    exact absNorm_normalizedFactor_coprime_of_coprime_norm
      K I hP m n hNormI hcop
  have hRight :
      (normalizedFactors J).filter
          (fun P => Not (Nat.Coprime (Ideal.absNorm P) n)) =
        normalizedFactors J := by
    apply Multiset.filter_eq_self.mpr
    intro P hP
    exact not_absNorm_normalizedFactor_coprime_norm K J hP n hNormJ
  rw [hLeft, hRight, zero_add]
  exact Ideal.prod_normalizedFactors_eq_self hJ

noncomputable def idealNormMulEquiv
    (K : Type*) [Field K] [NumberField K]
    (m n : Nat) (hm : Not (m = 0)) (hn : Not (n = 0))
    (hcop : Nat.Coprime m n) :
    Equiv
      (Prod
        {I : Ideal (NumberField.RingOfIntegers K) //
          Ideal.absNorm I = m}
        {J : Ideal (NumberField.RingOfIntegers K) //
          Ideal.absNorm J = n})
      {L : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm L = m * n} where
  toFun pair := Subtype.mk (pair.1.val * pair.2.val) (by
    rw [map_mul Ideal.absNorm, pair.1.property, pair.2.property])
  invFun L := by
    have hParts := absNorm_idealCoprimeNormPart_eq_and_nonpart_eq
      K L.val m n hm hn hcop L.property
    exact
      (Subtype.mk (idealCoprimeNormPart K L.val n) hParts.1,
        Subtype.mk (idealNoncoprimeNormPart K L.val n) hParts.2)
  left_inv pair := by
    apply Prod.ext
    next =>
      apply Subtype.ext
      apply idealCoprimeNormPart_mul_eq_left K
        pair.1.val pair.2.val m n
      next =>
        exact Ideal.absNorm_eq_zero_iff.not.mp (pair.1.property.trans_ne hm)
      next =>
        exact Ideal.absNorm_eq_zero_iff.not.mp (pair.2.property.trans_ne hn)
      next => exact pair.1.property
      next => exact pair.2.property
      next => exact hcop
    next =>
      apply Subtype.ext
      apply idealNoncoprimeNormPart_mul_eq_right K
        pair.1.val pair.2.val m n
      next =>
        exact Ideal.absNorm_eq_zero_iff.not.mp (pair.1.property.trans_ne hm)
      next =>
        exact Ideal.absNorm_eq_zero_iff.not.mp (pair.2.property.trans_ne hn)
      next => exact pair.1.property
      next => exact pair.2.property
      next => exact hcop
  right_inv L := by
    apply Subtype.ext
    apply idealCoprimeNormPart_mul_idealNoncoprimeNormPart K L.val n
    exact Ideal.absNorm_eq_zero_iff.not.mp
      (L.property.trans_ne (mul_ne_zero hm hn))

noncomputable def idealCountingArithmeticFunction
    (D : OddFundamentalDiscriminant) : ArithmeticFunction Complex :=
  toArithmeticFunction (fun n =>
    (Nat.card
      {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.absNorm I = n} : Complex))

theorem idealCountingArithmeticFunction_apply
    (D : OddFundamentalDiscriminant) (n : Nat) (hn : Not (n = 0)) :
    D.idealCountingArithmeticFunction n =
      (Nat.card
        {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
          Ideal.absNorm I = n} : Complex) := by
  simp [idealCountingArithmeticFunction, toArithmeticFunction, hn]

theorem idealCountingArithmeticFunction_isMultiplicative
    (D : OddFundamentalDiscriminant) :
    D.idealCountingArithmeticFunction.IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  apply And.intro
  next =>
    have hOne := D.idealCountAtPrimePow_eq_geomSum 2 0 Nat.prime_two
    simpa [idealCountingArithmeticFunction, toArithmeticFunction] using hOne
  next =>
    intro m n hm hn hcop
    rw [D.idealCountingArithmeticFunction_apply (m * n) (mul_ne_zero hm hn)]
    rw [D.idealCountingArithmeticFunction_apply m hm]
    rw [D.idealCountingArithmeticFunction_apply n hn]
    have hcard := Nat.card_congr
      (idealNormMulEquiv D.QuadraticField m n hm hn hcop)
    rw [<- hcard, Nat.card_prod, Nat.cast_mul]

theorem character_zetaMul_apply_prime_pow
    (D : OddFundamentalDiscriminant) (p k : Nat) (hp : Nat.Prime p) :
    D.character.zetaMul (p ^ k) =
      (Finset.range (k + 1)).sum (fun j => D.character p ^ j) := by
  rw [DirichletCharacter.zetaMul]
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  rw [Nat.sum_divisors_prime_pow hp]
  simp [toArithmeticFunction, hp.ne_zero]

theorem idealCountingArithmeticFunction_eq_character_zetaMul
    (D : OddFundamentalDiscriminant) :
    D.idealCountingArithmeticFunction = D.character.zetaMul := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    D.idealCountingArithmeticFunction
    D.idealCountingArithmeticFunction_isMultiplicative
    D.character.zetaMul
    (DirichletCharacter.isMultiplicative_zetaMul D.character)).mpr
  intro p k hp
  rw [D.idealCountingArithmeticFunction_apply (p ^ k)
    (pow_ne_zero k hp.ne_zero)]
  rw [D.idealCountAtPrimePow_eq_geomSum p k hp]
  exact (D.character_zetaMul_apply_prime_pow p k hp).symm

theorem idealCount_eq_character_zetaMul
    (D : OddFundamentalDiscriminant) (n : Nat) (hn : Not (n = 0)) :
    (Nat.card
      {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.absNorm I = n} : Complex) = D.character.zetaMul n := by
  rw [<- D.idealCountingArithmeticFunction_apply n hn]
  exact congrArg (fun f : ArithmeticFunction Complex => f n)
    D.idealCountingArithmeticFunction_eq_character_zetaMul

theorem dedekindZeta_quadraticField_eq_riemannZeta_mul_LFunction
    (D : OddFundamentalDiscriminant) {s : Complex} (hs : 1 < s.re) :
    NumberField.dedekindZeta D.QuadraticField s =
      riemannZeta s * D.character.LFunction s := by
  rw [NumberField.dedekindZeta]
  calc
    LSeries
        (fun n =>
          Nat.card
            {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
              Ideal.absNorm I = n}) s =
        LSeries D.character.zetaMul s := by
      exact LSeries_congr
        (fun hn => D.idealCount_eq_character_zetaMul _ hn) s
    _ = riemannZeta s * D.character.LFunction s := by
      rw [DirichletCharacter.zetaMul, <- ArithmeticFunction.coe_mul,
        LSeries_convolution']
      next =>
        congr 1
        next =>
          exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
        next =>
          rw [D.character.LFunction_eq_LSeries hs]
          exact LSeries_congr
            (fun hn => (D.character.apply_eq_toArithmeticFunction_apply hn).symm) s
      next =>
        exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
      next =>
        exact (LSeriesSummable_congr _
          (fun hn =>
            (D.character.apply_eq_toArithmeticFunction_apply hn).symm)).mpr
          (ZMod.LSeriesSummable_of_one_lt_re D.character hs)


end

end NumberField.OddFundamentalDiscriminant
