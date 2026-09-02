/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticDiscriminant

/-!
# Quadratic integer generators and prime ideal coefficients

This file constructs the canonical integral generator of the quadratic field
attached to an odd fundamental discriminant.  It proves that the generator
spans the full ring of integers, identifies its minimal polynomial, transports
Kummer--Dedekind factorization through the discriminant character, and proves
the exact Dedekind-zeta coefficient identity at every odd rational prime.
-/

@[expose] public section

namespace NumberField.OddFundamentalDiscriminant

noncomputable section

open UniqueFactorizationMonoid

def quadraticInteger (D : OddFundamentalDiscriminant) :
    NumberField.RingOfIntegers D.QuadraticField :=
  IsIntegralClosure.mk'
    (NumberField.RingOfIntegers D.QuadraticField)
    (QuadraticAlgebra.omega : D.QuadraticField) D.omega_isIntegral

theorem algebraMap_quadraticInteger (D : OddFundamentalDiscriminant) :
    algebraMap (NumberField.RingOfIntegers D.QuadraticField)
      D.QuadraticField D.quadraticInteger = QuadraticAlgebra.omega := by
  exact IsIntegralClosure.algebraMap_mk' _ _ _

def quadraticIntegerFamily (D : OddFundamentalDiscriminant) (i : Fin 2) :
    NumberField.RingOfIntegers D.QuadraticField :=
  IsIntegralClosure.mk'
    (NumberField.RingOfIntegers D.QuadraticField)
    (D.quadraticFieldBasis i) (D.quadraticFieldBasis_isIntegral i)

theorem algebraMap_quadraticIntegerFamily
    (D : OddFundamentalDiscriminant) (i : Fin 2) :
    algebraMap (NumberField.RingOfIntegers D.QuadraticField)
      D.QuadraticField (D.quadraticIntegerFamily i) =
        D.quadraticFieldBasis i := by
  exact IsIntegralClosure.algebraMap_mk' _ _ _

theorem quadraticIntegerFamily_zero (D : OddFundamentalDiscriminant) :
    D.quadraticIntegerFamily (0 : Fin 2) = 1 := by
  apply IsIntegralClosure.algebraMap_injective
    (NumberField.RingOfIntegers D.QuadraticField) Int D.QuadraticField
  rw [D.algebraMap_quadraticIntegerFamily, map_one,
    D.quadraticFieldBasis_zero]

theorem quadraticIntegerFamily_one (D : OddFundamentalDiscriminant) :
    D.quadraticIntegerFamily (1 : Fin 2) = D.quadraticInteger := by
  apply IsIntegralClosure.algebraMap_injective
    (NumberField.RingOfIntegers D.QuadraticField) Int D.QuadraticField
  rw [D.algebraMap_quadraticIntegerFamily, D.algebraMap_quadraticInteger,
    D.quadraticFieldBasis_one]

abbrev quadraticBasisIndexEquiv (D : OddFundamentalDiscriminant) :=
  (NumberField.integralBasis D.QuadraticField).indexEquiv
    D.quadraticFieldBasis

def reindexedIntegralBasis (D : OddFundamentalDiscriminant) :
    Module.Basis (Fin 2) Rat D.QuadraticField :=
  (NumberField.integralBasis D.QuadraticField).reindex
    D.quadraticBasisIndexEquiv

def reindexedIntegerBasis (D : OddFundamentalDiscriminant) :
    Module.Basis (Fin 2) Int
      (NumberField.RingOfIntegers D.QuadraticField) :=
  (NumberField.RingOfIntegers.basis D.QuadraticField).reindex
    D.quadraticBasisIndexEquiv

def integerChangeMatrix (D : OddFundamentalDiscriminant) :
    Matrix (Fin 2) (Fin 2) Int :=
  D.reindexedIntegerBasis.toMatrix D.quadraticIntegerFamily

theorem map_integerChangeMatrix (D : OddFundamentalDiscriminant) :
    Matrix.map D.integerChangeMatrix (algebraMap Int Rat) =
      D.reindexedIntegralBasis.toMatrix D.quadraticFieldBasis := by
  ext i j
  simp only [integerChangeMatrix, reindexedIntegerBasis,
    reindexedIntegralBasis, Module.Basis.toMatrix_apply, Matrix.map_apply,
    Module.Basis.repr_reindex_apply]
  rw [<- D.algebraMap_quadraticIntegerFamily j,
    NumberField.integralBasis_repr_apply]

theorem integerChangeMatrix_det_isUnit (D : OddFundamentalDiscriminant) :
    IsUnit D.integerChangeMatrix.det := by
  let P : Matrix (Fin 2) (Fin 2) Rat :=
    D.reindexedIntegralBasis.toMatrix D.quadraticFieldBasis
  have hdiscChange :
      Algebra.discr Rat D.quadraticFieldBasis =
        P.det ^ 2 * Algebra.discr Rat D.reindexedIntegralBasis := by
    calc
      Algebra.discr Rat D.quadraticFieldBasis =
          Algebra.discr Rat
            (Matrix.vecMul D.reindexedIntegralBasis
              (P.map (algebraMap Rat D.QuadraticField))) := by
        exact congrArg (Algebra.discr Rat)
          (D.reindexedIntegralBasis.toMatrix_map_vecMul
            D.quadraticFieldBasis).symm
      _ = P.det ^ 2 * Algebra.discr Rat D.reindexedIntegralBasis :=
        Algebra.discr_of_matrix_vecMul D.reindexedIntegralBasis P
  have hdetMap : P.det = ((D.integerChangeMatrix.det : Int) : Rat) := by
    dsimp only [P]
    rw [<- D.map_integerChangeMatrix]
    simpa only [RingHom.mapMatrix_apply, algebraMap_int_eq, eq_intCast] using
      (RingHom.map_det (algebraMap Int Rat) D.integerChangeMatrix).symm
  have hib : Algebra.discr Rat D.reindexedIntegralBasis =
      (NumberField.discr D.QuadraticField : Rat) := by
    convert
      (Algebra.discr_reindex Rat
        (NumberField.integralBasis D.QuadraticField)
        D.quadraticBasisIndexEquiv).trans
        (NumberField.coe_discr D.QuadraticField).symm using 1
    exact congrArg (Algebra.discr Rat)
      (show (D.reindexedIntegralBasis : Fin 2 -> D.QuadraticField) =
          Function.comp (NumberField.integralBasis D.QuadraticField)
            D.quadraticBasisIndexEquiv.symm from by
        simpa only [reindexedIntegralBasis] using
          (Module.Basis.coe_reindex
            (NumberField.integralBasis D.QuadraticField)
            D.quadraticBasisIndexEquiv))
  have hdiscRat : (D.value : Rat) =
      ((D.integerChangeMatrix.det : Int) : Rat) ^ 2 * (D.value : Rat) := by
    calc
      (D.value : Rat) = Algebra.discr Rat D.quadraticFieldBasis :=
        D.discr_quadraticFieldBasis.symm
      _ = P.det ^ 2 * Algebra.discr Rat D.reindexedIntegralBasis :=
        hdiscChange
      _ = ((D.integerChangeMatrix.det : Int) : Rat) ^ 2 *
          (NumberField.discr D.QuadraticField : Rat) := by
        rw [hdetMap, hib]
      _ = ((D.integerChangeMatrix.det : Int) : Rat) ^ 2 *
          (D.value : Rat) := by
        rw [D.discr_quadraticField]
  have hD : Not ((D.value : Rat) = 0) := by
    have hDInt : Not (D.value = 0) := by
      intro hzero
      have hgt := D.abs_gt_one
      rw [hzero] at hgt
      norm_num at hgt
    exact_mod_cast hDInt
  have hdetRat : ((D.integerChangeMatrix.det : Int) : Rat) ^ 2 = 1 := by
    calc
      ((D.integerChangeMatrix.det : Int) : Rat) ^ 2 =
          (((D.integerChangeMatrix.det : Int) : Rat) ^ 2 *
            (D.value : Rat)) / (D.value : Rat) := by field_simp
      _ = (D.value : Rat) / (D.value : Rat) := by rw [<- hdiscRat]
      _ = 1 := div_self hD
  have hdetInt : D.integerChangeMatrix.det ^ 2 = (1 : Int) := by
    exact_mod_cast hdetRat
  rw [Int.isUnit_iff]
  exact sq_eq_one_iff.mp hdetInt

def quadraticIntegerBasis (D : OddFundamentalDiscriminant) :
    Module.Basis (Fin 2) Int
      (NumberField.RingOfIntegers D.QuadraticField) :=
  let hbasis :=
    (D.reindexedIntegerBasis.is_basis_iff_det).mpr
      D.integerChangeMatrix_det_isUnit
  Module.Basis.mk hbasis.1 hbasis.2.ge

theorem quadraticIntegerBasis_apply (D : OddFundamentalDiscriminant)
    (i : Fin 2) :
    D.quadraticIntegerBasis i = D.quadraticIntegerFamily i := by
  simp [quadraticIntegerBasis, Module.Basis.mk_apply]

theorem adjoin_quadraticInteger_eq_top (D : OddFundamentalDiscriminant) :
    Algebra.adjoin Int {D.quadraticInteger} =
      (Top.top : Subalgebra Int
        (NumberField.RingOfIntegers D.QuadraticField)) := by
  apply Subalgebra.toSubmodule_injective
  change Subalgebra.toSubmodule (Algebra.adjoin Int {D.quadraticInteger}) =
    (Top.top : Submodule Int
      (NumberField.RingOfIntegers D.QuadraticField))
  apply le_antisymm le_top
  rw [<- D.quadraticIntegerBasis.span_eq]
  apply Submodule.span_le.mpr
  intro x hx
  choose i hi using hx
  rw [<- hi, D.quadraticIntegerBasis_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  next =>
    rw [D.quadraticIntegerFamily_zero]
    exact Subalgebra.one_mem _
  next =>
    have hsucc : j.succ = (1 : Fin 2) := by
      apply Fin.ext
      simp
    rw [hsucc, D.quadraticIntegerFamily_one]
    exact Algebra.subset_adjoin (Set.mem_singleton D.quadraticInteger)

theorem quadraticInteger_exponent_eq_one (D : OddFundamentalDiscriminant) :
    RingOfIntegers.exponent D.quadraticInteger = 1 := by
  rw [RingOfIntegers.exponent_eq_one_iff]
  exact D.adjoin_quadraticInteger_eq_top

def quadraticIntegerPolynomial (D : OddFundamentalDiscriminant) :
    Polynomial Int :=
  Polynomial.X ^ 2 - Polynomial.X -
    Polynomial.C ((D.value - 1) / 4)

theorem quadraticIntegerPolynomial_monic (D : OddFundamentalDiscriminant) :
    D.quadraticIntegerPolynomial.Monic := by
  unfold quadraticIntegerPolynomial
  monicity
  norm_num

theorem aeval_quadraticIntegerPolynomial (D : OddFundamentalDiscriminant) :
    Polynomial.aeval D.quadraticInteger D.quadraticIntegerPolynomial = 0 := by
  apply NumberField.RingOfIntegers.coe_injective
  simp [quadraticIntegerPolynomial, D.algebraMap_quadraticInteger,
    QuadraticAlgebra.omega_mul_omega_eq_algebraMap, pow_two]

def quadraticIntegerPowerBasis (D : OddFundamentalDiscriminant) :
    PowerBasis Int (NumberField.RingOfIntegers D.QuadraticField) :=
  PowerBasis.ofAdjoinEqTop'
    (Algebra.IsIntegral.isIntegral D.quadraticInteger)
    D.adjoin_quadraticInteger_eq_top

theorem quadraticIntegerPowerBasis_dim (D : OddFundamentalDiscriminant) :
    D.quadraticIntegerPowerBasis.dim = 2 := by
  rw [<- D.quadraticIntegerPowerBasis.finrank,
    NumberField.RingOfIntegers.rank, D.finrank_quadraticField]

theorem natDegree_minpoly_quadraticInteger
    (D : OddFundamentalDiscriminant) :
    (minpoly Int D.quadraticInteger).natDegree = 2 := by
  calc
    (minpoly Int D.quadraticInteger).natDegree =
        D.quadraticIntegerPowerBasis.dim := by
      simpa [quadraticIntegerPowerBasis] using
        D.quadraticIntegerPowerBasis.natDegree_minpoly
    _ = 2 := D.quadraticIntegerPowerBasis_dim

theorem minpoly_quadraticInteger (D : OddFundamentalDiscriminant) :
    minpoly Int D.quadraticInteger = D.quadraticIntegerPolynomial := by
  have hdvd : Dvd.dvd (minpoly Int D.quadraticInteger)
      D.quadraticIntegerPolynomial :=
    minpoly.isIntegrallyClosed_dvd
      (Algebra.IsIntegral.isIntegral D.quadraticInteger)
      D.aeval_quadraticIntegerPolynomial
  have hdegree : D.quadraticIntegerPolynomial.natDegree <=
      (minpoly Int D.quadraticInteger).natDegree := by
    rw [D.natDegree_minpoly_quadraticInteger]
    unfold quadraticIntegerPolynomial
    compute_degree
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (Algebra.IsIntegral.isIntegral D.quadraticInteger))
    D.quadraticIntegerPolynomial_monic hdvd hdegree).symm

theorem jacobiSym_value_eq_reciprocal
    (D : OddFundamentalDiscriminant) (p : Nat) (hpOdd : Odd p) :
    jacobiSym D.value p = jacobiSym (p : Int) D.modulus := by
  have hne : Not (D.value = 0) := by
    intro hzero
    have hlarge := D.abs_gt_one
    rw [hzero] at hlarge
    norm_num at hlarge
  rcases lt_or_gt_of_ne hne with hneg | hpos
  next =>
    have hmodAbs : D.modulus % 4 = 3 :=
      Int.natAbs_mod_four_eq_three_of_neg hneg D.mod_four
    have hvalue : D.value = -(D.modulus : Int) := by
      simp [modulus, Int.natCast_natAbs, abs_of_neg hneg]
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpOdd) with hpOne | hpThree
    next =>
      have hpCast : (p : ZMod 4) = 1 := by
        apply (ZMod.natCast_eq_natCast_iff' p 1 4).mpr
        simpa using hpOne
      have hrec :=
        jacobiSym.quadratic_reciprocity_one_mod_four'
          (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hmodAbs)) hpOne
      rw [hvalue, jacobiSym.neg _ hpOdd]
      simpa [hpCast] using hrec
    next =>
      have hpCast : (p : ZMod 4) = 3 := by
        apply (ZMod.natCast_eq_natCast_iff' p 3 4).mpr
        simpa using hpThree
      have hrec :=
        jacobiSym.quadratic_reciprocity_three_mod_four hmodAbs hpThree
      rw [hvalue, jacobiSym.neg _ hpOdd]
      simpa [hpCast] using congrArg Neg.neg hrec
  next =>
    have hmodAbs : D.modulus % 4 = 1 :=
      Int.natAbs_mod_four_eq_one_of_pos hpos D.mod_four
    have hrec :=
      jacobiSym.quadratic_reciprocity_one_mod_four hmodAbs hpOdd
    have hvalue : D.value = (D.modulus : Int) := by
      simp [modulus, Int.natCast_natAbs, abs_of_pos hpos]
    rw [hvalue]
    exact hrec

theorem character_apply_prime
    (D : OddFundamentalDiscriminant) (p : Nat) (hpOdd : Odd p) :
    D.character p = (jacobiSym D.value p : Complex) := by
  have hchar := D.character_apply_int (p : Int)
  rw [<- D.jacobiSym_value_eq_reciprocal p hpOdd] at hchar
  simpa using hchar

noncomputable def monicLinearFactorEquivRoot
    {F : Type*} [Field F] [DecidableEq F]
    (P : Polynomial F) (hP : Not (P = 0)) :
    Equiv
      {Q : Polynomial F //
        And (Membership.mem (normalizedFactors P) Q) (Q.natDegree = 1)}
      {x : F // Polynomial.IsRoot P x} := by
  let toRoot :
      {Q : Polynomial F //
        And (Membership.mem (normalizedFactors P) Q) (Q.natDegree = 1)} ->
        {x : F // Polynomial.IsRoot P x} := fun Q =>
    Subtype.mk (-Q.val.coeff 0) (by
      have hmem := Q.property.1
      have hne := ne_zero_of_mem_normalizedFactors hmem
      have hmonic : Q.val.Monic :=
        (Polynomial.normalize_eq_self_iff_monic hne).mp
          (normalize_normalized_factor Q.val hmem)
      have hshape := hmonic.eq_X_add_C Q.property.2
      have hdvd := dvd_of_mem_normalizedFactors hmem
      have hfactor :
          Polynomial.X - Polynomial.C (-Q.val.coeff 0) = Q.val := by
        rw [hshape]
        simp
      rw [<- hfactor] at hdvd
      exact Polynomial.dvd_iff_isRoot.mp hdvd)
  let toFactor :
      {x : F // Polynomial.IsRoot P x} ->
        {Q : Polynomial F //
          And (Membership.mem (normalizedFactors P) Q) (Q.natDegree = 1)} :=
    fun x =>
      Subtype.mk (Polynomial.X - Polynomial.C x.val) (And.intro (by
        apply (mem_normalizedFactors_iff' hP).mpr
        exact And.intro (Polynomial.irreducible_X_sub_C x.val)
          (And.intro
            (Polynomial.Monic.normalize_eq_self
              (Polynomial.monic_X_sub_C x.val))
            (Polynomial.dvd_iff_isRoot.mpr x.property))) (by
        exact Polynomial.natDegree_X_sub_C x.val))
  exact Equiv.mk toRoot toFactor (by
    intro Q
    apply Subtype.ext
    dsimp [toRoot, toFactor]
    have hmem := Q.property.1
    have hne := ne_zero_of_mem_normalizedFactors hmem
    have hmonic : Q.val.Monic :=
      (Polynomial.normalize_eq_self_iff_monic hne).mp
        (normalize_normalized_factor Q.val hmem)
    rw [hmonic.eq_X_add_C Q.property.2]
    simp) (by
    intro x
    apply Subtype.ext
    simp [toRoot, toFactor])

theorem two_ne_zero_zmod_of_odd_prime
    (p : Nat) [Fact (Nat.Prime p)] (hpOdd : Odd p) :
    Not ((2 : ZMod p) = 0) := by
  have hpNeTwo : Not (p = 2) := by
    intro hpTwo
    rw [hpTwo] at hpOdd
    choose k hk using hpOdd
    omega
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

noncomputable def quadraticIntegerRootEquivSqrt
    (D : OddFundamentalDiscriminant) (p : Nat) [Fact (Nat.Prime p)]
    (hpOdd : Odd p) :
    Equiv
      {x : ZMod p // Polynomial.IsRoot
        (D.quadraticIntegerPolynomial.map
          (Int.castRingHom (ZMod p))) x}
      {y : ZMod p // y ^ 2 = (D.value : ZMod p)} := by
  have hzero : (D.value - 1) % 4 = 0 := by
    have hmod := D.mod_four
    omega
  have hcoeffInt : 4 * ((D.value - 1) / 4) + 1 = D.value := by
    rw [Int.mul_ediv_cancel_of_emod_eq_zero hzero]
    ring
  have hcoeff :
      (4 : ZMod p) * (((D.value - 1) / 4 : Int) : ZMod p) + 1 =
        (D.value : ZMod p) := by
    have hcast := congrArg (fun z : Int => (z : ZMod p)) hcoeffInt
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
      using hcast
  have htwo := two_ne_zero_zmod_of_odd_prime p hpOdd
  let toSqrt :
      {x : ZMod p // Polynomial.IsRoot
        (D.quadraticIntegerPolynomial.map
          (Int.castRingHom (ZMod p))) x} ->
      {y : ZMod p // y ^ 2 = (D.value : ZMod p)} := fun x =>
    Subtype.mk (2 * x.val - 1) (by
      have hx := x.property
      rw [Polynomial.IsRoot.def] at hx
      simp [quadraticIntegerPolynomial] at hx
      rw [<- hcoeff]
      linear_combination 4 * hx)
  let toRoot :
      {y : ZMod p // y ^ 2 = (D.value : ZMod p)} ->
      {x : ZMod p // Polynomial.IsRoot
        (D.quadraticIntegerPolynomial.map
          (Int.castRingHom (ZMod p))) x} := fun y =>
    Subtype.mk ((y.val + 1) / 2) (by
      rw [Polynomial.IsRoot.def]
      simp [quadraticIntegerPolynomial]
      have hy := y.property.trans hcoeff.symm
      field_simp [htwo]
      linear_combination hy)
  exact Equiv.mk toSqrt toRoot (by
    intro x
    apply Subtype.ext
    dsimp [toSqrt, toRoot]
    field_simp [htwo]
    ring) (by
    intro y
    apply Subtype.ext
    dsimp [toSqrt, toRoot]
    field_simp [htwo]
    ring)

theorem card_monicLinearFactors_quadraticIntegerPolynomial
    (D : OddFundamentalDiscriminant) (p : Nat) [Fact (Nat.Prime p)]
    (hpOdd : Odd p) :
    ((Nat.card
      {Q : Polynomial (ZMod p) //
        And
          (Membership.mem
            (normalizedFactors
              (D.quadraticIntegerPolynomial.map
                (Int.castRingHom (ZMod p)))) Q)
          (Q.natDegree = 1)} : Nat) : Int) =
      jacobiSym D.value p + 1 := by
  let P :=
    D.quadraticIntegerPolynomial.map (Int.castRingHom (ZMod p))
  have hP : Not (P = 0) :=
    Polynomial.map_monic_ne_zero D.quadraticIntegerPolynomial_monic
  let eFactorRoot := monicLinearFactorEquivRoot P hP
  let eRootSqrt := D.quadraticIntegerRootEquivSqrt p hpOdd
  have hcard :
      Nat.card
        {Q : Polynomial (ZMod p) //
          And (Membership.mem (normalizedFactors P) Q) (Q.natDegree = 1)} =
      Nat.card {y : ZMod p // y ^ 2 = (D.value : ZMod p)} :=
    Nat.card_congr (eFactorRoot.trans eRootSqrt)
  let S : Set (ZMod p) := {y | y ^ 2 = (D.value : ZMod p)}
  have hset :
      Nat.card {y : ZMod p // y ^ 2 = (D.value : ZMod p)} =
        S.toFinset.card := by
    change Nat.card S = S.toFinset.card
    rw [Nat.card_eq_fintype_card, Set.toFinset_card]
  have hpNeTwo : Not (p = 2) := by
    intro hpTwo
    rw [hpTwo] at hpOdd
    choose k hk using hpOdd
    omega
  have hsqrt := legendreSym.card_sqrts (p := p) hpNeTwo D.value
  calc
    ((Nat.card
      {Q : Polynomial (ZMod p) //
        And
          (Membership.mem
            (normalizedFactors
              (D.quadraticIntegerPolynomial.map
                (Int.castRingHom (ZMod p)))) Q)
          (Q.natDegree = 1)} : Nat) : Int) =
        (Nat.card
          {y : ZMod p // y ^ 2 = (D.value : ZMod p)} : Nat) := by
      exact_mod_cast hcard
    _ = (S.toFinset.card : Int) := by
      exact_mod_cast hset
    _ = legendreSym p D.value + 1 := by
      simpa [S] using hsqrt
    _ = jacobiSym D.value p + 1 := by
      rw [jacobiSym.legendreSym.to_jacobiSym]

noncomputable def idealNormPrimeEquivPrimesOverInertiaOne
    (K : Type*) [Field K] [NumberField K]
    (p : Nat) [Fact (Nat.Prime p)] :
    Equiv
      {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = p}
      {P : Ideal.primesOver
          (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) //
        Ideal.inertiaDeg P.val Int = 1} := by
  let toPrime :
      {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = p} ->
      {P : Ideal.primesOver
          (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) //
        Ideal.inertiaDeg P.val Int = 1} := fun I =>
    have hprime : I.val.IsPrime := by
      apply Ideal.isPrime_of_irreducible_absNorm
      rw [I.property]
      exact (Nat.irreducible_iff_nat_prime p).mpr Fact.out
    have hlies : I.val.LiesOver (Ideal.span {(p : Int)}) := by
      have hNormPrime : Nat.Prime (Ideal.absNorm I.val) := by
        rw [I.property]
        exact Fact.out
      apply Ideal.LiesOver.mk
      simpa [I.property, Ideal.under_def] using
        (Ideal.span_singleton_absNorm (I := I.val) hNormPrime)
    have hpow : p ^ Ideal.inertiaDeg I.val Int = p := by
      letI : I.val.IsPrime := hprime
      letI : I.val.LiesOver (Ideal.span {(p : Int)}) := hlies
      rw [Ideal.pow_inertiaDeg p I.val]
      exact I.property
    have hinertia : Ideal.inertiaDeg I.val Int = 1 := by
      apply Nat.pow_right_injective (Fact.out : Nat.Prime p).two_le
      simpa using hpow
    Subtype.mk
      (Subtype.mk I.val (And.intro hprime hlies))
      hinertia
  let toIdeal :
      {P : Ideal.primesOver
          (Ideal.span {(p : Int)}) (NumberField.RingOfIntegers K) //
        Ideal.inertiaDeg P.val Int = 1} ->
      {I : Ideal (NumberField.RingOfIntegers K) //
        Ideal.absNorm I = p} := fun P =>
    Subtype.mk P.val.val (by
      have hpow := Ideal.pow_inertiaDeg p P.val.val
      rw [P.property, pow_one] at hpow
      exact hpow.symm)
  exact Equiv.mk toPrime toIdeal (by
    intro I
    apply Subtype.ext
    rfl) (by
    intro P
    apply Subtype.ext
    rfl)

noncomputable def primesOverInertiaOneEquivMonicLinearFactors
    (D : OddFundamentalDiscriminant) (p : Nat) [Fact (Nat.Prime p)] :
    Equiv
      {P : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.inertiaDeg P.val Int = 1}
      {Q : Polynomial (ZMod p) //
        And
          (Membership.mem
            (normalizedFactors
              (D.quadraticIntegerPolynomial.map
                (Int.castRingHom (ZMod p)))) Q)
          (Q.natDegree = 1)} := by
  have hpExp : Not (Dvd.dvd p
      (RingOfIntegers.exponent D.quadraticInteger)) := by
    rw [D.quadraticInteger_exponent_eq_one]
    exact (Fact.out : Nat.Prime p).not_dvd_one
  let e :=
    NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      hpExp
  let toFactor :
      {P : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.inertiaDeg P.val Int = 1} ->
      {Q : Polynomial (ZMod p) //
        And
          (Membership.mem
            (normalizedFactors
              (D.quadraticIntegerPolynomial.map
                (Int.castRingHom (ZMod p)))) Q)
          (Q.natDegree = 1)} := fun P =>
    let Q := e P.val
    Subtype.mk Q.val (And.intro (by
      have hmem := Q.property
      change Membership.mem
        ((normalizedFactors
          ((minpoly Int D.quadraticInteger).map
            (Int.castRingHom (ZMod p)))).toFinset) Q.val at hmem
      rw [D.minpoly_quadraticInteger] at hmem
      simpa only [Multiset.mem_toFinset] using hmem) (by
      have hinertia :=
        NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
          hpExp Q.property
      have heq : e.symm Q = P.val := e.symm_apply_apply P.val
      rw [heq] at hinertia
      exact hinertia.symm.trans P.property))
  let toPrime :
      {Q : Polynomial (ZMod p) //
        And
          (Membership.mem
            (normalizedFactors
              (D.quadraticIntegerPolynomial.map
                (Int.castRingHom (ZMod p)))) Q)
          (Q.natDegree = 1)} ->
      {P : Ideal.primesOver
          (Ideal.span {(p : Int)})
          (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.inertiaDeg P.val Int = 1} := fun Q =>
    let Q' :
        RingOfIntegers.monicFactorsMod
          D.quadraticInteger p :=
      Subtype.mk Q.val (by
        change Membership.mem
          ((normalizedFactors
            ((minpoly Int D.quadraticInteger).map
              (Int.castRingHom (ZMod p)))).toFinset) Q.val
        rw [D.minpoly_quadraticInteger]
        simpa only [Multiset.mem_toFinset] using Q.property.1)
    Subtype.mk (e.symm Q') (by
      have hinertia :=
        NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
          hpExp Q'.property
      exact hinertia.trans Q.property.2)
  exact Equiv.mk toFactor toPrime (by
    intro P
    apply Subtype.ext
    dsimp only [toFactor, toPrime]
    apply e.injective
    rw [e.apply_symm_apply]) (by
    intro Q
    apply Subtype.ext
    dsimp only [toFactor, toPrime]
    exact congrArg Subtype.val
      (e.apply_symm_apply
        (Subtype.mk Q.val (by
          change Membership.mem
            ((normalizedFactors
              ((minpoly Int D.quadraticInteger).map
                (Int.castRingHom (ZMod p)))).toFinset) Q.val
          rw [D.minpoly_quadraticInteger]
          simpa only [Multiset.mem_toFinset] using Q.property.1))))

theorem idealCountAtOddPrime_eq_jacobi_add_one
    (D : OddFundamentalDiscriminant) (p : Nat) [Fact (Nat.Prime p)]
    (hpOdd : Odd p) :
    ((Nat.card
      {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.absNorm I = p} : Nat) : Int) =
      jacobiSym D.value p + 1 := by
  let e :=
    (idealNormPrimeEquivPrimesOverInertiaOne D.QuadraticField p).trans
      (D.primesOverInertiaOneEquivMonicLinearFactors p)
  have hcard := Nat.card_congr e
  calc
    ((Nat.card
      {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.absNorm I = p} : Nat) : Int) =
      (Nat.card
        {Q : Polynomial (ZMod p) //
          And
            (Membership.mem
              (normalizedFactors
                (D.quadraticIntegerPolynomial.map
                  (Int.castRingHom (ZMod p)))) Q)
            (Q.natDegree = 1)} : Nat) := by
      exact_mod_cast hcard
    _ = jacobiSym D.value p + 1 :=
      D.card_monicLinearFactors_quadraticIntegerPolynomial p hpOdd

theorem idealCountAtOddPrime_eq_one_add_character
    (D : OddFundamentalDiscriminant) (p : Nat) [Fact (Nat.Prime p)]
    (hpOdd : Odd p) :
    (Nat.card
      {I : Ideal (NumberField.RingOfIntegers D.QuadraticField) //
        Ideal.absNorm I = p} : Complex) =
      1 + D.character p := by
  have hInt := D.idealCountAtOddPrime_eq_jacobi_add_one p hpOdd
  have hComplex := congrArg (fun z : Int => (z : Complex)) hInt
  rw [D.character_apply_prime p hpOdd]
  simpa [add_comm] using hComplex

end

end NumberField.OddFundamentalDiscriminant
