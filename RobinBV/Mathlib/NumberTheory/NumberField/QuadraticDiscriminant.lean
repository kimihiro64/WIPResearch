/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
/-
# Quadratic discriminant identities

This module records the elementary discriminant and squarefree identities
needed for quadratic number-field bookkeeping.
-/
module

import Mathlib.Data.Rat.Lemmas

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import RobinBV.Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticCharacter

/-!
# Canonical quadratic orders of odd fundamental discriminants

This file constructs the canonical rank-two integer order attached to an odd
fundamental discriminant and proves that its canonical basis has exactly that
discriminant.  It also records the nontrivial size of the discriminant of a
degree-two number field.
-/

@[expose] public section

namespace NumberField

theorem one_lt_natAbs_discr_of_finrank_eq_two (K : Type*) [Field K]
    [NumberField K] (hdegree : Module.finrank Rat K = 2) :
    1 < (discr K).natAbs := by
  have hdegree' : 1 < Module.finrank Rat K := by omega
  have hbound := abs_discr_gt_two (K := K) hdegree'
  have hboundInt : (2 : Int) < ((discr K).natAbs : Int) := by
    rw [Int.natCast_natAbs]
    exact hbound
  have hbound' : 2 < (discr K).natAbs := by
    exact_mod_cast hboundInt
  exact lt_trans (by norm_num) hbound'

namespace OddFundamentalDiscriminant

private theorem nat_not_isSquare_of_squarefree_of_one_lt {n : Nat}
    (hn : 1 < n) (hsq : Squarefree n) : Not (IsSquare n) := by
  intro hSquare
  choose x hx using hSquare
  have hx1 : Not (x = 1) := by
    intro hOne
    rw [hOne, one_mul] at hx
    omega
  have hpow : Squarefree (x ^ 2) := by
    rw [pow_two, <- hx]
    exact hsq
  have hexponent :=
    (Nat.squarefree_pow_iff hx1 (by norm_num : Not ((2 : Nat) = 0))).mp hpow
  omega

private theorem not_isSquare_value (D : OddFundamentalDiscriminant) :
    Not (IsSquare D.value) := by
  intro hSquare
  choose x hx using hSquare
  have hAbsSquare : IsSquare D.value.natAbs := by
    apply Exists.intro x.natAbs
    have hAbs := congrArg Int.natAbs hx
    simpa only [Int.natAbs_mul] using hAbs
  exact nat_not_isSquare_of_squarefree_of_one_lt
    D.abs_gt_one D.squarefree_natAbs hAbsSquare

private theorem no_rat_root (D : OddFundamentalDiscriminant) :
    forall r : Rat,
      Not (r ^ 2 = (((D.value - 1) / 4 : Int) : Rat) + r) := by
  intro r hroot
  have hmod := D.mod_four
  have hzero : (D.value - 1) % 4 = 0 := by omega
  have hcoeffInt : 4 * ((D.value - 1) / 4) + 1 = D.value := by
    rw [Int.mul_ediv_cancel_of_emod_eq_zero hzero]
    ring
  have hcoeffRat :
      (4 : Rat) * (((D.value - 1) / 4 : Int) : Rat) + 1 =
        (D.value : Rat) := by
    exact_mod_cast hcoeffInt
  have hSquareRat : IsSquare (D.value : Rat) := by
    apply Exists.intro (2 * r - 1)
    rw [<- hcoeffRat]
    nlinarith
  have hSquareInt : IsSquare D.value :=
    Rat.isSquare_intCast_iff.mp hSquareRat
  exact D.not_isSquare_value hSquareInt

/-- The canonical quadratic order with generator satisfying
`omega ^ 2 = (D - 1) / 4 + omega`. -/
abbrev QuadraticOrder (D : OddFundamentalDiscriminant) :=
  QuadraticAlgebra Int ((D.value - 1) / 4) 1

/-- The canonical quadratic field attached to `D`. -/
abbrev QuadraticField (D : OddFundamentalDiscriminant) :=
  QuadraticAlgebra Rat (((D.value - 1) / 4 : Int) : Rat) 1

instance quadraticField_irreducibleFact (D : OddFundamentalDiscriminant) :
    Fact (forall r : Rat,
      Not (r ^ 2 = (((D.value - 1) / 4 : Int) : Rat) + 1 * r)) :=
  Fact.mk (by simpa using D.no_rat_root)

instance quadraticField_numberField (D : OddFundamentalDiscriminant) :
    NumberField D.QuadraticField where
  to_charZero := inferInstance
  to_finiteDimensional :=
    (QuadraticAlgebra.basis
      (((D.value - 1) / 4 : Int) : Rat) 1).finiteDimensional_of_finite

theorem finrank_quadraticField (D : OddFundamentalDiscriminant) :
    Module.finrank Rat D.QuadraticField = 2 :=
  QuadraticAlgebra.finrank_eq_two
    (((D.value - 1) / 4 : Int) : Rat) 1

/-- The coordinatewise embedding of the canonical order into its fraction
field model. -/
def quadraticOrderToField (D : OddFundamentalDiscriminant) :
    AlgHom Int D.QuadraticOrder D.QuadraticField where
  toFun z := QuadraticAlgebra.mk (z.re : Rat) (z.im : Rat)
  map_one' := by
    ext <;> simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      Rat.intCast_zero, Rat.intCast_one]
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  commutes' z := by ext <;> simp

theorem quadraticOrderToField_omega (D : OddFundamentalDiscriminant) :
    D.quadraticOrderToField
      (QuadraticAlgebra.omega : D.QuadraticOrder) =
        (QuadraticAlgebra.omega : D.QuadraticField) := by
  ext <;> simp [quadraticOrderToField]

/-- The canonical generator of the quadratic field is integral over the
integers. -/
theorem omega_isIntegral (D : OddFundamentalDiscriminant) :
    IsIntegral Int
      (QuadraticAlgebra.omega : D.QuadraticField) := by
  have hOrder : IsIntegral Int
      (QuadraticAlgebra.omega : D.QuadraticOrder) :=
    IsIntegral.of_finite Int _
  have hMapped := hOrder.map D.quadraticOrderToField
  rw [D.quadraticOrderToField_omega] at hMapped
  exact hMapped

/-- The basis `1, omega` of the canonical quadratic order. -/
noncomputable def quadraticOrderBasis (D : OddFundamentalDiscriminant) :
    Module.Basis (Fin 2) Int D.QuadraticOrder :=
  QuadraticAlgebra.basis ((D.value - 1) / 4) 1

/-- The canonical quadratic order attached to `D` has discriminant `D`. -/
theorem discr_quadraticOrderBasis (D : OddFundamentalDiscriminant) :
    Algebra.discr Int D.quadraticOrderBasis = D.value := by
  exact QuadraticAlgebra.discr_basis_one_eq_of_mod_four_eq_one
    D.value D.mod_four

/-- The basis `1, omega` of the canonical quadratic field. -/
noncomputable abbrev quadraticFieldBasis (D : OddFundamentalDiscriminant) :
    Module.Basis (Fin 2) Rat D.QuadraticField :=
  QuadraticAlgebra.basis (((D.value - 1) / 4 : Int) : Rat) 1

theorem quadraticFieldBasis_zero (D : OddFundamentalDiscriminant) :
    D.quadraticFieldBasis (0 : Fin 2) = 1 := by
  apply D.quadraticFieldBasis.repr.injective
  ext i
  fin_cases i <;> simp [quadraticFieldBasis,
    QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one]

theorem quadraticFieldBasis_one (D : OddFundamentalDiscriminant) :
    D.quadraticFieldBasis (1 : Fin 2) = QuadraticAlgebra.omega := by
  apply D.quadraticFieldBasis.repr.injective
  ext i
  fin_cases i <;> simp [quadraticFieldBasis,
    QuadraticAlgebra.basis_repr_apply]

theorem quadraticFieldBasis_isIntegral (D : OddFundamentalDiscriminant)
    (i : Fin 2) : IsIntegral Int (D.quadraticFieldBasis i) := by
  fin_cases i
  next =>
    convert isIntegral_one
    simpa using D.quadraticFieldBasis_zero
  next =>
    convert D.omega_isIntegral
    simpa using D.quadraticFieldBasis_one

/-- The canonical rational basis has discriminant `D`.  The trace is computed
directly under the canonical rational-algebra structure of the field. -/
theorem discr_quadraticFieldBasis (D : OddFundamentalDiscriminant) :
    Algebra.discr Rat D.quadraticFieldBasis = (D.value : Rat) := by
  have htrace (z : D.QuadraticField) :
      Algebra.trace Rat D.QuadraticField z = 2 * z.re + z.im := by
    rw [Algebra.trace_eq_matrix_trace D.quadraticFieldBasis,
      Matrix.trace_fin_two]
    simp [Algebra.leftMulMatrix_eq_repr_mul,
      QuadraticAlgebra.basis_repr_apply, D.quadraticFieldBasis_zero,
      D.quadraticFieldBasis_one]
    ring
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, htrace]
  simp [D.quadraticFieldBasis_zero, D.quadraticFieldBasis_one,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hmod := D.mod_four
  have hzero : (D.value - 1) % 4 = 0 := by omega
  have hcoeffInt : 4 * ((D.value - 1) / 4) + 1 = D.value := by
    rw [Int.mul_ediv_cancel_of_emod_eq_zero hzero]
    ring
  have hcoeffRat :
      (4 : Rat) * (((D.value - 1) / 4 : Int) : Rat) + 1 =
      (D.value : Rat) := by
    exact_mod_cast hcoeffInt
  rw [<- hcoeffRat]
  ring

theorem integralBasis_to_quadraticFieldBasis_isIntegral
    (D : OddFundamentalDiscriminant) (i j : Fin 2) :
    let ib := (NumberField.integralBasis D.QuadraticField).reindex
      ((NumberField.integralBasis D.QuadraticField).indexEquiv
        D.quadraticFieldBasis)
    IsIntegral Int (ib.toMatrix D.quadraticFieldBasis i j) := by
  dsimp only
  rw [Module.Basis.toMatrix_apply, Module.Basis.repr_reindex_apply]
  choose x hx using
    (IsIntegralClosure.isIntegral_iff
      (A := NumberField.RingOfIntegers D.QuadraticField)).mp
      (D.quadraticFieldBasis_isIntegral j)
  rw [<- hx, NumberField.integralBasis_repr_apply]
  exact isIntegral_algebraMap

/-- The canonical quadratic field attached to an odd fundamental
discriminant has signed number-field discriminant exactly `D`. -/
theorem discr_quadraticField (D : OddFundamentalDiscriminant) :
    NumberField.discr D.QuadraticField = D.value := by
  let ib := (NumberField.integralBasis D.QuadraticField).reindex
    ((NumberField.integralBasis D.QuadraticField).indexEquiv
      D.quadraticFieldBasis)
  let P : Matrix (Fin 2) (Fin 2) Rat :=
    ib.toMatrix D.quadraticFieldBasis
  have hPInt (i j : Fin 2) : IsIntegral Int (P i j) := by
    exact D.integralBasis_to_quadraticFieldBasis_isIntegral i j
  have hPRep : forall i j : Fin 2, exists z : Int,
      algebraMap Int Rat z = P i j := by
    intro i j
    exact IsIntegrallyClosed.isIntegral_iff.mp (hPInt i j)
  let M : Matrix (Fin 2) (Fin 2) Int := fun i j =>
    Classical.choose (hPRep i j)
  have hM (i j : Fin 2) : algebraMap Int Rat (M i j) = P i j :=
    Classical.choose_spec (hPRep i j)
  have hMap : Matrix.map M (algebraMap Int Rat) = P := by
    ext i j
    exact hM i j
  have hdiscChange :
      Algebra.discr Rat D.quadraticFieldBasis =
        P.det ^ 2 * Algebra.discr Rat ib := by
    calc
      Algebra.discr Rat D.quadraticFieldBasis =
          Algebra.discr Rat
            (Matrix.vecMul ib (P.map (algebraMap Rat D.QuadraticField))) := by
        exact congrArg (Algebra.discr Rat)
          (ib.toMatrix_map_vecMul D.quadraticFieldBasis).symm
      _ = P.det ^ 2 * Algebra.discr Rat ib :=
        Algebra.discr_of_matrix_vecMul ib P
  have hdetMap : P.det = ((Matrix.det M : Int) : Rat) := by
    rw [<- hMap]
    simpa only [RingHom.mapMatrix_apply, algebraMap_int_eq, eq_intCast] using
      (RingHom.map_det (algebraMap Int Rat) M).symm
  have hib : Algebra.discr Rat ib =
      (NumberField.discr D.QuadraticField : Rat) := by
    convert
      (Algebra.discr_reindex Rat
        (NumberField.integralBasis D.QuadraticField)
        ((NumberField.integralBasis D.QuadraticField).indexEquiv
          D.quadraticFieldBasis)).trans
        (NumberField.coe_discr D.QuadraticField).symm using 1
    exact congrArg (Algebra.discr Rat)
      (show (ib : Fin 2 -> D.QuadraticField) =
          Function.comp (NumberField.integralBasis D.QuadraticField)
            ((NumberField.integralBasis D.QuadraticField).indexEquiv
              D.quadraticFieldBasis).symm from by
        simpa only [ib] using
          (Module.Basis.coe_reindex
            (NumberField.integralBasis D.QuadraticField)
            ((NumberField.integralBasis D.QuadraticField).indexEquiv
              D.quadraticFieldBasis)))
  have hdiscRat : (D.value : Rat) =
      ((Matrix.det M : Int) : Rat) ^ 2 *
        (NumberField.discr D.QuadraticField : Rat) := by
    rw [<- D.discr_quadraticFieldBasis, hdiscChange, hdetMap, hib]
  have hdiscInt : D.value =
      Matrix.det M ^ 2 * NumberField.discr D.QuadraticField := by
    exact_mod_cast hdiscRat
  have hnatAbs := congrArg Int.natAbs hdiscInt
  have hnatAbs' : D.value.natAbs =
      (Matrix.det M).natAbs ^ 2 *
        (NumberField.discr D.QuadraticField).natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow] using hnatAbs
  have hdiv : Dvd.dvd ((Matrix.det M).natAbs ^ 2) D.value.natAbs := by
    rw [hnatAbs']
    exact dvd_mul_right _ _
  have hsqPow : Squarefree ((Matrix.det M).natAbs ^ 2) :=
    D.squarefree_natAbs.squarefree_of_dvd hdiv
  have hdetAbs : (Matrix.det M).natAbs = 1 := by
    by_contra hne
    have hexponent :=
      (Nat.squarefree_pow_iff hne
        (by norm_num : Not ((2 : Nat) = 0))).mp hsqPow
    omega
  have hdetSq : Matrix.det M ^ 2 = (1 : Int) := by
    have hunit : IsUnit (Matrix.det M) := by
      rw [Int.isUnit_iff_natAbs_eq]
      exact hdetAbs
    rcases Int.isUnit_iff.mp hunit with hpos | hneg
    next => simp [hpos]
    next => simp [hneg]
  rw [hdetSq, one_mul] at hdiscInt
  exact hdiscInt.symm

end OddFundamentalDiscriminant

end NumberField
