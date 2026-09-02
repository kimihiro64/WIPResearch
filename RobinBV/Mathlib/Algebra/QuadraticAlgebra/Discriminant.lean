/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.Discriminant

/-!
# Discriminant of a quadratic algebra

This file evaluates the discriminant of the canonical basis of a quadratic
algebra.  The specialization with relation `omega ^ 2 = a + omega` gives the
canonical rank-two order of every integer congruent to one modulo four.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] (a b : R)

theorem discr_basis :
    Algebra.discr R (basis a b) = b ^ 2 + 4 * a := by
  have hb0 : basis a b (0 : Fin 2) = 1 := by
    apply (basis a b).repr.injective
    ext i
    fin_cases i <;> simp [basis_repr_apply]
  have hb1 : basis a b (1 : Fin 2) = omega := by
    apply (basis a b).repr.injective
    ext i
    fin_cases i <;> simp [basis_repr_apply]
  have htrace (z : QuadraticAlgebra R a b) :
      Algebra.trace R (QuadraticAlgebra R a b) z = 2 * z.re + b * z.im := by
    rw [Algebra.trace_eq_matrix_trace (basis a b), Matrix.trace_fin_two]
    simp [Algebra.leftMulMatrix_eq_repr_mul, basis_repr_apply, hb0, hb1]
    ring
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, htrace]
  simp [hb0, hb1]
  ring

theorem discr_basis_one_eq_of_mod_four_eq_one (D : Int)
    (hmod : D % 4 = 1) :
    Algebra.discr Int (basis ((D - 1) / 4) 1) = D := by
  rw [discr_basis]
  have hzero : (D - 1) % 4 = 0 := by omega
  have hcancel : 4 * ((D - 1) / 4) = D - 1 :=
    Int.mul_ediv_cancel_of_emod_eq_zero hzero
  rw [hcancel]
  ring

end QuadraticAlgebra
