/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimePowerRemainder

/-!
# Exact principal majorants for complete character prime-power steps

The principal character at the same modulus retains every conductor
omission. It majorizes the entire character step without replacing it
by a root-log envelope or truncating the admitted exponents.
-/

set_option autoImplicit false

namespace DirichletCharacter

noncomputable section

/-- Norms of ordinary powers of character values are exactly the real
principal powers, including nonunits and exponent zero. -/
theorem norm_value_pow_eq_principal_re
    {N : Nat} (chi : DirichletCharacter Complex N) (a : ZMod N) (j : Nat) :
    norm (chi a ^ j) = (((1 : DirichletCharacter Complex N) a)^j).re := by
  by_cases ha : IsUnit a
  next =>
    have hNorm : norm (chi a) = 1 := by
      simpa only [IsUnit.unit_spec] using chi.unit_norm_eq_one ha.unit
    rw [norm_pow, hNorm, MulChar.one_apply ha, one_pow, one_pow, Complex.one_re]
  next =>
    rw [chi.map_nonunit ha, (1 : DirichletCharacter Complex N).map_nonunit ha]
    by_cases hj : j = 0
    next =>
      simp only [hj, pow_zero, norm_one, Complex.one_re]
    next =>
      rw [zero_pow hj, norm_zero, Complex.zero_re]

/-- The exact principal step majorizes the full higher step at any base
with nonnegative logarithm. -/
theorem norm_primePowerHigherStep_le_principal_re
    {N : Nat} (chi : DirichletCharacter Complex N)
    (p m : Nat) (hp : 1 <= p) (t : Real) :
    norm (chi.primePowerHigherStep p m t) <=
      ((1 : DirichletCharacter Complex N).primePowerHigherStep p m t).re := by
  have hLog : 0 <= Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  unfold primePowerHigherStep
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLog,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum]
  apply mul_le_mul_of_nonneg_left _ hLog
  calc
    _ <= (Finset.Icc (m+1) (Nat.log p (Nat.floor t))).sum
        (fun j => norm (chi (p : ZMod N)^j)) := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact norm_value_pow_eq_principal_re chi (p : ZMod N) j

/-- Full prime-cap principal domination, retaining all admitted powers
and the same exact excluded-prime set on both sides. -/
theorem norm_sum_primePowerHigherStep_le_principal_re
    {N : Nat} (chi : DirichletCharacter Complex N) (P m : Nat) (t : Real) :
    norm ((Nat.primesLE P).sum (fun p => chi.primePowerHigherStep p m t)) <=
      ((Nat.primesLE P).sum
        (fun p => (1 : DirichletCharacter Complex N).primePowerHigherStep p m t)).re := by
  rw [Complex.re_sum]
  calc
    _ <= (Nat.primesLE P).sum (fun p => norm (chi.primePowerHigherStep p m t)) :=
      norm_sum_le _ _
    _ <= _ := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_primePowerHigherStep_le_principal_re chi p m
        (Nat.mem_primesLE.mp hp).2.one_le t

/-- The full principal higher step has norm equal to its real part. -/
theorem principal_sum_primePowerHigherStep_norm_eq_re
    (N P m : Nat) (t : Real) :
    norm ((Nat.primesLE P).sum
      (fun p => (1 : DirichletCharacter Complex N).primePowerHigherStep p m t)) =
    ((Nat.primesLE P).sum
      (fun p => (1 : DirichletCharacter Complex N).primePowerHigherStep p m t)).re := by
  apply le_antisymm (norm_sum_primePowerHigherStep_le_principal_re 1 P m t)
  exact Complex.re_le_norm _

end

end DirichletCharacter
