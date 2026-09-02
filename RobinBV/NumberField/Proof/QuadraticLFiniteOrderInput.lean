import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Basic
import RobinBV.NumberField.Proof.QuadraticLZeroSymmetry

/-!
# Finite-order inputs for completed quadratic L-functions

The completed Dirichlet L-function is proved nontrivial from its Euler product
at `s = 2`.  Exact period cancellation gives a uniform modulus bound for every
partial character sum.  These are the nontriviality and Abel-continuation
inputs needed for finite-order Hadamard control.
-/

namespace RobinBV.NumberField

open DirichletCharacter

noncomputable section

variable {N : Nat} [NeZero N]

theorem LFunction_two_ne_zero (chi : DirichletCharacter Complex N) :
    Not (LFunction chi 2 = 0) := by
  have hExp := chi.LSeries_eulerProduct_exp_log
    (s := (2 : Complex)) (by norm_num)
  have hSeries : Not (LSeries (fun n => chi n) (2 : Complex) = 0) := by
    intro hZero
    exact Complex.exp_ne_zero _ (hExp.trans hZero)
  rw [LFunction_eq_LSeries chi (by norm_num)]
  exact hSeries

theorem completedLFunction_two_ne_zero
    (chi : DirichletCharacter Complex N) :
    Not (completedLFunction chi 2 = 0) := by
  intro hCompleted
  have hRelation := LFunction_eq_completed_div_gammaFactor
    chi (2 : Complex) (Or.inl (by norm_num))
  rw [hCompleted, zero_div] at hRelation
  exact LFunction_two_ne_zero chi hRelation

/-- A completed Dirichlet L-function is not identically zero. -/
theorem completedLFunction_nontrivial
    (chi : DirichletCharacter Complex N) :
    Not (completedLFunction chi = 0) := by
  intro hZeroFunction
  apply completedLFunction_two_ne_zero chi
  exact congrFun hZeroFunction 2

theorem completedLFunction_bounded_on_closedBall
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (R : Real) :
    Exists fun M : Real =>
      And (0 <= M) (forall w : Complex,
        norm w <= R -> norm (completedLFunction chi w) <= M) := by
  have hContinuous : ContinuousOn (completedLFunction chi)
      (Metric.closedBall 0 R) :=
    (differentiable_completedLFunction hchi).continuous.continuousOn
  exact Complex.exists_norm_bound_on_closedBall hContinuous

theorem sum_range_character_eq_zero
    (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1)) :
    (Finset.range N).sum (fun n => chi n) = 0 := by
  cases N with
  | zero => exact (NeZero.ne (0 : Nat) rfl).elim
  | succ n =>
      calc
        (Finset.range (n + 1)).sum (fun k => chi k) =
            Finset.univ.sum (fun i : Fin (n + 1) => chi i.val) := by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (fun k : Nat => chi k) (n + 1)).symm
        _ = Finset.univ.sum (fun x : ZMod (n + 1) => chi x) := by
          apply Fintype.sum_equiv (ZMod.finEquiv (n + 1))
          intro i
          apply congrArg chi
          apply ZMod.val_injective (n + 1)
          rw [ZMod.val_cast_of_lt i.isLt]
          rfl
        _ = 0 := chi.sum_eq_zero_of_ne_one hchi

omit [NeZero N] in
private theorem character_nat_mul_modulus_add
    (chi : DirichletCharacter Complex N) (q m : Nat) :
    chi ((N * q + m : Nat) : ZMod N) = chi (m : ZMod N) := by
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]

theorem sum_range_mul_modulus_character_eq_zero
    (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1))
    (q : Nat) :
    (Finset.range (N * q)).sum (fun n => chi n) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, zero_add]
      simpa only [character_nat_mul_modulus_add chi q] using
        sum_range_character_eq_zero chi hchi

theorem sum_range_character_eq_sum_range_mod
    (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1))
    (n : Nat) :
    (Finset.range n).sum (fun k => chi k) =
      (Finset.range (n % N)).sum (fun k => chi k) := by
  conv_lhs => rw [<- Nat.div_add_mod n N]
  rw [Finset.sum_range_add,
    sum_range_mul_modulus_character_eq_zero chi hchi, zero_add]
  apply Finset.sum_congr rfl
  intro k _hk
  exact character_nat_mul_modulus_add chi (n / N) k

/-- Every partial sum of a nontrivial Dirichlet character has norm at most
its modulus, by exact cancellation of complete periods. -/
theorem norm_sum_range_character_le_modulus
    (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1))
    (n : Nat) :
    norm ((Finset.range n).sum (fun k => chi k)) <= (N : Real) := by
  rw [sum_range_character_eq_sum_range_mod chi hchi n]
  calc
    norm ((Finset.range (n % N)).sum (fun k => chi k)) <=
        (Finset.range (n % N)).sum (fun k => norm (chi k)) :=
      norm_sum_le _ _
    _ <= (Finset.range (n % N)).sum (fun _k => (1 : Real)) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact chi.norm_le_one k
    _ = (n % N : Nat) := by simp
    _ <= (N : Nat) := by
      exact_mod_cast (Nat.mod_lt n (NeZero.pos N)).le

end

end RobinBV.NumberField
