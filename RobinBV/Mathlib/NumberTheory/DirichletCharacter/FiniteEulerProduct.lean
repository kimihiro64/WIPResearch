/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import RobinBV.Mathlib.Analysis.Normed.Ring.FiniteProductRemainder

/-!
# Finite character Euler products with exponent caps

A capped divisor product differs from the full finite Euler product by an
exact product of cap factors. Linearization retains the finite Euler factor,
all cap interactions, and the entire complementary tail.

The exponent-one block involves the square of the character. No character
cancellation, conductor-uniform Euler-product bound, or asymptotic cap law is
assumed. The identities apply to any finite set of integers at least two;
primality is not needed for the finite algebra.
-/

noncomputable section

namespace DirichletCharacter

variable {N : Nat} (chi : DirichletCharacter Complex N)

/-- The local ratio in a character Euler factor at the natural index p. -/
def eulerRatio (p : Nat) : Complex := chi (p : ZMod N) / (p : Complex)

/-- The complete finite Euler product at s=1. -/
def finiteEulerProduct (s : Finset Nat) : Complex :=
  s.prod (fun p => (1 - chi.eulerRatio p) ^ (-1 : Int))

/-- The finite divisor product with the exponent at p bounded by a(p). -/
def finiteCappedEulerProduct (s : Finset Nat) (a : Nat -> Nat) : Complex :=
  s.prod (fun p => (Finset.range (a p + 1)).sum (fun k => chi.eulerRatio p ^ k))

/-- Overflow beyond the exponent caps inside the finite Euler product. -/
def finiteCapOverflow (s : Finset Nat) (a : Nat -> Nat) : Complex :=
  chi.finiteEulerProduct s - chi.finiteCappedEulerProduct s a

/-- Off-diagonal quadratic majorant for the full family of cap factors. -/
def capQuadraticMajorant (s : Finset Nat) (a : Nat -> Nat) : Real :=
  (((s.sum (fun p => norm (chi.eulerRatio p ^ (a p + 1)))) ^ 2 -
    s.sum (fun p => norm (chi.eulerRatio p ^ (a p + 1)) ^ 2)) / 2) *
      s.prod (fun p => 1 + norm (chi.eulerRatio p ^ (a p + 1)))

/-- Every local character ratio is dominated by the reciprocal index. -/
theorem norm_eulerRatio_le (p : Nat) :
    norm (chi.eulerRatio p) <= 1 / (p : Real) := by
  rw [eulerRatio, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (chi.norm_le_one _) (Nat.cast_nonneg p)

/-- At an index at least two the Euler denominator cannot vanish. -/
theorem eulerRatio_ne_one {p : Nat} (hp : 2 <= p) :
    Not (chi.eulerRatio p = 1) := by
  have hp1 : 1 < (p : Real) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hp)
  have hp0 : 0 < (p : Real) := by linarith
  have hdiv : 1 / (p : Real) < 1 := by
    simpa only [div_self (ne_of_gt hp0)] using div_lt_div_of_pos_right hp1 hp0
  intro h
  have hnorm := (chi.norm_eulerRatio_le p).trans_lt hdiv
  rw [h, norm_one] at hnorm
  exact (lt_irrefl (1 : Real)) hnorm

/-- Powers of a local ratio satisfy the full reciprocal-power bound. -/
theorem norm_eulerRatio_pow_le (p k : Nat) :
    norm (chi.eulerRatio p ^ k) <= 1 / (p : Real) ^ k := by
  rw [norm_pow, <- one_div_pow]
  exact pow_left_monotoneOn (norm_nonneg _)
    (show 0 <= 1 / (p : Real) from by positivity) (chi.norm_eulerRatio_le p)

/-- The finite geometric sum has the Euler-factor times cap-factor form. -/
theorem cappedLocalFactor_eq {p : Nat} (hp : 2 <= p) (a : Nat) :
    (Finset.range (a + 1)).sum (fun k => chi.eulerRatio p ^ k) =
      (1 - chi.eulerRatio p) ^ (-1 : Int) *
        (1 - chi.eulerRatio p ^ (a + 1)) := by
  rw [geom_sum_eq (chi.eulerRatio_ne_one hp)]
  rw [show chi.eulerRatio p ^ (a + 1) - 1 =
      -(1 - chi.eulerRatio p ^ (a + 1)) by ring]
  rw [show chi.eulerRatio p - 1 = -(1 - chi.eulerRatio p) by ring]
  simp only [zpow_neg_one, div_eq_mul_inv, inv_neg, neg_mul_neg, mul_comm]

/-- The finite Euler factor is nonzero; no uniform bound on it is asserted. -/
theorem finiteEulerProduct_ne_zero (s : Finset Nat)
    (hs : forall p, Membership.mem s p -> 2 <= p) :
    Not (chi.finiteEulerProduct s = 0) := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  simp only [zpow_neg_one]
  exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm (chi.eulerRatio_ne_one (hs p hp))))

/-- Exact capped Euler-product identity, with every cap factor retained. -/
theorem finiteCappedEulerProduct_eq (s : Finset Nat) (a : Nat -> Nat)
    (hs : forall p, Membership.mem s p -> 2 <= p) :
    chi.finiteCappedEulerProduct s a =
      chi.finiteEulerProduct s *
        s.prod (fun p => 1 - chi.eulerRatio p ^ (a p + 1)) := by
  unfold finiteCappedEulerProduct finiteEulerProduct
  rw [<- Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun p hp => chi.cappedLocalFactor_eq (hs p hp) (a p))

/-- Exact overflow identity. All cofactor mass is carried by the finite Euler
factor, rather than furnishing a separate source of cancellation. -/
theorem finiteCapOverflow_eq (s : Finset Nat) (a : Nat -> Nat)
    (hs : forall p, Membership.mem s p -> 2 <= p) :
    chi.finiteCapOverflow s a =
      chi.finiteEulerProduct s *
        (1 - s.prod (fun p => 1 - chi.eulerRatio p ^ (a p + 1))) := by
  rw [finiteCapOverflow, chi.finiteCappedEulerProduct_eq s a hs]
  ring

/-- Linearizing the overflow pays for every nonlinear cap interaction. -/
theorem finiteCapOverflow_linearization (s : Finset Nat) (a : Nat -> Nat)
    (hs : forall p, Membership.mem s p -> 2 <= p) :
    norm (chi.finiteCapOverflow s a -
      chi.finiteEulerProduct s * s.sum (fun p => chi.eulerRatio p ^ (a p + 1))) <=
        norm (chi.finiteEulerProduct s) * chi.capQuadraticMajorant s a := by
  rw [chi.finiteCapOverflow_eq s a hs, <- mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (Finset.norm_one_sub_prod_one_sub_sub_sum_le_quadratic s
      (fun p => chi.eulerRatio p ^ (a p + 1))) (norm_nonneg _)

/-- The exponent-one contribution is exactly a squared-character prime sum. -/
theorem capOne_sum_eq (s : Finset Nat) (a : Nat -> Nat) :
    (s.filter (fun p => a p = 1)).sum (fun p => chi.eulerRatio p ^ (a p + 1)) =
      (s.filter (fun p => a p = 1)).sum
        (fun p => chi (p : ZMod N) ^ 2 / (p : Complex) ^ 2) := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]
  simp only [eulerRatio, one_add_one_eq_two, div_pow]

/-- The complete complementary cap sum has an explicit reciprocal majorant.
For positive caps, this is precisely the higher-cap tail. -/
theorem norm_capComplement_sum_le (s : Finset Nat) (a : Nat -> Nat) :
    norm ((s.filter (fun p => Not (a p = 1))).sum
      (fun p => chi.eulerRatio p ^ (a p + 1))) <=
        (s.filter (fun p => Not (a p = 1))).sum
          (fun p => 1 / (p : Real) ^ (a p + 1)) :=
  (norm_sum_le _ _).trans
    (Finset.sum_le_sum (fun p _ => chi.norm_eulerRatio_pow_le p (a p + 1)))

/-- Separate the squared-character block from all higher-cap and nonlinear
terms without discarding the finite Euler factor. The complementary tail
also covers zero caps when they are present. -/
theorem finiteCapOverflow_primeSquare_remainder
    (s : Finset Nat) (a : Nat -> Nat)
    (hs : forall p, Membership.mem s p -> 2 <= p) :
    norm (chi.finiteCapOverflow s a - chi.finiteEulerProduct s *
      (s.filter (fun p => a p = 1)).sum
        (fun p => chi (p : ZMod N) ^ 2 / (p : Complex) ^ 2)) <=
      norm (chi.finiteEulerProduct s) *
        ((s.filter (fun p => Not (a p = 1))).sum
          (fun p => 1 / (p : Real) ^ (a p + 1)) + chi.capQuadraticMajorant s a) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun p => a p = 1)
    (fun p => chi.eulerRatio p ^ (a p + 1))
  have hdecomp :
      chi.finiteCapOverflow s a - chi.finiteEulerProduct s *
        (s.filter (fun p => a p = 1)).sum
          (fun p => chi (p : ZMod N) ^ 2 / (p : Complex) ^ 2) =
      chi.finiteEulerProduct s *
        (s.filter (fun p => Not (a p = 1))).sum
          (fun p => chi.eulerRatio p ^ (a p + 1)) +
      (chi.finiteCapOverflow s a - chi.finiteEulerProduct s *
        s.sum (fun p => chi.eulerRatio p ^ (a p + 1))) := by
    rw [<- chi.capOne_sum_eq s a, <- hsplit]
    ring
  rw [hdecomp]
  calc
    _ <= norm (chi.finiteEulerProduct s *
        (s.filter (fun p => Not (a p = 1))).sum
          (fun p => chi.eulerRatio p ^ (a p + 1))) +
        norm (chi.finiteCapOverflow s a - chi.finiteEulerProduct s *
          s.sum (fun p => chi.eulerRatio p ^ (a p + 1))) := norm_add_le _ _
    _ <= norm (chi.finiteEulerProduct s) *
        (s.filter (fun p => Not (a p = 1))).sum
          (fun p => 1 / (p : Real) ^ (a p + 1)) +
        norm (chi.finiteEulerProduct s) * chi.capQuadraticMajorant s a := by
      apply add_le_add
      next =>
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (chi.norm_capComplement_sum_le s a) (norm_nonneg _)
      next =>
        exact chi.finiteCapOverflow_linearization s a hs
    _ = _ := by ring

end DirichletCharacter
