/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.SelbergSieve.ReciprocalMass

/-!
# RadicalFiber

Finite Selberg sieve input, proved from Mathlib primitives.
The classical sieve argument follows D. R. Heath-Brown, Lectures on sieves,
Sections 2-3 (https://arxiv.org/abs/math/0209360).
No prime-distribution or unproved analytic hypothesis is introduced.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat

theorem reciprocal_totient_euler_identity (d : Nat) :
    (d : Real)^(-1 : Int) *
      d.primeFactors.prod (fun p => (1-(p : Real)^(-1 : Int))^(-1 : Int)) =
        (d.totient : Real)^(-1 : Int) := by
  have ht := congrArg (fun v : Rat => (v : Real)) (Nat.totient_eq_mul_prod_factors d)
  push_cast at ht
  rw [ht]
  simp only [zpow_neg_one, mul_inv, Finset.prod_inv_distrib]

/-- A finite multiple fiber whose cofactors use only prime divisors of d
has reciprocal mass at most1/phi(d). The cofactor injection is exact. -/
theorem sum_reciprocal_fiber_le_inv_totient (A : Finset Nat) (d : Nat)
    (hdiv : forall m, Membership.mem A m -> Dvd.dvd d m)
    (hsmooth : forall m, Membership.mem A m ->
      Membership.mem (Nat.factoredNumbers d.primeFactors) (m/d)) :
    A.sum (fun m => (m : Real)^(-1 : Int)) <= (d.totient : Real)^(-1 : Int) := by
  let B := A.image (fun m => m/d)
  have hinj : Set.InjOn (fun m => m/d) A := by
    intro m hm k hk he
    calc
      m = d*(m/d) := (Nat.mul_div_cancel' (hdiv m hm)).symm
      _ = d*(k/d) := congrArg (fun v => d*v) he
      _ = k := Nat.mul_div_cancel' (hdiv k hk)
  have hmass := sum_reciprocal_le_euler_product B d.primeFactors (by
    intro q hq
    choose m hm using Finset.mem_image.mp hq
    rw [<- hm.2]
    exact hsmooth m hm.1)
  have hfilter : d.primeFactors.filter Nat.Prime = d.primeFactors :=
    Finset.filter_eq_self.mpr (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [hfilter] at hmass
  have he : A.sum (fun m => (m : Real)^(-1 : Int)) =
      (d : Real)^(-1 : Int) * B.sum (fun m => (m : Real)^(-1 : Int)) := by
    dsimp [B]
    rw [Finset.mul_sum, Finset.sum_image]
    next =>
      apply Finset.sum_congr rfl
      intro m hm
      have hf : (d : Real)*((m/d : Nat) : Real) = (m : Real) := by
        exact_mod_cast Nat.mul_div_cancel' (hdiv m hm)
      calc
        (m : Real)^(-1 : Int) =
            ((d : Real)*((m/d : Nat) : Real))^(-1 : Int) :=
          congrArg (fun v : Real => v^(-1 : Int)) hf.symm
        _ = (d : Real)^(-1 : Int)*((m/d : Nat) : Real)^(-1 : Int) := by
          simp [mul_comm]
    next =>
      intro m hm k hk he
      exact hinj hm hk he
  calc
    A.sum (fun m => (m : Real)^(-1 : Int)) =
        (d : Real)^(-1 : Int) * B.sum (fun m => (m : Real)^(-1 : Int)) := he
    _ <= (d : Real)^(-1 : Int) *
        d.primeFactors.prod (fun p => (1-(p : Real)^(-1 : Int))^(-1 : Int)) :=
      _root_.mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (d.totient : Real)^(-1 : Int) := reciprocal_totient_euler_identity d

end Nat
