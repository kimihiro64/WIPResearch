/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# DualMobius

Finite Selberg sieve input, proved from Mathlib primitives.
The classical sieve argument follows D. R. Heath-Brown, Lectures on sieves,
Sections 2-3 (https://arxiv.org/abs/math/0209360).
No prime-distribution or unproved analytic hypothesis is introduced.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat

theorem divisor_complement_complement {P d : Nat} (hP : 0 < P) (hd : Dvd.dvd d P) :
    P/(P/d) = d := by
  have hd0 : 0 < d := by
    by_contra hh
    have hz : d = 0 := by omega
    choose c hc using hd
    simp only [hz, Nat.zero_mul] at hc
    omega
  have hpd : 0 < P/d := Nat.div_pos (Nat.le_of_dvd hP hd) hd0
  exact Nat.div_eq_of_eq_mul_left hpd (Nat.mul_div_cancel' hd).symm

/-- Complementing divisors turns an upper-divisor sum into an ordinary
divisor sum. The endpoints and divisibility constraints remain exact. -/
theorem sum_divisors_above_eq_complement {P d : Nat} (hP : 0 < P)
    (hd : Dvd.dvd d P) (f : Nat -> Real) :
    P.divisors.sum (fun e => if Dvd.dvd d e then f e else 0) =
      (P/d).divisors.sum (fun e => f (P/e)) := by
  have hP0 : Not (P = 0) := by omega
  calc
    P.divisors.sum (fun e => if Dvd.dvd d e then f e else 0) =
        P.divisors.sum (fun e => if Dvd.dvd d (P/e) then f (P/e) else 0) :=
      (Nat.sum_div_divisors P _).symm
    _ = P.divisors.sum (fun e => if Dvd.dvd e (P/d) then f (P/e) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      have hed := Nat.dvd_of_mem_divisors he
      have hiff : Dvd.dvd d (P/e) <-> Dvd.dvd e (P/d) := by
        rw [Nat.dvd_div_iff_mul_dvd hed, Nat.dvd_div_iff_mul_dvd hd, Nat.mul_comm d e]
      simp only [hiff]
    _ = (P/d).divisors.sum (fun e => f (P/e)) := by
      rw [<- Finset.sum_filter,
        Nat.divisors_filter_dvd_of_dvd hP0 (Nat.div_dvd_of_dvd hd)]

noncomputable def divisorMobiusTransform (f : Nat -> Real) (k : Nat) : Real :=
  k.divisorsAntidiagonal.sum (fun x => (ArithmeticFunction.moebius x.1 : Real)*f x.2)

theorem sum_divisorMobiusTransform (f : Nat -> Real) {k : Nat} (hk : 0 < k) :
    k.divisors.sum (fun d => divisorMobiusTransform f d) = f k := by
  exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := divisorMobiusTransform f) (g := f)).mpr (fun _ _ => rfl) k hk

noncomputable def upperDivisorMobius (P : Nat) (f : Nat -> Real) (d : Nat) : Real :=
  divisorMobiusTransform (fun k => f (P/k)) (P/d)

/-- Actual dual Mobius inversion, supplying the optimizer's prescribed
diagonal coefficients without an unproved analytic source hypothesis. -/
theorem sum_upperDivisorMobius {P d : Nat} (hP : 0 < P) (hd : Dvd.dvd d P)
    (f : Nat -> Real) :
    P.divisors.sum (fun e => if Dvd.dvd d e then upperDivisorMobius P f e else 0) =
      f d := by
  rw [sum_divisors_above_eq_complement hP hd]
  have hd0 : 0 < d := by
    by_contra hh
    have hz : d = 0 := by omega
    choose c hc using hd
    simp only [hz, Nat.zero_mul] at hc
    omega
  have hpd : 0 < P/d := Nat.div_pos (Nat.le_of_dvd hP hd) hd0
  calc
    (P/d).divisors.sum (fun e => upperDivisorMobius P f (P/e)) =
        (P/d).divisors.sum (fun e => divisorMobiusTransform (fun k => f (P/k)) e) := by
      apply Finset.sum_congr rfl
      intro e he
      have hed : Dvd.dvd e P := dvd_trans (Nat.dvd_of_mem_divisors he)
        (Nat.div_dvd_of_dvd hd)
      simp only [upperDivisorMobius, divisor_complement_complement hP hed]
    _ = f (P/(P/d)) := sum_divisorMobiusTransform (fun k => f (P/k)) hpd
    _ = f d := congrArg f (divisor_complement_complement hP hd)

end Nat
