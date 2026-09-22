/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import RobinBV.Mathlib.Analysis.Complex.DifferenceSecondMoment

/-!
# Reflection mixed second moment

This is the verified mixed-moment expansion and Cauchy-Schwarz consumer used
by the almost-all reflection energy chain.
-/

set_option autoImplicit false

open ComplexConjugate

namespace Complex

noncomputable def finiteMixedDifferenceSecondMoment {I J K : Type*}
    (A : Finset I) (G : Finset J) (P : Finset K) (a : I -> Complex)
    (f : I -> Real) (H : J -> Real) (height : K -> Real) (v : Real) : Real :=
  G.sum (fun g => P.sum (fun p => norm (A.sum (fun n =>
    a n*exp (Complex.I*(f n : Complex)*((H g-height p+v : Real) : Complex))))^2))

private theorem mixed_phase_sum {J K : Type*} (G : Finset J) (P : Finset K)
    (H : J -> Real) (height : K -> Real) (d v : Real) :
    G.sum (fun g => P.sum (fun p =>
      exp (Complex.I*(d : Complex)*((H g-height p+v : Real) : Complex)))) =
      exp (Complex.I*(d : Complex)*(v : Complex))*
        G.sum (fun g => exp (Complex.I*(H g : Complex)*(d : Complex)))*
        conj (P.sum (fun p => exp (Complex.I*(height p : Complex)*(d : Complex)))) := by
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro g hg
  rw [<- exp_conj]
  have hc : conj (Complex.I*(height p : Complex)*(d : Complex)) =
      -Complex.I*(height p : Complex)*(d : Complex) := by simp
  rw [hc, <- exp_add, <- exp_add]
  congr 1
  push_cast
  ring

private theorem mixed_sum_four_comm {I J K : Type*}
    (A : Finset I) (G : Finset J) (P : Finset K) (z : J -> K -> I -> I -> Complex) :
    G.sum (fun g => P.sum (fun p => A.sum (fun i => A.sum (z g p i)))) =
      A.sum (fun i => A.sum (fun j => G.sum (fun g => P.sum (fun p => z g p i j)))) := by
  calc
    _ = G.sum (fun g => A.sum (fun i => P.sum (fun p => A.sum (z g p i)))) :=
      Finset.sum_congr rfl (fun g hg => Finset.sum_comm)
    _ = A.sum (fun i => G.sum (fun g => P.sum (fun p => A.sum (z g p i)))) :=
      Finset.sum_comm
    _ = A.sum (fun i => G.sum (fun g => A.sum (fun j => P.sum (fun p => z g p i j)))) :=
      Finset.sum_congr rfl (fun i hi =>
        Finset.sum_congr rfl (fun g hg => Finset.sum_comm))
    _ = _ := Finset.sum_congr rfl (fun i hi => Finset.sum_comm)

theorem finite_mixed_difference_second_moment_expansion {I J K : Type*}
    (A : Finset I) (G : Finset J) (P : Finset K) (a : I -> Complex)
    (f : I -> Real) (H : J -> Real) (height : K -> Real) (v : Real) :
    (finiteMixedDifferenceSecondMoment A G P a f H height v : Complex) =
      A.sum (fun i => A.sum (fun j =>
        (a i*conj (a j))*exp (Complex.I*((f i-f j : Real) : Complex)*(v : Complex))*
          G.sum (fun g => exp (Complex.I*(H g : Complex)*((f i-f j : Real) : Complex)))*
          conj (P.sum (fun p =>
            exp (Complex.I*(height p : Complex)*((f i-f j : Real) : Complex)))))) := by
  unfold finiteMixedDifferenceSecondMoment
  simp_rw [ofReal_sum, finite_fourier_norm_sq_expansion]
  rw [mixed_sum_four_comm A G P]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [<- Finset.mul_sum]
  rw [mixed_phase_sum]
  ring

theorem finite_mixed_difference_second_moment_sq_le {I J K : Type*}
    (A : Finset I) (G : Finset J) (P : Finset K) (a : I -> Complex)
    (f : I -> Real) (H : J -> Real) (height : K -> Real) (v : Real)
    (ha : forall n, Membership.mem A n -> norm (a n) <= 1) :
    (finiteMixedDifferenceSecondMoment A G P a f H height v)^2 <=
      finiteDifferenceSecondMoment A G (fun _ => 1) f H*
        finiteDifferenceSecondMoment A P (fun _ => 1) f height := by
  let KG : Real -> Complex := fun t => G.sum (fun g => exp (Complex.I*(H g : Complex)*(t : Complex)))
  let KP : Real -> Complex := fun t => P.sum (fun p => exp (Complex.I*(height p : Complex)*(t : Complex)))
  let term : I -> I -> Complex := fun i j =>
    (a i*conj (a j))*exp (Complex.I*((f i-f j : Real) : Complex)*(v : Complex))*
      KG (f i-f j)*conj (KP (f i-f j))
  let Q := finiteMixedDifferenceSecondMoment A G P a f H height v
  have hQ : 0 <= Q :=
    Finset.sum_nonneg (fun g hg => Finset.sum_nonneg (fun p hp => sq_nonneg _))
  have hterm (i : I) (hi : Membership.mem A i) (j : I) (hj : Membership.mem A j) :
      norm (term i j) <= norm (KG (f i-f j))*norm (KP (f i-f j)) := by
    have hc : norm (a i*conj (a j)) <= 1 := by
      rw [norm_mul, norm_conj]
      calc
        _ <= (1 : Real)*1 := mul_le_mul (ha i hi) (ha j hj) (norm_nonneg _) zero_le_one
        _ = _ := by ring
    change norm ((a i*conj (a j))*
      exp (Complex.I*((f i-f j : Real) : Complex)*(v : Complex))*
      KG (f i-f j)*conj (KP (f i-f j))) <= _
    rw [norm_mul, norm_mul, norm_mul, norm_conj, finite_fourier_phase_norm, mul_one]
    simpa only [mul_assoc, one_mul] using mul_le_mul_of_nonneg_right hc
      (mul_nonneg (norm_nonneg (KG (f i-f j))) (norm_nonneg (KP (f i-f j))))
  have hexp : (Q : Complex) = A.sum (fun i => A.sum (term i)) :=
    finite_mixed_difference_second_moment_expansion A G P a f H height v
  have hmajor : Q <= A.sum (fun i => A.sum (fun j =>
      norm (KG (f i-f j))*norm (KP (f i-f j)))) := by
    calc
      _ = norm (Q : Complex) := by rw [norm_real, Real.norm_of_nonneg hQ]
      _ = norm (A.sum (fun i => A.sum (term i))) := congrArg norm hexp
      _ <= A.sum (fun i => norm (A.sum (term i))) := norm_sum_le _ _
      _ <= A.sum (fun i => A.sum (fun j => norm (term i j))) :=
        Finset.sum_le_sum (fun i hi => norm_sum_le _ _)
      _ <= _ := Finset.sum_le_sum (fun i hi =>
        Finset.sum_le_sum (fun j hj => hterm i hi j hj))
  have hKG : finiteDifferenceSecondMoment A G (fun _ => 1) f H =
      A.sum (fun i => A.sum (fun j => norm (KG (f i-f j))^2)) := by
    rw [finite_difference_second_moment_eq_real_kernel]
    simp only [map_one, one_mul, one_re, KG]
  have hKP : finiteDifferenceSecondMoment A P (fun _ => 1) f height =
      A.sum (fun i => A.sum (fun j => norm (KP (f i-f j))^2)) := by
    rw [finite_difference_second_moment_eq_real_kernel]
    simp only [map_one, one_mul, one_re, KP]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (SProd.sprod A A : Finset (Prod I I))
    (fun p => norm (KG (f p.1-f p.2))) (fun p => norm (KP (f p.1-f p.2)))
  simp only [Finset.sum_product] at hcs
  rw [<- hKG, <- hKP] at hcs
  have hsq := mul_self_le_mul_self hQ hmajor
  calc
    _ <= (A.sum (fun i => A.sum (fun j =>
        norm (KG (f i-f j))*norm (KP (f i-f j)))))^2 := by
      simpa only [pow_two] using hsq
    _ <= _ := hcs

end Complex
