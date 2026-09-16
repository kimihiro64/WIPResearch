/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Coefficient majorants for finite difference sums

The complete squared Dirichlet-type sum over two finite height indices has
an exact expansion with a nonnegative frequency-difference kernel. This proves
Jutila's coefficient majorant inequality with constant one. A common height
shift is harmless after coefficient majorization. Nonnegative amplification
retains every equal-amplifier-index term on the full finite product support.

Frequencies and heights may repeat; no spacing or analytic density estimate
is assumed. These finite inequalities do not prove a zeta-zero energy bound.
The phase norm and single Fourier-sum expansion are retained unchanged from
FiniteFourierMoment, which now consumes this narrower algebraic source.
-/

set_option autoImplicit false

open ComplexConjugate

namespace Complex

theorem finite_fourier_phase_norm (d t : Real) :
    norm (exp (I*(d : Complex)*(t : Complex))) = 1 := by
  rw [show I*(d : Complex)*(t : Complex) = ((d*t : Real) : Complex)*I by
    push_cast
    ring]
  exact norm_exp_ofReal_mul_I (d*t)

theorem finite_fourier_norm_sq_expansion {v : Type*} (s : Finset v)
    (c : v -> Complex) (g : v -> Real) (t : Real) :
    ((norm (s.sum (fun i => c i * exp (I*(g i : Complex)*(t : Complex)))) ^ 2 : Real) :
        Complex) =
      s.sum (fun i => s.sum (fun j =>
        (c i * conj (c j)) * exp (I*((g i-g j : Real) : Complex)*(t : Complex)))) := by
  rw [ofReal_pow, <- mul_conj']
  rw [map_sum]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul, <- exp_conj]
  have he : conj (I*(g j : Complex)*(t : Complex)) =
      -(I*(g j : Complex)*(t : Complex)) := by simp
  rw [he]
  calc
    _ = (c i * conj (c j)) *
        (exp (I*(g i : Complex)*(t : Complex)) *
          exp (-(I*(g j : Complex)*(t : Complex)))) := by ring
    _ = _ := by
      rw [<- exp_add]
      congr 2
      push_cast
      ring

noncomputable def finiteDifferenceSecondMoment {v w : Type*}
    (A : Finset v) (G : Finset w) (a : v -> Complex)
    (frequency : v -> Real) (height : w -> Real) : Real :=
  G.sum (fun g => G.sum (fun h =>
    norm (A.sum (fun n => a n *
      exp (I*(frequency n : Complex)*((height g-height h : Real) : Complex))))^2))

private theorem sum_four_comm {v w : Type*} (A : Finset v) (G : Finset w)
    (f : w -> w -> v -> v -> Complex) :
    G.sum (fun g => G.sum (fun h => A.sum (fun i => A.sum (f g h i)))) =
      A.sum (fun i => A.sum (fun j => G.sum (fun g => G.sum (fun h => f g h i j)))) := by
  calc
    _ = G.sum (fun g => A.sum (fun i => G.sum (fun h => A.sum (f g h i)))) :=
      Finset.sum_congr rfl (fun g hg => Finset.sum_comm)
    _ = A.sum (fun i => G.sum (fun g => G.sum (fun h => A.sum (f g h i)))) :=
      Finset.sum_comm
    _ = A.sum (fun i => G.sum (fun g => A.sum (fun j => G.sum (fun h => f g h i j)))) :=
      Finset.sum_congr rfl (fun i hi =>
        Finset.sum_congr rfl (fun g hg => Finset.sum_comm))
    _ = _ := Finset.sum_congr rfl (fun i hi => Finset.sum_comm)

theorem sum_difference_phase_eq_norm_sq {w : Type*}
    (G : Finset w) (height : w -> Real) (d : Real) :
    G.sum (fun g => G.sum (fun h =>
      exp (I*(d : Complex)*((height g-height h : Real) : Complex)))) =
      ((norm (G.sum (fun g => exp (I*(height g : Complex)*(d : Complex))))^2 : Real) :
        Complex) := by
  have he (g h : w) :
      I*(d : Complex)*((height g-height h : Real) : Complex) =
        I*((height g-height h : Real) : Complex)*(d : Complex) := by ring
  simp_rw [he]
  symm
  simpa only [map_one, one_mul] using
    finite_fourier_norm_sq_expansion G (fun _ => 1) height d

theorem finite_difference_second_moment_expansion {v w : Type*}
    (A : Finset v) (G : Finset w) (a : v -> Complex)
    (frequency : v -> Real) (height : w -> Real) :
    (finiteDifferenceSecondMoment A G a frequency height : Complex) =
      A.sum (fun i => A.sum (fun j => (a i*conj (a j)) *
        ((norm (G.sum (fun g => exp (I*(height g : Complex)*
          ((frequency i-frequency j : Real) : Complex)))))^2 : Real))) := by
  unfold finiteDifferenceSecondMoment
  simp_rw [ofReal_sum, finite_fourier_norm_sq_expansion]
  rw [sum_four_comm A G]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [<- Finset.mul_sum]
  rw [sum_difference_phase_eq_norm_sq]

theorem finite_difference_second_moment_eq_real_kernel {v w : Type*}
    (A : Finset v) (G : Finset w) (a : v -> Complex)
    (frequency : v -> Real) (height : w -> Real) :
    finiteDifferenceSecondMoment A G a frequency height =
      A.sum (fun i => A.sum (fun j => (a i*conj (a j)).re *
        norm (G.sum (fun g => exp (I*(height g : Complex)*
          ((frequency i-frequency j : Real) : Complex))))^2)) := by
  have he := congrArg Complex.re
    (finite_difference_second_moment_expansion A G a frequency height)
  simpa only [ofReal_re, re_sum, mul_re, ofReal_im, mul_zero, sub_zero] using he

theorem finite_difference_second_moment_le_majorant {v w : Type*}
    (A : Finset v) (G : Finset w) (a : v -> Complex)
    (b frequency : v -> Real) (height : w -> Real)
    (hb : forall i, (A : Set v) i -> 0 <= b i)
    (ha : forall i, (A : Set v) i -> norm (a i) <= b i) :
    finiteDifferenceSecondMoment A G a frequency height <=
      finiteDifferenceSecondMoment A G (fun i => (b i : Complex)) frequency height := by
  rw [finite_difference_second_moment_eq_real_kernel,
    finite_difference_second_moment_eq_real_kernel]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  simp only [conj_ofReal, <- ofReal_mul, ofReal_re]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _ <= norm (a i*conj (a j)) := re_le_norm _
    _ = norm (a i)*norm (a j) := by rw [norm_mul, norm_conj]
    _ <= b i*b j := mul_le_mul (ha i hi) (ha j hj) (norm_nonneg _) (hb i hi)


theorem finite_difference_second_moment_shift_le {v w : Type*}
    (A : Finset v) (G : Finset w) (a : v -> Complex)
    (frequency : v -> Real) (height : w -> Real) (u : Real) :
    G.sum (fun g => G.sum (fun h => norm (A.sum (fun i =>
      a i*exp (I*(frequency i : Complex)*((height g-height h+u : Real) : Complex))))^2))
      <= finiteDifferenceSecondMoment A G
        (fun i => (norm (a i) : Complex)) frequency height := by
  have h := finite_difference_second_moment_le_majorant A G
    (fun i => a i*exp (I*(frequency i : Complex)*(u : Complex)))
    (fun i => norm (a i)) frequency height (fun i hi => norm_nonneg _)
    (fun i hi => by rw [norm_mul, finite_fourier_phase_norm, mul_one])
  unfold finiteDifferenceSecondMoment at h
  unfold finiteDifferenceSecondMoment
  convert h using 1
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro h hh
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  change a i*exp (I*(frequency i : Complex)*
      ((height g-height h+u : Real) : Complex)) =
    (a i*exp (I*(frequency i : Complex)*(u : Complex)))*
      exp (I*(frequency i : Complex)*((height g-height h : Real) : Complex))
  calc
    _ = a i*exp (I*(frequency i : Complex)*(u : Complex)+
        I*(frequency i : Complex)*((height g-height h : Real) : Complex)) := by
      congr 2
      push_cast
      ring
    _ = _ := by rw [exp_add]; ring

theorem finite_difference_second_moment_amplify_nonneg {v w z : Type*}
    (A : Finset v) (G : Finset w) (B : Finset z)
    (a frequency : v -> Real) (height : w -> Real)
    (b shift : z -> Real)
    (ha : forall i, (A : Set v) i -> 0 <= a i)
    (hb : forall p, (B : Set z) p -> 0 <= b p) :
    B.sum (fun p => b p^2) *
        finiteDifferenceSecondMoment A G (fun i => (a i : Complex)) frequency height <=
      finiteDifferenceSecondMoment (SProd.sprod A B : Finset (Prod v z)) G
        (fun ip => ((a ip.1*b ip.2 : Real) : Complex))
        (fun ip => frequency ip.1+shift ip.2) height := by
  rw [finite_difference_second_moment_eq_real_kernel,
    finite_difference_second_moment_eq_real_kernel]
  simp only [Finset.sum_product, conj_ofReal, <- ofReal_mul, ofReal_re]
  let K : Real -> Real := fun d =>
    norm (G.sum (fun g => exp (I*(height g : Complex)*(d : Complex))))^2
  change B.sum (fun p => b p^2) *
      A.sum (fun i => A.sum (fun j => a i*a j*K (frequency i-frequency j))) <=
    A.sum (fun i => B.sum (fun p => A.sum (fun j => B.sum (fun q =>
      (a i*b p)*(a j*b q)*K (frequency i+shift p-(frequency j+shift q))))))
  calc
    _ = B.sum (fun p => A.sum (fun i => A.sum (fun j =>
        b p^2*(a i*a j*K (frequency i-frequency j))))) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ = A.sum (fun i => B.sum (fun p => A.sum (fun j =>
        b p^2*(a i*a j*K (frequency i-frequency j))))) := Finset.sum_comm
    _ = A.sum (fun i => B.sum (fun p => A.sum (fun j =>
        (a i*b p)*(a j*b p)*K (frequency i+shift p-(frequency j+shift p))))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro j hj
      rw [show frequency i+shift p-(frequency j+shift p) =
        frequency i-frequency j by ring]
      ring
    _ <= _ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.single_le_sum
        (f := fun q => (a i*b p)*(a j*b q)*
          K (frequency i+shift p-(frequency j+shift q))) _ hp
      intro q hq
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (ha i hi) (hb p hp))
          (mul_nonneg (ha j hj) (hb q hq)))
        (sq_nonneg _)

theorem finite_difference_second_moment_amplify {v w z : Type*}
    (A : Finset v) (G : Finset w) (B : Finset z)
    (a : v -> Complex) (frequency : v -> Real) (height : w -> Real)
    (b shift : z -> Real)
    (hb : forall p, (B : Set z) p -> 0 <= b p) :
    B.sum (fun p => b p^2) * finiteDifferenceSecondMoment A G a frequency height <=
      finiteDifferenceSecondMoment (SProd.sprod A B : Finset (Prod v z)) G
        (fun ip => ((norm (a ip.1)*b ip.2 : Real) : Complex))
        (fun ip => frequency ip.1+shift ip.2) height := by
  have hm := finite_difference_second_moment_le_majorant A G a
    (fun i => norm (a i)) frequency height
    (fun i hi => norm_nonneg _) (fun i hi => le_rfl)
  exact (mul_le_mul_of_nonneg_left hm
    (Finset.sum_nonneg (fun p hp => sq_nonneg _))).trans
      (finite_difference_second_moment_amplify_nonneg A G B
        (fun i => norm (a i)) frequency height b shift
        (fun i hi => norm_nonneg _) hb)

end Complex
