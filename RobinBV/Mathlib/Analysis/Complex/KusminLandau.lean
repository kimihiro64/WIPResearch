/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.InverseChord
import RobinBV.Mathlib.Analysis.Complex.VerticalAbel

/-!
# A finite first-derivative exponential-sum estimate

Decreasing separated angular increments give an explicit uniform finite sum bound.
These finite estimates do not assume a prime-distribution theorem.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Complex

/-- A finite first-derivative estimate for decreasing upper-semicircle increments. -/
theorem norm_sum_exp_le_of_antitone_increment (f : Nat -> Real) (N : Nat)
    {spacing : Real} (hspacing : 0 < spacing)
    (hpos : forall j, 0 < f (j+1)-f j)
    (hpi : forall j, f (j+1)-f j <= Real.pi)
    (hanti : Antitone (fun j => f (j+1)-f j))
    (hlower : forall j, j < N -> spacing <= f (j+1)-f j) :
    norm ((Finset.range N).sum (fun j => exp (I*(f j : Complex)))) <=
      3*Real.pi/spacing := by
  let u : Nat -> Complex := fun j => exp (I*(f j : Complex))
  let b : Nat -> Complex := fun j => inverseChordWeight (f (j+1)-f j)
  have hu (j : Nat) (_hj : j <= N) : norm (u j) <= 1 := by
    simp [u]
  have hb (j : Nat) (hj : j < N) : norm (b j) <= Real.pi/(2*spacing) := by
    calc
      _ <= Real.pi/(2*(f (j+1)-f j)) := norm_inverseChordWeight_le _ (hpos j) (hpi j)
      _ <= Real.pi/(2*spacing) := div_le_div_of_nonneg_left Real.pi_pos.le
        (by positivity) (by nlinarith only [hlower j hj])
  have hre (j : Nat) : (b j).re = (b 0).re := rfl
  have him : Antitone (fun j => (b j).im) := by
    intro i j hij
    exact inverseChordWeight_im_mono (hpos j) (hanti hij) (hpi i)
  have hmul (j : Nat) : b j*(u (j+1)-u j) = u j := by
    have he : I*(f (j+1) : Complex) =
        I*(f j : Complex)+I*((f (j+1)-f j : Real) : Complex) := by
      push_cast
      ring
    dsimp only [u, b]
    rw [he, exp_add]
    calc
      _ = exp (I*(f j : Complex)) *
          (inverseChordWeight (f (j+1)-f j) *
            (exp (I*((f (j+1)-f j : Real) : Complex))-1)) := by ring
      _ = exp (I*(f j : Complex)) := by
        rw [inverseChordWeight_mul_exp_sub_one _ (hpos j) (hpi j), mul_one]
  have h := norm_sum_mul_diff_le_vertical u b N
    (B := Real.pi/(2*spacing)) (by positivity) hu hb hre him
  simp_rw [hmul] at h
  have he : 6*(Real.pi/(2*spacing)) = 3*Real.pi/spacing := by ring
  rw [he] at h
  exact h

end Complex
