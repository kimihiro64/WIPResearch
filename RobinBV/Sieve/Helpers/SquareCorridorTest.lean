/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RobinBV.Sieve.Helpers.LogWindowTest
import RobinBV.Sieve.Helpers.SquareIntervalMovingWidth

/-!
# Inner and outer logarithmic corridor tests

These are affine versions of the existing smooth compactly supported profile.
The exact normalized arithmetic weight is retained.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

noncomputable def squareCorridorInnerTest (theta eta x : Real) : Real -> Complex :=
  scaledLogWindowTest eta ((1-2*theta)*movingSquareLogWidth x)
    (Real.log x+theta*movingSquareLogWidth x)

noncomputable def squareCorridorOuterTest (theta eta x : Real) : Real -> Complex :=
  scaledLogWindowTest eta ((1+2*theta)*movingSquareLogWidth x)
    (Real.log x-theta*movingSquareLogWidth x)

theorem scaledLogWindowTest_weight_eq {m : Nat} (hm : 0 < m)
    (eta L c : Real) :
    (scaledLogWindowTest eta L c (Real.log m)).re / Real.sqrt m =
      logWindowCutoff eta ((Real.log m-c)/L) := by
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  have he : Real.exp (Real.log (m : Real)/2) = Real.sqrt m := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hmR]
    congr 1
    ring
  have hcast : ((Real.log (m : Real) : Complex)/2) =
      ((Real.log (m : Real)/2 : Real) : Complex) := by
    push_cast
    rfl
  have hExp : Complex.exp ((Real.log (m : Real) : Complex)/2) =
      (Real.sqrt (m : Real) : Complex) := by
    rw [hcast, <- Complex.ofReal_exp, he]
  rw [scaledLogWindowTest, hExp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  field_simp [(Real.sqrt_pos.mpr hmR).ne']

end RobinBV.Sieve
