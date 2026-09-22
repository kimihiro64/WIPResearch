/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import RobinBV.Mathlib.Analysis.Complex.LogPhaseCorrelation

/-!
# Log-phase norm transfer with a stepped denominator

This finite consumer converts the proved log-difference estimate into the
uniform `1/(Y*D)` scale needed for D-spaced differencing, retaining explicit
window and denominator hypotheses.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Complex

theorem log_difference_norm_transfer
    (Y P Q : Real) (N L D : Nat) (hY : 0 < Y) (hP : 0 < P)
    (hL : 0 < L) (hD : 0 < D)
    (hsmall : Y * (L : Real) <= Real.pi * P^2)
    (hnum : P + (N : Real) + L + 1 <= Q)
    (hden : Y * (D : Real) <= Y * L) :
    norm ((Finset.range N).sum (fun j =>
      exp (I * ((-Y * (Real.log (P + (j : Real) + L) -
        Real.log (P + (j : Real))) : Real) : Complex)))) <=
      3 * Real.pi * Q^2 / (Y * D) := by
  have hc := norm_sum_exp_log_difference_le Y P N L hY hP hL hsmall
  have hnum' : 3 * Real.pi * (P + (N : Real) + L + 1)^2 <=
      3 * Real.pi * Q^2 := by
    gcongr
  calc
    _ <= 3 * Real.pi * (P + (N : Real) + L + 1)^2 /
        (Y * (L : Real)) := hc
    _ <= 3 * Real.pi * Q^2 / (Y * (L : Real)) :=
      div_le_div_of_nonneg_right hnum' (by positivity)
    _ <= 3 * Real.pi * Q^2 / (Y * (D : Real)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden

end Complex
