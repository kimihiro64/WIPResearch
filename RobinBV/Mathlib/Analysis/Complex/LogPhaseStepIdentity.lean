/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LogPhaseCorrelationUniform
import RobinBV.Mathlib.Analysis.Complex.LogPhaseStepArithmetic

/-!
# D-spaced logarithmic phase identity

The exact phase product for two D-spaced shifts is transported to a single
log-difference packet.  Natural-index arithmetic is isolated from analytic
estimates.
-/

set_option autoImplicit false

namespace Complex

theorem log_phase_step_identity
    (Y P : Real) (j h k D : Nat) (horder : k < h) :
    logPhaseCorrelationTerm Y P j (h*D) (k*D) =
      exp (I * ((-Y *
        (Real.log (P + (k*D : Nat) + (j : Real) + ((h-k)*D : Nat)) -
          Real.log (P + (k*D : Nat) + (j : Real))) : Real) : Complex)) := by
  rw [show logPhaseCorrelationTerm Y P j (h*D) (k*D) =
      exp (I * ((-Y *
        (Real.log (P + (j + h*D : Nat)) -
          Real.log (P + (j + k*D : Nat))) : Real) : Complex)) by
    dsimp [logPhaseCorrelationTerm]
    exact log_phase_product_identity Y P j (h*D) (k*D)]
  congr 1
  rw [step_index_identity j h k D (Nat.le_of_lt horder)]
  push_cast
  ring

end Complex
