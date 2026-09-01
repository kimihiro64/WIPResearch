import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Finite mass layer decomposition

This Mathlib-only statement is the abstract finite partition used by the CA
prime-exponent decomposition. The project-specific event model and its
application remain behind `Solution.lean`.
-/

namespace RobinBV

/-- A finite mass splits exactly into layer one and all remaining layers. -/
theorem ca_mass_layer_decomposition
    {alpha : Type*} [DecidableEq alpha]
    (events : Finset alpha) (layer : alpha -> Nat) (mass : alpha -> Real) :
    (∑ e ∈ events, mass e) =
      (∑ e ∈ events.filter (fun e => layer e = 1), mass e) +
        ∑ e ∈ events.filter (fun e => layer e ≠ 1), mass e := by
  sorry

end RobinBV
