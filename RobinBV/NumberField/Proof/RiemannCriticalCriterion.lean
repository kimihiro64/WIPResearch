import RobinBV.NumberField.Proof.RiemannCriticalConverse

/-!
# The principal critical integral criterion

This combines the proved centered zeta-tail estimate with its oscillation
converse. The coefficient is the actual full xi zero mass, not an assumed RH
constant. The equivalence is a criterion for RH, not a proof of RH.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

/-- RH is equivalent to the exact-mass critical bound for the actual
centered Chebyshev tail. -/
theorem riemannHypothesis_iff_riemannCriticalBound :
    RiemannHypothesis <-> RiemannCriticalBound :=
  Iff.intro riemannCriticalBound_of_riemannHypothesis
    riemannHypothesis_of_riemannCriticalBound

end RobinBV.NumberField
