import RobinBV.CA.Definitions.ExponentMass

/-!
# First-layer and repeated-layer partition

This is the exact structural split needed before applying a theorem about
ordinary primes: the first layer is the prime-support term, while every extra
prime-power exponent is isolated in the repeated-layer remainder.
-/

namespace RobinBV.CA

open scoped BigOperators

/-- Residue-class exponent mass is the sum of its first and repeated layers. -/
theorem logPrimeExponentMass_eq_firstLayer_add_repeatedLayer
    (n q : Nat) (a : ZMod q) :
    logPrimeExponentMass n q a =
      firstLayerLogPrimeMass n q a + repeatedLayerLogPrimeMass n q a := by
  classical
  unfold logPrimeExponentMass firstLayerLogPrimeMass repeatedLayerLogPrimeMass
  rw [Finset.sum_filter_add_sum_filter_not]

end RobinBV.CA
