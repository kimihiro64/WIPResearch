import RobinBV.CA.Definitions.ExponentMass

/-!
# CA exponent-mass layer decomposition

The first public result separates the ordinary prime-support layer from the
repeated prime-power remainder, residue class by residue class.
-/

namespace RobinBV

/-- The logarithmic exponent mass splits exactly into first and repeated layers. -/
theorem ca_mass_layer_decomposition (n q : Nat) (a : ZMod q) :
    CA.logPrimeExponentMass n q a =
      CA.firstLayerLogPrimeMass n q a + CA.repeatedLayerLogPrimeMass n q a := by
  classical
  unfold CA.logPrimeExponentMass CA.firstLayerLogPrimeMass
    CA.repeatedLayerLogPrimeMass
  rw [Finset.sum_filter_add_sum_filter_not]

end RobinBV
