import RobinBV

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

theorem RobinBV.ca_mass_layer_decomposition (n q : Nat) (a : ZMod q) :
    RobinBV.CA.logPrimeExponentMass n q a =
      RobinBV.CA.firstLayerLogPrimeMass n q a +
        RobinBV.CA.repeatedLayerLogPrimeMass n q a := by
  exact RobinBV.CA.logPrimeExponentMass_eq_firstLayer_add_repeatedLayer n q a
