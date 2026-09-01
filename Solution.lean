import RobinBV

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

theorem RobinBV.ca_mass_layer_decomposition
    {alpha : Type*} [DecidableEq alpha]
    (events : Finset alpha) (layer : alpha -> Nat) (mass : alpha -> Real) :
    (∑ e ∈ events, mass e) =
      (∑ e ∈ events.filter (fun e => layer e = 1), mass e) +
        ∑ e ∈ events.filter (fun e => layer e ≠ 1), mass e := by
  rw [Finset.sum_filter_add_sum_filter_not]
