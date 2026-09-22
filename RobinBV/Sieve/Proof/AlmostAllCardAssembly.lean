/- Copyright (c) 2026 Jonas Whidden. -/
import RobinBV.Sieve.Assembly.SquareCorridorMomentCost

/-!
# Almost-all cardinality assembly

The final elementary conversion from an ENNReal fourth-moment cost to a
cardinality bound is isolated here for direct use by the exceptional-block
consumer.
-/

set_option autoImplicit false

open MeasureTheory

theorem almost_all_card_from_ennreal_cost
    {m : Nat} {k B : Real} {M : ENNReal}
    (hk : 0 < k) (hB : 0 <= B) (hcost : ENNReal.ofReal ((m : Real)*k) <= M)
    (hmoment : M <= ENNReal.ofReal B) :
    (m : Real) <= B/k := by
  have hmk : 0 <= (m : Real)*k := mul_nonneg (Nat.cast_nonneg m) hk.le
  have hchain : ENNReal.ofReal ((m : Real)*k) <= ENNReal.ofReal B :=
    hcost.trans hmoment
  have hle : (m : Real)*k <= B := by
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp hchain
  have hdiv : (B/k)*k = B := by
    field_simp
  apply le_of_mul_le_mul_right _ hk
  nlinarith
