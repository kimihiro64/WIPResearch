import RobinBV.NumberField.Proof.ImprimitiveCriticalCriterion
import RobinBV.NumberField.Proof.PrincipalCharacterZeros
import RobinBV.NumberField.Proof.RiemannCriticalCriterion

/-!
# A critical integral criterion for full Dirichlet GRH

The hypothesis quantifies over every complex Dirichlet character at every
positive modulus, including principal and imprimitive characters. Its
equivalent integral family uses the centered zeta tail for the common
principal factor and the actual paired ambient integral for each nonprincipal
character. Each cutoff may depend on the character and on epsilon; no uniform
conductor estimate is asserted. This does not address arbitrary automorphic
L-functions or prove GRH.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

noncomputable section

/-- GRH for all actual complex Dirichlet L-functions, with no primitive,
parity, reality or nonprincipality restriction. -/
def FullDirichletGRH : Prop :=
  forall (N : Nat) [NeZero N] (chi : DirichletCharacter Complex N), DirichletERH chi

/-- The complete critical integral family: the centered principal zeta tail
and the paired ambient tail of every nonprincipal complex character. The
positive conductor instance is proved, not an extra mathematical assumption. -/
def FullDirichletCriticalBounds : Prop :=
  And RiemannCriticalBound
    (forall (N : Nat) [NeZero N] (chi : DirichletCharacter Complex N),
      letI : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
      Not (chi = 1) -> ImprimitivePairedDirichletCriticalBound chi)

/-- Full Dirichlet GRH is equivalent to the complete exact-mass critical
integral family. All principal characters are handled by their proved zeta
zero bridge, not by omitting them from the universal quantifier. -/
theorem fullDirichletGRH_iff_criticalIntegralCriteria :
    FullDirichletGRH <-> FullDirichletCriticalBounds := by
  constructor
  next =>
    intro hGRH
    have hRH : RiemannHypothesis :=
      (dirichletERH_principal_iff_riemannHypothesis (N := 1)).1 (hGRH 1 1)
    refine And.intro (riemannHypothesis_iff_riemannCriticalBound.1 hRH) ?_
    intro N inst chi
    let : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
    intro hchi
    exact (dirichletERH_iff_imprimitivePairedCriticalBound chi hchi).1 (hGRH N chi)
  next =>
    intro hBounds N inst chi
    by_cases hchi : chi = 1
    case pos =>
      subst chi
      exact (dirichletERH_principal_iff_riemannHypothesis (N := N)).2
        (riemannHypothesis_iff_riemannCriticalBound.2 hBounds.1)
    case neg =>
      let : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
      exact (dirichletERH_iff_imprimitivePairedCriticalBound chi hchi).2
        (hBounds.2 N chi hchi)

end

end RobinBV.NumberField
