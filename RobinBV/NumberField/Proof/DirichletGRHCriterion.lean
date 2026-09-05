import RobinBV.NumberField.Proof.PrincipalCharacterAsymptotic
import RobinBV.NumberField.Proof.PrincipalCharacterZeros

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

/-- The complete family stated entirely with actual ambient tails: centered
principal integrals at every positive modulus and paired nonprincipal
integrals for every complex character. The quantifiers are fixed-level,
not a uniform claim for a modulus chosen as a function of the cutoff. -/
def FullCenteredDirichletCriticalBounds : Prop :=
  And (forall (N : Nat) [NeZero N], PrincipalCenteredCriticalBound N)
    (forall (N : Nat) [NeZero N] (chi : DirichletCharacter Complex N),
      letI : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
      Not (chi = 1) -> ImprimitivePairedDirichletCriticalBound chi)

/-- Full Dirichlet GRH is equivalent to the exact-mass critical family of
actual ambient integrals, including correctly centered principal tails. -/
theorem fullDirichletGRH_iff_centeredCriticalIntegralCriteria :
    FullDirichletGRH <-> FullCenteredDirichletCriticalBounds := by
  rw [fullDirichletGRH_iff_criticalIntegralCriteria]
  unfold FullDirichletCriticalBounds FullCenteredDirichletCriticalBounds
  apply and_congr _ Iff.rfl
  constructor
  next =>
    intro hBound N inst
    exact principalCenteredCriticalBound_iff_riemannCriticalBound.2 hBound
  next =>
    intro hBound
    exact (principalCenteredCriticalBound_iff_riemannCriticalBound (N := 1)).1 (hBound 1)

end

end RobinBV.NumberField
