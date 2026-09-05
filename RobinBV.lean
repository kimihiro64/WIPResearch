import RobinBV.CA.Definitions.Distribution
import RobinBV.CA.Helpers.LayerPartition
import RobinBV.Mathlib
import RobinBV.NumberField.Proof.CharacterChebyshevDecay
import RobinBV.NumberField.Proof.DirichletGRHCriterion
import RobinBV.NumberField.Proof.IdealCALocalThreshold
import RobinBV.NumberField.Proof.ImprimitiveEndpointAsymptotic
import RobinBV.NumberField.Proof.QuadraticDedekindNicolasOmega
import RobinBV.NumberField.Proof.QuadraticIdealNicolasAsymptoticTransfer
import RobinBV.NumberField.Proof.QuadraticPrimePowerLayers
import RobinBV.Sieve.Assembly.OwnerExpansionBV

/-!
# Public library root

This module exports the exploratory targets and their proved structural
reductions. The canonical quadratic Dedekind-zeta factorization is proved and
registered as a headline theorem. The library also proves the full complex
Dirichlet GRH/critical-integral equivalence, including the principal zeta
component, and the complete nonprincipal conductor correction with its
resonant leading term. No RH, ERH or GRH assertion is proved merely by these
equivalences.
-/
