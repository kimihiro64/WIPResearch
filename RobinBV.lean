import RobinBV.CA.Definitions.Distribution
import RobinBV.CA.Helpers.LayerPartition
import RobinBV.Mathlib
import RobinBV.NumberField.Proof.CharacterChebyshevDecay
import RobinBV.NumberField.Proof.DirichletGRHCriterion
import RobinBV.NumberField.Proof.IdealCALocalThreshold
import RobinBV.NumberField.Proof.MovingCharacterLevelBridge
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
component and every actual centered principal ambient tail. The complete
conductor corrections retain their resonant leading terms; the principal
secondary term has an exact signed residual identity and asymmetric bounds.
The full moving correction for every fixed complex Dirichlet character has
an unconditional principal-power coefficient at every positive integer power
scale. It is exactly the difference of actual centered character integrals
at the original and primorial-enlarged lcm levels. Its square-scale critical
shift is -2 for principal, -1 for nonprincipal quadratic, and zero for
higher-order characters. No RH, ERH or GRH assertion is proved merely by
these equivalences or correction estimates.
-/
