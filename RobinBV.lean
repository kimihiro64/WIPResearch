import RobinBV.CA.Definitions.Distribution
import RobinBV.CA.Helpers.LayerPartition
import RobinBV.Mathlib
import RobinBV.NumberField.Assembly.DirichletCharacterResults
import RobinBV.NumberField.Proof.IdealCALocalThreshold
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
scale and at arbitrary real square-root cutoffs. It is exactly the difference of actual centered character integrals
at the original and primorial-enlarged lcm levels. Its square-scale critical
shift is -2 for principal, -1 for nonprincipal quadratic, and zero for
higher-order characters. After retaining the first m finite prime moments
exactly, the first omitted layer has coefficient -(m+1)/m^2 at scale
P^(m^2/(m+1))*log(P) precisely when the (m+1)-st character power is
principal, and zero otherwise. Every higher layer and the full cap error
are proved negligible at this scale. Under ERH of a nonprincipal cubic
character power, a further quartic term has coefficient -2/3 at scale
P^(3/2)*log(P) when the fourth power is principal, and zero otherwise.
Its full higher-weight and root-prime ERH estimates cover both parities
and imprimitive characters. More generally, for m+1 <= L < 2*(m+1),
assuming nonprincipality and ERH for precisely the intervening powers,
the exact-prefix residual has coefficient -L/(m*(L-1)) at scale
P^(m*(L-1)/L)*log(P) when the L-th power is principal, and zero
otherwise. This includes the actual centered integral difference and
accounts for every cap correction and the complete higher-power tail.
Retaining the complete model integrals of earlier principal powers
removes the intermediate nonprincipality restriction: ERH of those
powers alone gives the same selected coefficient. Its principal input
is proved from Robin's full rational higher-weight bounds under RH,
with complete prime-power and conductor corrections.
At L=2*(m+1), the doubled arithmetic layer cancels against the first
root's prime-power correction. Retaining the entire first-root Chebyshev
tail yields a vanishing normalized residual, with ERH needed only for
the strictly later intervening powers. No constant or sign is assigned
to the retained first-root contribution.
No RH, ERH or GRH assertion is proved merely
by these equivalences or conditional correction estimates.
-/
