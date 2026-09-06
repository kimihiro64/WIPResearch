import RobinBV.NumberField.Proof.CharacterChebyshevDecay
import RobinBV.NumberField.Proof.MovingCharacterBoundaryCovariance
import RobinBV.NumberField.Proof.MovingCharacterCenteredHierarchy
import RobinBV.NumberField.Proof.MovingCharacterHigherResonance
import RobinBV.NumberField.Proof.MovingCharacterQuartic
import RobinBV.NumberField.Proof.MovingCharacterRealCutoff

/-!
# Dirichlet critical criteria and sharp moving-level corrections

Thin export assembly for the actual full Dirichlet GRH equivalence,
unconditional finite-moment and real-cutoff shifts, and the strict higher
secondary resonance hierarchy under the stated intervening-power ERH.
The exact-model extension includes every principal intermediate power.
At the doubled-layer boundary the full first-root Chebyshev contribution
is retained and the doubled arithmetic layer cancels exactly.
Its complete canonical zero-series leading term includes every parity,
conductor correction, central zero and multiplicity.
Complete kernel errors retain the shifted spectral mass, evaluated by the
actual completed-function logarithmic derivative under the stated RH/ERH.
The actual root zero series has logarithmic mean 2k/(k-1/2) times its
canonical central multiplicity. The principal xi central multiplicity is zero.
After full floor-clock and arithmetic error transfer, the actual centered
boundary residual has integer-cutoff logarithmic mean
2(m+1)/(m(m+1/2)) times the central multiplicity of chi^(m+1).
Its exact second moment is the complete canonical equal-zero pair mass
divided by m squared. All coincident-zero cross terms are retained;
the full-series bound and squared arithmetic-error transfer are derived.
The diagonal mass is evaluated by actual completed logarithmic derivatives
at zero and at the selected root index. The complete nonnegative repeated-zero
correction remains explicit. Subtracting the exact canonical central mean
gives the actual centered variance and its nonnegative real part.
For every principal character and every m>=1, RH implies strictly positive
actual second moment and arbitrarily late norm excursions at every smaller
squared amplitude. Thus the normalized principal residual does not tend to zero.
At every resonant layer chi^(m+1)=1, the complete profile differs from
the principal profile by a vanishing quantity, even for nonreal characters.
Full Dirichlet GRH supplies cofinal fixed sharp layers for every character.
Balanced finite resonant combinations cancel the entire leading fluctuation.
The actual principal residual is real at every cutoff; complete zero-series
control proves actual boundary boundedness. Zero mean and positive full
second moment then give recurrent excursions of both signs, without LI or
simple zeros. Resonant nonreal characters are asymptotically real and inherit
these two signed excursions. Full GRH gives cofinal fixed signed layers.
For arbitrary pairs of characters, positive moduli and fixed layers, the
complete conjugate-product mean is the canonical scaled-frequency pair sum
divided by the two layer indices. Every cross-family coincidence is retained.
Centering subtracts the product of the actual central-multiplicity means;
no zero-family independence, disjointness or moving-layer limit is assumed.
-/
