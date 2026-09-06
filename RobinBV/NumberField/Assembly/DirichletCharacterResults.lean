import RobinBV.NumberField.Proof.CharacterChebyshevDecay
import RobinBV.NumberField.Proof.DirichletGRHCriterion
import RobinBV.NumberField.Proof.DirichletShiftedZeroMass
import RobinBV.NumberField.Proof.MovingCharacterBoundaryMean
import RobinBV.NumberField.Proof.MovingCharacterCenteredHierarchy
import RobinBV.NumberField.Proof.MovingCharacterHigherResonance
import RobinBV.NumberField.Proof.MovingCharacterQuartic
import RobinBV.NumberField.Proof.MovingCharacterRealCutoff
import RobinBV.NumberField.Proof.RiemannShiftedZeroMass

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
-/
