# Mathlib candidate layer

Reusable mathematics intended for possible upstreaming lives under
`RobinBV/Mathlib/` and is exported by `RobinBV/Mathlib.lean`.
The child generator replaces `RobinBV` with the configured project
namespace.

## Hard boundary

A Mathlib candidate module may import only:

- narrow `Mathlib.*`, `Batteries.*`, `Init.*`, `Lean.*`, or `Std.*` modules;
- another module inside the same `<Project>.Mathlib` candidate layer.

It may not import project definitions, helpers, proof branches, assembly,
`Challenge`, `Solution`, or a third-party project library. Its declarations
must use the namespace they would have after upstreaming, never the project's
namespace. The architecture audit enforces these dependency and namespace
rules.

## File and declaration standards

Each real candidate file should:

1. mirror its proposed Mathlib destination after the `<Project>/Mathlib/`
   prefix is removed;
2. use Mathlib's copyright, Apache-2.0 licence, author, module-documentation,
   declaration-documentation, naming, and formatting conventions;
3. state results at reusable generality without headline-theorem terminology;
4. use narrow, sorted, nonredundant imports and avoid project-only dependencies;
5. build independently before the project modules that consume it;
6. include focused regression examples or tests when behavior is not captured
   by a theorem statement alone;
7. contain no `sorry`, local axioms, discovery commands, or generated proof
   shortcuts.

## Candidate inventory

Replace the scaffold row when the first real candidate module is created.

| Project module | Proposed Mathlib path | Readiness | Upstream reference |
| --- | --- | --- | --- |
| `RobinBV.Mathlib.Analysis.Complex.ShiftedInverseSquare` | `Mathlib/Analysis/Complex/ShiftedInverseSquare.lean` | project-verified | Full critical-line shifted inverse-square mass comparison and exact real two-pole series identity for all real centers at least one; complete-series Cauchy-Schwarz refinement, including central points and arbitrary summable families |
| `RobinBV.Mathlib.NumberTheory.PrimePow.LogCutoff` | `Mathlib/NumberTheory/PrimePow/LogCutoff.lean` | project-verified | Exact real cutoff between consecutive integer powers, signed logarithmic gap and positive-power admission equivalence with floored real roots, including every equality transition |
| `RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimePowerCorrection` | `Mathlib/NumberTheory/DirichletCharacter/PrimePowerCorrection.lean` | project-verified | Exact finite Mangoldt conductor and lcm-level deletion identities, complete local geometric-log tail and full admitted-prefix norm bounds; pointwise conductor identity adapted from BombieriVinogradov at `1ed555f755ef71491890143de49f2f3fdb9d8c7e` (Apache-2.0), with no project import |
| `RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimeChebyshev` | `Mathlib/NumberTheory/DirichletCharacter/PrimeChebyshev.lean` | project-verified | Complete character-weighted psi-minus-theta domination and cutoff-independent finite conductor prime correction; all excluded primes and higher prime powers retained |
| `RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimePowerRemainder` | `Mathlib/NumberTheory/DirichletCharacter/PrimePowerRemainder.lean` | project-verified | Exact admitted-prefix, first-remaining-layer and capped root-prime moment identities; full higher-power root-log norm bound uniform in cap and character; elementary theta majorant for character prime sums |
| `RobinBV.Mathlib.NumberTheory.PrimePow.FiniteSum` | `Mathlib/NumberTheory/PrimePow/FiniteSum.lean` | project-verified | Complete unique-prime reindexing of arbitrary additive prime-power-supported weights meeting a modulus, with exact logarithmic exponent bounds and cutoff zero included |
| `RobinBV.Mathlib.NumberTheory.PrimePow.TotalSum` | `Mathlib/NumberTheory/PrimePow/TotalSum.lean` | project-verified | Complete prime-power-supported additive sums reindexed over every prime below the cutoff and all admitted positive exponents, including cutoff zero |
| `RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimePowerSquareRemainder` | `Mathlib/NumberTheory/DirichletCharacter/PrimePowerSquareRemainder.lean` | project-verified | Exact weighted Mangoldt decomposition into prime and squared-character root moments plus the entire higher-power remainder; uniform third-root logarithmic bound for every complex character |
| `RobinBV.Mathlib.Analysis.SpecialFunctions.Log.GeometricTail` | `Mathlib/Analysis/SpecialFunctions/Log/GeometricTail.lean` | project-verified | Exact shifted geometric-logarithm tail decomposition with a complete inverse-cutoff remainder bound and the resonant real sign; retains the position between consecutive powers |
| `RobinBV.Mathlib.Analysis.Complex.LogDerivContinuation` | `Mathlib/Analysis/Complex/LogDerivContinuation.lean` | project-verified | Holomorphic continuation of a logarithmic derivative on an open connected domain forces nonvanishing of a nontrivial analytic function; exact finite-order pole and analytic-identity proof, with no simple-zero assumption |
| `RobinBV.Mathlib.Analysis.MellinTail` | `Mathlib/Analysis/MellinTail.lean` | project-verified | Tail Mellin holomorphy from continuity on a positive closed tail and a power-decay bound, including zero-extension local integrability and absolute convergence with no artificial lower-strip restriction |
| `RobinBV.Mathlib.MeasureTheory.Integral.TailSwap` | `Mathlib/MeasureTheory/Integral/TailSwap.lean` | project-verified | Complete RCLike triangular Fubini from two L1 factors, with integrability conclusions and the exact primitive boundary term; generalizes Robin1984 TailReweight at published commit `2a74ac5c912cebf839bd3bf908249201eb62eb2d` (Apache-2.0) to complex derivative factors |
| `RobinBV.Mathlib.NumberTheory.DirichletCharacter.FiniteEulerProduct` | `Mathlib/NumberTheory/DirichletCharacter/FiniteEulerProduct.lean` | project-verified | Exact capped character Euler products, full overflow linearization, squared-character exponent-one block, and complete complementary-cap and nonlinear error bounds |
| `RobinBV.Mathlib.Analysis.Normed.Ring.FiniteProductRemainder` | `Mathlib/Analysis/Normed/Ring/FiniteProductRemainder.lean` | project-verified | Full linearization remainder for finite products in seminormed commutative rings; polynomial majorant and off-diagonal quadratic bound, with no smallness assumption |
| `RobinBV.Mathlib.Algebra.QuadraticAlgebra.Discriminant` | `Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean` | project-verified | Computes the discriminant of the canonical basis of a quadratic algebra, including the odd-discriminant integer specialization |
| `RobinBV.Mathlib.NumberTheory.NumberField.Ideal.Factorization` | `Mathlib/NumberTheory/NumberField/Ideal/Factorization.lean` | project-verified | Extends the distinct-factor calculation already used internally by `Ideal.quotientEquivPiFactors` |
| `RobinBV.Mathlib.NumberTheory.NumberField.QuadraticCharacter` | `Mathlib/NumberTheory/NumberField/QuadraticCharacter.lean` | project-verified | Constructs the primitive self-dual Jacobi character of an odd fundamental discriminant and proves its sign-dependent parity |
| `RobinBV.Mathlib.NumberTheory.NumberField.QuadraticDiscriminant` | `Mathlib/NumberTheory/NumberField/QuadraticDiscriminant.lean` | project-verified | Constructs the canonical quadratic field of an odd fundamental discriminant and proves that its signed number-field discriminant is the original parameter |
| `RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZeta` | `Mathlib/NumberTheory/NumberField/QuadraticZeta.lean` | project-verified | Constructs the canonical integral generator, proves its Kummer--Dedekind exponent is one, identifies its minimal polynomial, and proves the exact ideal-count coefficient at every odd rational prime |
| `RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaAtTwo` | `Mathlib/NumberTheory/NumberField/QuadraticZetaAtTwo.lean` | project-verified | Analyzes the canonical generator modulo two, proves the ideal-count coefficient at two, and combines it with the odd-prime formula |
| `RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaSplitting` | `Mathlib/NumberTheory/NumberField/QuadraticZetaSplitting.lean` | project-verified | Reconstructs prime-power norm ideals from exponent vectors and proves the exact split, ramified, and inert classification |
| `RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaPrimePowers` | `Mathlib/NumberTheory/NumberField/QuadraticZetaPrimePowers.lean` | project-verified | Counts splitting exponent vectors and proves the geometric-sum formula for every prime-power ideal-counting coefficient |
| `RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaFactorization` | `Mathlib/NumberTheory/NumberField/QuadraticZetaFactorization.lean` | project-verified | Counts ideals of every prime-power and positive norm, identifies the ideal-counting arithmetic function with the zeta-character convolution, and proves the quadratic Dedekind zeta factorization on `re(s) > 1` |

| `RobinBV.Mathlib.NumberTheory.PrimeSieve.Owner` | `Mathlib/NumberTheory/PrimeSieve/Owner.lean` | project-verified | Extracts the finite least-prime owner partition from original robin commit `b6a7dff5f9546131cf668a9c8bfa436f4650bc0d`; preserves arbitrary additive weights and full owner packets |
| `RobinBV.Mathlib.NumberTheory.PrimeSieve.InclusionExclusion` | `Mathlib/NumberTheory/PrimeSieve/InclusionExclusion.lean` | project-verified | Complete arbitrary-ring-weight prime-sieve and owner expansions over actual squarefree product moduli; includes the empty subset and every finite endpoint |
| `RobinBV.Mathlib.NumberTheory.PrimeSieve.OwnerModuli` | `Mathlib/NumberTheory/PrimeSieve/OwnerModuli.lean` | project-verified | A product modulus identifies its largest-prime owner and selected lower-prime subset uniquely; the complete prime-universe product bounds every branch modulus |
| `RobinBV.Mathlib.NumberTheory.PrimeSieve.Progression` | `Mathlib/NumberTheory/PrimeSieve/Progression.lean` | project-verified | Exact weighted owner-to-cofactor progression transport with gcd-adjusted modulus and a proved local obstruction for inadmissible classes |
| `RobinBV.Mathlib.NumberTheory.PrimeSieve.Scaled` | `Mathlib/NumberTheory/PrimeSieve/Scaled.lean` | project-verified | Exact dilation of an owner packet to its rough cofactors, including cofactor one and repeated owner-prime powers; same original robin revision |
| `RobinBV.Mathlib.NumberTheory.PrimeSieve.Weighted` | `Mathlib/NumberTheory/PrimeSieve/Weighted.lean` | project-verified | Generalizes the complete owner telescope from local density `1/p` to arbitrary `g(p)`; proves a complete future-weighted error budget and contraction for densities in `[0,1]` |

Readiness should be one of: `extracting`, `project-verified`, `mathlib-ready`,
`submitted`, or `upstreamed`. A module is `mathlib-ready` only after it has an
identified destination, no project dependency, focused tests, and a clean
standalone build against the project's pinned Mathlib revision.

## Least-prime owner source provenance

The `Owner`, `Scaled`, and `Weighted` modules extract only the project-independent closure of
`CF4ClockSieve`, `ExactLeastPrimeOwnerStage`,
`ExactLeastPrimeOwnerScaledTelescope`, and the complete recurrence in
`ExactLeastPrimeOwnerDefect` from the original `robin` repository at commit
`b6a7dff5f9546131cf668a9c8bfa436f4650bc0d`. The source file blobs were verified
against that commit and the source root toolchain matches Lean 4.33.1.
No original-repository import or dependency is added. The original code is
copyright 2026 Jonas Whidden under MIT; its full permission notice is retained
in each adapted module, which is distributed under Apache-2.0 for this
candidate layer. This is reuse plus a local-density generalization, not a
claim of a new classical Buchstab identity or an RH proof.
