# CA Distribution and Quadratic Robin Criteria

[![CI](https://github.com/kimihiro64/robin-bv-explorations/actions/workflows/ci.yml/badge.svg)](https://github.com/kimihiro64/robin-bv-explorations/actions/workflows/ci.yml)

An exploratory Lean 4 research repository for distribution estimates on the logarithmic prime-exponent measure of colossally abundant numbers and Robin-type criteria for quadratic and abelian number fields.

## Problem

**Distribution of CA exponent mass and Robin criteria over number fields**

CA target: for every real theta with 0 <= theta < 1/2 and every real A >= 1, seek a constant C and a size threshold such that every sufficiently large colossally abundant N, with P its largest prime divisor, has total maximum reduced-residue-class discrepancy of the logarithmic measure sum_{p|N} v_p(N) log p through moduli q <= P^theta at most C P/(log P)^A, after primes dividing q are removed from the reference mass. Number-field target: for each fixed quadratic field K, determine whether ERH for zeta_K is equivalent to an eventual strict upper bound sigma_K(I) < exp(gamma) Res_{s=1}(zeta_K) Norm(I) log log Norm(I) for all sufficiently large nonzero integral ideals I, and identify the corrected constant or hypotheses if this candidate is false; then test the character-factorization mechanism for finite abelian extensions, including complex-valued character factors.

## Current status

This repository is in exploratory research mode. It currently contains:

- an exact Bombieri--Vinogradov-style target for CA logarithmic
  prime-exponent mass, with `theta < 1/2` and the reduced mass specified;
- a proved residue-class decomposition of that mass into the first prime layer
  and the repeated-prime-power remainder;
- a finite ideal-divisor sum and eventual Robin-bound schema for a fixed
  number field, with the Dedekind-zeta residue and ERH predicate still explicit
  inputs;
- a proved reverse analytic bridge: failure of quadratic Dedekind ERH forces
  an `OmegaMinus` excursion of the quadratic Dedekind Nicolas function at some
  exponent `0 < b < 1/2`, with separate nonreal-zero and signed real-zero
  arguments; and
- a quadratic-degree specialization that is deliberately a definition of the
  research target, not a claimed equivalence.

Neither headline theorem is proved. `Challenge.lean` and `Solution.lean`
currently expose only the proved quadratic Dedekind-zeta factorization.

## CA distribution route

For a CA integer `N`, each event `(p,j)` contributes `log p`; consequently the
mass at `p` is `v_p(N) log p`. The proved first split is

```text
CA exponent mass = first-layer prime mass + repeated-layer mass.
```

The intended analytic route has three independent hard steps:

1. prove from CA maximality that the first layer is exactly the initial prime
   segment through the largest prime factor `P`;
2. prove a uniform power-saving bound for the repeated layers, expected from
   the fact that layer `j >= 2` lives on prime scales substantially below `P`;
3. transfer the classical prime theorem to the logarithmically weighted first
   layer and combine it with the repeated-layer error for every fixed
   `theta < 1/2`.

This explains why the target is plausible and nontrivial. A crude higher-layer
bound of order `P^(1/2+o(1))`, summed over `P^theta` moduli, still gives a power
saving when `theta < 1/2`; it does not justify the endpoint.

## Quadratic and abelian field route

For a nonzero integral ideal `I`, the current definition uses

```text
sigma_K(I) = sum of Norm(J) over integral ideal divisors J of I.
```

The candidate normalization is

```text
sigma_K(I) < exp(gamma) * kappa_K * Norm(I) * log log Norm(I),
```

where `kappa_K` should ultimately be identified with the residue of
`zeta_K(s)` at `s = 1`. Before any equivalence can be claimed, the project must
prove the number-field maximal-order constant, formulate the zero statement,
and recover both directions of Robin's oscillation argument with ramified
prime ideals and the finite exceptional range accounted for.

A terminology point matters here: quadratic fields may be real or imaginary,
but their associated quadratic Dirichlet characters are real-valued. Genuinely
complex-valued character factors first enter the proposed extension to more
general finite abelian fields. That extension is a separate proof branch, not
an automatic consequence of the quadratic case.

## Audit of proposed consequences

The following implications were checked before being admitted to the proof
graph.

| Proposed impact | Status | What is actually missing |
| --- | --- | --- |
| A CA level of distribution at `theta >= 1/2` proves RH | **Not established** | An average congruence estimate does not by itself control the sign of Robin's scalar defect. A separate sign-sensitive transfer theorem would be needed. The present target excludes the endpoint. |
| The estimate eliminates all CA counterexamples to Robin | **Not established** | CA reduction identifies the relevant extremizers, but exclusion still requires a quantitative negative margin in Robin's inequality. |
| It proves the Alaoglu--Erdos consecutive-ratio conjecture | **Not established** | Aggregate distribution cannot exclude an exact coincidence of two marginal thresholds; that is the distinct transcendence obstruction in the classical conjecture. |
| It counts CA or superabundant numbers in short intervals | **Not established** | Distribution of mass inside one extremal integer gives no counting theorem for how often extremal integers occur. |
| It improves Cramer--Granville prime-gap bounds | **Not established** | Average distribution in residue classes is not a short-interval prime theorem. The CA first-layer threshold is `log(1+1/p)/log p`, not the proposed fractional part of `log(p+1)/log p`. |
| It may create a useful smooth-sifting interface | **Research possibility** | This becomes a theorem only after an explicit transfer from prime/smooth-number estimates to the CA event measure is proved. |

The source audit also found that [Pascadi's exponent-of-distribution paper](https://arxiv.org/abs/2505.00653)
concerns primes and smooth numbers in specific weighted settings, not CA
prime-exponent measures; [Lagarias's paper](https://arxiv.org/abs/math/0008177)
supports the classical Robin criterion but not the proposed distribution
bridge; and the cited Lucas-law congruence paper is unrelated to CA numbers,
sieve distribution, or Robin's inequality. The original
[Alaoglu--Erdos paper](https://users.renyi.hu/~p_erdos/1944-03.pdf) is the
relevant source for the consecutive-CA threshold problem.

## Local dependency boundary

The repository uses local path dependencies while it is exploratory:

- `Robin1984` at clean HEAD
  `2a74ac5c912cebf839bd3bf908249201eb62eb2d`;
- `bombieri-vinogradov` theorem-code checkpoint
  `380bc17efe7f63ad3e03921006cc520e3491225f`.

The successful local proof replay uses isolated object trees at those current
dependency revisions. The Bombieri--Vinogradov theorem-code checkpoint is
finished; its separate final Comparator replay does not change the theorem
dependency used here. A reproducible release must replace the local paths by
clean, reviewed commit pins and repeat every build and axiom audit.

The release state is visible mechanically:

- while `formalization.yaml` contains the canonical `TEMPLATE:` sentinels, CI
  validates the starter surface but the repository is not submission-ready;
- after the real metadata and Challenge/Solution surface replace every
  sentinel, CI enforces the ordinary Palomar metadata contract.

## Repository map

- `Challenge.lean` — small human-auditable statement surface.
- `Solution.lean` — corresponding proved declarations.
- `RobinBV/` — proof development.
- `RobinBV/Mathlib/` — project-independent, Mathlib-oriented
  candidate modules behind a mechanically enforced one-way import boundary.
- `MATHLIB_PORTING.md` — proposed upstream paths and readiness for reusable
  candidate modules.
- `SIBLING_CAPABILITIES.md` — declaration-level index of reusable results in
  known sibling formalizations and the exact revisions reviewed.
- `comparator.json` — exact Challenge/Solution declarations and axiom boundary.
- `formalization.yaml` — Palomar/community metadata, sources, fidelity, and
  review disclosure.
- `paper/` — public research paper source.
- `scripts/` — reproducible build, lint, experiment, certificate, and Palomar
  verification tools.
- `data/` — only reasonably sized data that is relevant and reproducible.

Local research context and AI working files are intentionally ignored and never
part of the public repository history.

## Reuse before reproof

Before developing a general result that is absent from the pinned Mathlib,
consult [`SIBLING_CAPABILITIES.md`](SIBLING_CAPABILITIES.md). It distinguishes
complete headline theorems from independently proved leaves in active projects
and names stable modules or declarations to inspect. Borrow only from an exact
published commit after checking its licence, hypotheses, imports, placeholders,
axiom surface, and toolchain; then record the source and attribution locally.

## Build and checks

Install Git, Python 3.11+, Ruby, and `elan`, then run:

```text
python scripts/check.py --profile research
```

That checks the public-file boundary, Lean source policy, Python formatting,
lint, strict typing, tests, Palomar metadata mode, Mathlib-candidate isolation,
and the Lean build.

Before release, run:

```text
python scripts/check.py --profile release
./scripts/verify-comparator.sh
```

The Comparator command requires a supported Linux host with Git, Go, Ruby,
Rust/Cargo, Python, and Landrun. GitHub CI runs the pinned verifier stack.
It pins the reviewed upstream `leanprover/lean4export` v4.33.0 source and
compiles that source unchanged with the generated repository's exact Lean
v4.33.1 toolchain via `ELAN_TOOLCHAIN`. This is the known-good Robin1984
Palomar configuration and keeps the exporter aligned with the repository's
`.olean` format without a fork or machine-local patch.

## Releases

`RELEASE_VERSION` contains the semantic version for the next completed
release. CI checks its format and tag collision before the long Lean build.
Research-mode repositories containing `TEMPLATE:` metadata never publish a
release. Once the real metadata and theorem surface are complete, a successful
`main` run publishes exactly three assets after every gate passes: the paper
PDF, a Linux `.lake/build` archive with project licensing, and an offline API
documentation ZIP with Lean and pinned-dependency notices. Reruns verify an
existing release at the same commit instead of duplicating it.

## Paper

The paper should state the exact mathematical result, its significance, source
relationship, proof architecture, formalization trust boundary, computation or
certificate coverage, limitations, automation disclosure, and actual review
status. Every theorem presented as proved must map to a kernel-checked Lean
declaration.

Its project-authored source and rendered PDF are dual-licensed under
Apache-2.0 or CC-BY-4.0, at the recipient's option. The repository's default
metadata licence remains Apache-2.0.

## Palomar

Development may begin in this public repository so GitHub CI is available from
the outset. Submit only after the full release profile passes at a clean commit,
that exact 40-character SHA is pushed, and the current
[Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
has been reviewed. Use the
[Palomar submission form](https://submit.palomar-registry.org/) only for the
verified commit.

A successful Lean build, Comparator check, NanoDa replay, or automated review
does not by itself establish novelty, source fidelity, mathematical
significance, or independent expert review.

## Licence

The repository's original material is licensed under
[Apache License 2.0](LICENSE) by default. The research paper is additionally
available under CC-BY-4.0, at the recipient's option. Mathematical provenance,
cited papers, supplied literature, dependencies, and generated archives are
covered by [LICENSING.md](LICENSING.md); this project does not claim ownership
of mathematical results or relicense third-party material.
