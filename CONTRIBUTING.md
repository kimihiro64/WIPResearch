# Contributing

Keep contributions mathematically focused, source-faithful, reproducible, and
reviewable.

## Proof source

- Do not add project-local axioms, `admit`, `native_decide`, bodyless constants,
  opaque proof shortcuts, or `sorry` outside the deliberate Challenge statement
  surface.
- Preserve exact quantifiers and hypotheses. Numerical work may verify a proved
  finite remainder; it may not replace an arbitrary parameter.
- Prefer small modules with narrow, sorted, nonredundant imports.
- Keep `#check`, `#print`, `#eval`, `#reduce`, tactic suggestions, and other
  discovery commands out of committed proof modules.
- Document the mathematical content and proof role of every owned module.

## Mathlib candidates

Put project-independent results with plausible upstream value under
`<ProjectNamespace>/Mathlib/`, export them from
`<ProjectNamespace>/Mathlib.lean`, and update `MATHLIB_PORTING.md`. Paths below
that directory should mirror the proposed Mathlib destination. Candidate files
use their eventual upstream namespace and Mathlib's source, documentation,
naming, formatting, testing, and licence conventions.

Candidate modules may import only narrow Mathlib/Core modules or other
candidates. They may not import the project's definitions, helpers, proof
branches, assembly, Challenge/Solution, or third-party project libraries. Run
the architecture audit and build each candidate before its first project
consumer.

## Sibling reuse

Before reproving a general lemma that is absent from the pinned Mathlib, check
`SIBLING_CAPABILITIES.md`. Treat it as a discovery index, not a proof or
compatibility guarantee. Open the named declaration at an exact published
commit; audit its statement, licence, toolchain, direct and transitive imports,
placeholders, and axioms; and record the repository, full SHA, original name,
renaming, and attribution in this project. Prefer an existing sibling Mathlib
candidate. Otherwise extract only the minimum project-independent closure into
this project's candidate layer or pin the sibling dependency explicitly.

## Python and experiments

Public Python must be reproducible, typed, formatted, lint-clean, and tested.
Record the tested statement, parameter domain, worst case or first
counterexample, and code revision. Commit experiment data only when it is
reasonably sized, relevant to the mathematical account, and documented with its
generator and meaning.

## Public boundary

Never stage local research state or AI working files. `python scripts/check.py`
audits the Git index, but contributors must also review `git status` before a
commit. The prohibited roots include `.agents/`, `.research/`, `.codex/`,
`AGENTS.md`, and `PLANS.md`.

## Verification

Run the research profile before opening a pull request. Release work additionally
requires the full Palomar profile, paper, Comparator, NanoDa, clean Git state,
and exact public commit audit.

## Licence

Contributions are accepted under the repository's Apache-2.0 licence unless
explicitly agreed and marked otherwise. Preserve applicable third-party
notices and submit only material you are authorized to license. The paper's
additional CC-BY-4.0 option and generated-distribution scope are documented in
[LICENSING.md](LICENSING.md).
