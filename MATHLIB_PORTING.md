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
| `RobinBV.Mathlib.NumberTheory.NumberField.Ideal.Factorization` | `Mathlib/NumberTheory/NumberField/Ideal/Factorization.lean` | project-verified | Extends the distinct-factor calculation already used internally by `Ideal.quotientEquivPiFactors` |
| `RobinBV.Mathlib.NumberTheory.NumberField.QuadraticCharacter` | `Mathlib/NumberTheory/NumberField/QuadraticCharacter.lean` | project-verified | Constructs the primitive self-dual Jacobi character of an odd fundamental discriminant and proves its sign-dependent parity |

Readiness should be one of: `extracting`, `project-verified`, `mathlib-ready`,
`submitted`, or `upstreamed`. A module is `mathlib-ready` only after it has an
identified destination, no project dependency, focused tests, and a clean
standalone build against the project's pinned Mathlib revision.
