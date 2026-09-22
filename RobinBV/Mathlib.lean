/-
# RobinBV Mathlib facade

This facade exports the project-local analytic and arithmetic modules used by
the sieve and prime-interval developments.
-/

import RobinBV.Mathlib.Analysis.Complex.Core
import RobinBV.Mathlib.Analysis.Complex.LinnikVMVT
import RobinBV.Mathlib.Analysis.Complex.LogPhase
import RobinBV.Mathlib.Analysis.MellinTail
import RobinBV.Mathlib.Analysis.SpecificLimits.IntervalMeanOscillation
import RobinBV.Mathlib.MeasureTheory.Integral.TailSwap
import RobinBV.Mathlib.NumberTheory.BernoulliPeriodic
import RobinBV.Mathlib.NumberTheory.DirichletCharacter
import RobinBV.Mathlib.NumberTheory.LSeries
import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaFactorization
import RobinBV.Mathlib.NumberTheory.PrimeSieveBounds

/-!
# Mathlib candidate facade

This facade imports only reusable modules that are being maintained for eventual
upstreaming to Mathlib. Candidate source belongs under `RobinBV/Mathlib/`
and must remain independent of every project-specific definition, proof branch,
assembly module, and statement surface.

When a real candidate module is added, import it here and record its proposed
upstream path and readiness in `MATHLIB_PORTING.md`.
-/
