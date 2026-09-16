import RobinBV.Mathlib.Analysis.Complex.DirichletSegment
import RobinBV.Mathlib.Analysis.Complex.FourierBounds
import RobinBV.Mathlib.Analysis.Complex.LogDerivContinuation
import RobinBV.Mathlib.Analysis.Complex.ShiftedInverseSquare
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
