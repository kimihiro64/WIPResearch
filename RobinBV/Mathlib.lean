import RobinBV.Mathlib.Analysis.Complex.LogDerivContinuation
import RobinBV.Mathlib.Analysis.MellinTail
import RobinBV.Mathlib.Analysis.SpecialFunctions.Log.GeometricTail
import RobinBV.Mathlib.MeasureTheory.Integral.TailSwap
import RobinBV.Mathlib.NumberTheory.DirichletCharacter.FiniteEulerProduct
import RobinBV.Mathlib.NumberTheory.NumberField.Ideal.Factorization
import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZeta
import RobinBV.Mathlib.NumberTheory.NumberField.QuadraticZetaFactorization
import RobinBV.Mathlib.NumberTheory.PrimeSieve.InclusionExclusion
import RobinBV.Mathlib.NumberTheory.PrimeSieve.OwnerModuli
import RobinBV.Mathlib.NumberTheory.PrimeSieve.Progression
import RobinBV.Mathlib.NumberTheory.PrimeSieve.Weighted

/-!
# Mathlib candidate facade

This facade imports only reusable modules that are being maintained for eventual
upstreaming to Mathlib. Candidate source belongs under `RobinBV/Mathlib/`
and must remain independent of every project-specific definition, proof branch,
assembly module, and statement surface.

When a real candidate module is added, import it here and record its proposed
upstream path and readiness in `MATHLIB_PORTING.md`.
-/
