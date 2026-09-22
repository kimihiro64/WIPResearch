/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
/-
# Prime-sieve facade

This facade exports the square-interval owner, density, and weighted sieve
modules used throughout the Legendre project.
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalBandCoverage
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalEvenEndpoint
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalFifthOptimization
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalGapNull
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalLogComparison
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalLogIncidence
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalOwnerPackets
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalPolynomialLoss
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalQuadraticMultiplier
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalRepeatedSuccessor
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalUnitFringeBoundary
import RobinBV.Mathlib.NumberTheory.PrimeSieve.Weighted

/-!
# Prime-sieve candidate facade

Exports the focused reusable ownership, progression and square-interval leaves.
This facade has no theorem bodies and introduces no project-specific dependency.
-/
