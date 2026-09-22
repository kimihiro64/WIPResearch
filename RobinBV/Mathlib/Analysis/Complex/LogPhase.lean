/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LogPhaseCorrelation
import RobinBV.Mathlib.Analysis.Complex.LogPhaseCorrelationUniform
import RobinBV.Mathlib.Analysis.Complex.LogPhaseStepArithmetic
import RobinBV.Mathlib.Analysis.Complex.LogPhaseStepForwardTransfer
import RobinBV.Mathlib.Analysis.Complex.LogPhaseStepVanDerCorput
import RobinBV.Mathlib.Analysis.Complex.LogPhaseTransfer
import RobinBV.Mathlib.Analysis.Complex.LogPhaseVanDerCorput

/-!
# Logarithmic phase candidate facade

This facade groups the exact correlation, transfer, and finite van der
Corput consumers for the logarithmic phase.
-/
