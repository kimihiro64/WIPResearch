import RobinBV.CA.Definitions.Distribution
import RobinBV.CA.Helpers.LayerPartition
import RobinBV.Mathlib
import RobinBV.NumberField.Definitions.QuadraticDedekindZeta
import RobinBV.NumberField.Definitions.RobinCriterion
import RobinBV.NumberField.Proof.CriticalCorrectionBridge
import RobinBV.NumberField.Proof.IdealAbundancyEulerProduct
import RobinBV.NumberField.Proof.IdealCALocalThreshold
import RobinBV.NumberField.Proof.IdealCAObjective
import RobinBV.NumberField.Proof.IdealDivisorEulerProduct
import RobinBV.NumberField.Proof.IdealEulerReserve
import RobinBV.NumberField.Proof.IdealLcmPacket
import RobinBV.NumberField.Proof.IdealNicolasTransfer
import RobinBV.NumberField.Proof.QuadraticDedekindERH
import RobinBV.NumberField.Proof.QuadraticDedekindPrimeSide
import RobinBV.NumberField.Proof.QuadraticPrimePowerTransfer
import RobinBV.NumberField.Proof.QuadraticPrimePowerLayers
import RobinBV.NumberField.Proof.QuadraticDedekindWeightedError
import RobinBV.NumberField.Proof.QuadraticDedekindZeroMass
import RobinBV.NumberField.Proof.QuadraticDedekindZeroSymmetry
import RobinBV.NumberField.Proof.QuadraticDedekindZetaZeros
import RobinBV.NumberField.Proof.QuadraticLZeroMassEvaluation

/-!
# Public library root

This module exports the exploratory targets and their proved structural
reductions. The canonical quadratic Dedekind-zeta factorization is proved and
registered as a headline theorem; the critical-scale Robin criterion remains
open.
-/
