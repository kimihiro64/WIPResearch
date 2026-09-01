import BombieriVinogradov.Definitions.Statement
import RobinBV.CA.Definitions.ExponentMass

/-!
# CA logarithmic-mass level of distribution

This module states the research target. It is a definition of a proposition,
not a theorem claimed by the project.
-/

namespace RobinBV.CA

open Finset Nat Real

/-- `P` is the largest prime divisor of `n`. -/
def IsLargestPrimeFactor (n P : Nat) : Prop :=
  P ∈ n.primeFactors ∧ ∀ p ∈ n.primeFactors, p ≤ P

/-- Discrepancy of the reduced logarithmic exponent mass in one unit class. -/
noncomputable def reducedResidueDiscrepancy
    (n q : Nat) (a : (ZMod q)ˣ) : Real :=
  |logPrimeExponentMass n q (a : ZMod q) -
    reducedLogPrimeExponentMass n q / q.totient|

/-- Maximum reduced-residue discrepancy at modulus `q`. -/
noncomputable def maxReducedResidueDiscrepancy (n q : Nat) : Real :=
  ⨆ a : (ZMod q)ˣ, reducedResidueDiscrepancy n q a

/-- Average discrepancy through the cutoff `P ^ theta`. -/
noncomputable def averageReducedResidueDiscrepancy
    (n P : Nat) (theta : Real) : Real :=
  ∑ q ∈ Icc 1 ⌊(P : Real) ^ theta⌋₊,
    maxReducedResidueDiscrepancy n q

/--
Candidate Bombieri--Vinogradov range for CA logarithmic prime-exponent mass.

The endpoint `theta = 1/2` is deliberately excluded. This proposition does
not include, and therefore cannot silently assume, a bridge to Robin's
inequality or the Riemann hypothesis.
-/
def LogPrimeExponentDistribution : Prop :=
  ∀ theta : Real, 0 ≤ theta → theta < 1 / 2 →
    ∀ A : Real, 1 ≤ A →
      ∃ C : Real, 0 < C ∧ ∃ X : Nat,
        ∀ n P : Nat, ∀ eps : Real,
          Robin1984.IsColossallyAbundantWith n eps →
          IsLargestPrimeFactor n P → X ≤ P →
          averageReducedResidueDiscrepancy n P theta ≤
            C * P / Real.log P ^ A

end RobinBV.CA
