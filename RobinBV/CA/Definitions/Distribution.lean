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
  And (Membership.mem n.primeFactors P)
    (forall p, Membership.mem n.primeFactors p -> p <= P)

/-- Discrepancy of the reduced logarithmic exponent mass in one unit class. -/
noncomputable def reducedResidueDiscrepancy
    (n q : Nat) (a : Units (ZMod q)) : Real :=
  abs (logPrimeExponentMass n q (a : ZMod q) -
    reducedLogPrimeExponentMass n q / q.totient)

/-- Maximum reduced-residue discrepancy at modulus `q`. -/
noncomputable def maxReducedResidueDiscrepancy (n q : Nat) : Real :=
  iSup (fun a : Units (ZMod q) => reducedResidueDiscrepancy n q a)

/-- Average discrepancy through the cutoff `P ^ theta`. -/
noncomputable def averageReducedResidueDiscrepancy
    (n P : Nat) (theta : Real) : Real :=
  Finset.sum (Icc 1 (Nat.floor ((P : Real) ^ theta)))
    (fun q => maxReducedResidueDiscrepancy n q)

/--
Candidate Bombieri--Vinogradov range for CA logarithmic prime-exponent mass.

The endpoint `theta = 1/2` is deliberately excluded. This proposition does
not include, and therefore cannot silently assume, a bridge to Robin's
inequality or the Riemann hypothesis.
-/
def LogPrimeExponentDistribution : Prop :=
  forall theta : Real, 0 <= theta -> theta < 1 / 2 ->
    forall A : Real, 1 <= A ->
      exists C : Real, And (0 < C) (exists X : Nat,
        forall n P : Nat, forall eps : Real,
          Robin1984.IsColossallyAbundantWith n eps ->
          IsLargestPrimeFactor n P -> X <= P ->
          averageReducedResidueDiscrepancy n P theta <=
            C * P / Real.log P ^ A)

end RobinBV.CA
