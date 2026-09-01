import Robin1984.ColossallyAbundant.CAProfile

/-!
# Logarithmic prime-exponent mass

The factorization of an integer is viewed as a finite packet of prime-power
events. Each event at prime `p` carries mass `log p`, so the total mass at `p`
is exactly `v_p(n) log p`.
-/

namespace RobinBV.CA

open scoped BigOperators

/-- Logarithmic prime-exponent mass in one residue class modulo `q`. -/
noncomputable def logPrimeExponentMass (n q : Nat) (a : ZMod q) : Real :=
  ∑ e ∈ Robin1984.actualExponentEvents n,
    if (e.p : ZMod q) = a then Real.log (e.p : Real) else 0

/-- The part of the residue-class mass coming from the first exponent layer. -/
noncomputable def firstLayerLogPrimeMass (n q : Nat) (a : ZMod q) : Real :=
  ∑ e ∈ (Robin1984.actualExponentEvents n).filter (fun e => e.j = 1),
    if (e.p : ZMod q) = a then Real.log (e.p : Real) else 0

/-- The residue-class mass coming from exponent layers `j >= 2`. -/
noncomputable def repeatedLayerLogPrimeMass (n q : Nat) (a : ZMod q) : Real :=
  ∑ e ∈ (Robin1984.actualExponentEvents n).filter (fun e => e.j ≠ 1),
    if (e.p : ZMod q) = a then Real.log (e.p : Real) else 0

/-- Total logarithmic exponent mass after removing primes that divide `q`. -/
noncomputable def reducedLogPrimeExponentMass (n q : Nat) : Real :=
  ∑ e ∈ Robin1984.actualExponentEvents n,
    if e.p.Coprime q then Real.log (e.p : Real) else 0

end RobinBV.CA
