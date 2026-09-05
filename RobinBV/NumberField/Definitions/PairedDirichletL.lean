import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import RobinBV.NumberField.Definitions.QuadraticLZeros

/-!
# Paired Dirichlet completed L-function

This module defines the dual-character product of symmetric completed
Dirichlet L-functions and its critical-line assertion.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz

noncomputable section

/-- The dual-character entire carrier. Its two factors correspond to a
character and its inverse. -/
noncomputable def pairedDirichletZeroCarrier
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (s : Complex) : Complex :=
  symmetricCompletedLFunction chi s *
    symmetricCompletedLFunction (Inv.inv chi) s

/-- The critical-line assertion for every zero of the paired carrier in
the open critical strip. -/
def PairedDirichletERH
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) : Prop :=
  forall rho : Complex,
    pairedDirichletZeroCarrier chi rho = 0 ->
      0 < rho.re -> rho.re < 1 -> rho.re = 1 / 2

end

end RobinBV.NumberField
