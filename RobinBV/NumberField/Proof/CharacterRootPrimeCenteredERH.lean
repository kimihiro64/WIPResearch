import RobinBV.NumberField.Proof.PrincipalCharacterZeros
import RobinBV.NumberField.Proof.PrincipalRootPrimeERH

/-!
# Complete model-centered root-prime decay for every character

The principal case uses the actual equivalence between principal ERH and
RH; the nonprincipal case uses the full primitive/imprimitive ERH estimate.
No parity, primitivity or nonprincipality restriction remains.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

/-- ERH gives a complete model-centered root-prime estimate for every
complex character of positive modulus, above the half-root exponent. -/
theorem rootPrimeCharacterTail_centered_scaled_tendsto_of_ERH
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) {s : Real} (hs : 1 / 2 < (k : Real) * s) :
    Tendsto (fun x : Real => ((x ^ (1 - s) * Real.log x : Real) : Complex) *
      (rootPrimeCharacterTail chi (Inv.inv (k : Real)) x -
        (if chi = 1 then (1 : Complex) else 0) *
          ((integral (volume.restrict (Ioi x)) (fun t : Real =>
            t ^ (Inv.inv (k : Real)) * Robin1984.robinRealWeight 1 t) : Real) : Complex)))
      atTop (nhds (0 : Complex)) := by
  by_cases hChi : chi = 1
  next =>
    subst chi
    have hRH := (dirichletERH_principal_iff_riemannHypothesis (N := N)).1 hERH
    simpa only [ite_true, one_mul] using
      principalRootPrimeCharacterTail_centered_scaled_tendsto (N := N) hRH hk hs
  next =>
    simpa only [if_neg hChi, zero_mul, sub_zero] using
      rootPrimeCharacterTail_scaled_tendsto_of_ERH hChi hERH hk hs

end

end RobinBV.NumberField
