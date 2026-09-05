import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimePowerCorrection

/-!
# Exact prime-power decomposition of the conductor correction

The complete difference of character Chebyshev sums is reconstructed from
every prime divisor of the ambient level and every positive exponent admitted
by the cutoff. Primes on which the inducing character vanishes cancel
automatically. No estimate or ERH hypothesis is used.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz

noncomputable section

/-- The exact finite prime-power conductor correction, including cutoff zero
and primes whose first power already exceeds the cutoff. -/
theorem characterChebyshevSum_sub_primitive_eq_sum_primePowers
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (x : Nat) :
    characterChebyshevSum x chi - characterChebyshevSum x chi.primitiveCharacter =
      -Finset.sum N.primeFactors (fun p =>
        (Real.log p : Complex) * Finset.sum (Finset.Icc 1 (Nat.log p x))
          (fun k => chi.primitiveCharacter (p : ZMod chi.conductor) ^ k)) := by
  unfold characterChebyshevSum BombieriVinogradov.VaughanMeanValue.psiCharacterSum
  rw [<- Finset.sum_sub_distrib]
  simp_rw [<- mul_sub]
  exact chi.sum_vonMangoldt_mul_sub_primitive_eq x

end

end RobinBV.NumberField
