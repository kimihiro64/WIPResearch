import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Critical-strip zeros of completed Dirichlet L-functions

The completed Dirichlet L-function is already analytically continued in
Mathlib.  These definitions isolate its critical-strip zeros and the
corresponding extended Riemann hypothesis without introducing an abstract
zero predicate.
-/

namespace RobinBV.NumberField

open DirichletCharacter

variable {N : Nat} [NeZero N]

/-- A zero of the completed Dirichlet L-function strictly inside the critical
strip. -/
def IsNontrivialCompletedLZero
    (chi : DirichletCharacter Complex N) (rho : Complex) : Prop :=
  And (completedLFunction chi rho = 0)
    (And (0 < rho.re) (rho.re < 1))

/-- Extended RH for a Dirichlet character, stated using the actual completed
L-function supplied by Mathlib. -/
def DirichletERH (chi : DirichletCharacter Complex N) : Prop :=
  forall rho : Complex,
    IsNontrivialCompletedLZero chi rho -> rho.re = 1 / 2

end RobinBV.NumberField
