/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.AlmostAllActualPrimeClosure
import RobinBV.Sieve.Proof.AlmostAllCorridorMomentAssembly

/-!
# Actual-prime closure from real corridor moments

This module is the direct consumer joining the corridor cost to the existing
real inner and outer fourth-moment estimates.  It makes the full-interval
integrability, nonnegativity, endpoint split, and ENNReal conversion explicit
before applying the actual-prime cardinality theorem.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Classical

namespace RobinBV.Sieve

theorem prime_count_actual_exceptional_block_bound_from_real_moment
    {N : Nat} {delta C epsilon Bf1 Bf2 Bg1 Bg2 : Real}
    {f g : Real -> Real}
    (hN : 0 < N) (hd : 0 < delta) (hC : 0 <= C)
    (hcost : ENNReal.ofReal
      (((actualPrimeExceptionalBlock N delta).card : Real) * delta^5 *
        (N : Real)^5 / 8192) <=
      lintegral
        (volume.restrict (Set.Icc ((N : Real)^2) (4*(N : Real)^2)))
        (fun x => ENNReal.ofReal (f x + g x)))
    (hf1 : IntegrableOn f
      (Set.Icc ((N : Real)^2) (2*(N : Real)^2)))
    (hf2 : IntegrableOn f
      (Set.Icc (2*(N : Real)^2) (4*(N : Real)^2)))
    (hg1 : IntegrableOn g
      (Set.Icc ((N : Real)^2) (2*(N : Real)^2)))
    (hg2 : IntegrableOn g
      (Set.Icc (2*(N : Real)^2) (4*(N : Real)^2)))
    (hfull : IntegrableOn (fun x => f x + g x)
      (Set.Icc ((N : Real)^2) (4*(N : Real)^2)))
    (hnonneg : forall x, 0 <= f x + g x)
    (hbf1 : integral
      (volume.restrict (Set.Icc ((N : Real)^2) (2*(N : Real)^2))) f <= Bf1)
    (hbf2 : integral
      (volume.restrict (Set.Icc (2*(N : Real)^2) (4*(N : Real)^2))) f <= Bf2)
    (hbg1 : integral
      (volume.restrict (Set.Icc ((N : Real)^2) (2*(N : Real)^2))) g <= Bg1)
    (hbg2 : integral
      (volume.restrict (Set.Icc (2*(N : Real)^2) (4*(N : Real)^2))) g <= Bg2)
    (hmoment : ENNReal.ofReal (Bf1 + Bf2 + Bg1 + Bg2) <=
      ENNReal.ofReal (C * (N : Real)^((11 / 2 : Real) + epsilon))) :
    ((actualPrimeExceptionalBlock N delta).card : Real) <=
      (8192 * C / delta^5) * (N : Real)^((1 / 2 : Real) + epsilon) := by
  have hsplit := _root_.almost_all_lintegral_sum_Icc_four_of_halves
    (X := (N : Real)^2) (Bf1 := Bf1) (Bf2 := Bf2)
    (Bg1 := Bg1) (Bg2 := Bg2) (f := f) (g := g)
    (by positivity) hf1 hf2 hg1 hg2 hfull hnonneg hbf1 hbf2 hbg1 hbg2
  have hcost' := hcost.trans hsplit
  exact prime_count_bad_block_bound_from_low_moment hN hd hC hcost' hmoment

end RobinBV.Sieve
