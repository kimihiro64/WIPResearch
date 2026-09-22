/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.AlmostAllActualPrimeRealMomentClosure
import RobinBV.Sieve.Proof.AlmostAllDyadicPrimeDensity

/-!
# Eventual actual-prime exceptional-block bound

This is the direct AA14 consumer.  It packages the exact low-moment and
corridor-cost hypotheses with one common threshold and returns the explicit
exceptional-cardinality estimate for every larger scale.  No zero-density or
moment input is hidden in the statement.
-/

set_option autoImplicit false

open MeasureTheory
open Filter

namespace RobinBV.Sieve

structure ActualPrimeMomentWitness (N : Nat) (delta C epsilon : Real) where
  Bf1 : Real
  Bf2 : Real
  Bg1 : Real
  Bg2 : Real
  f : Real -> Real
  g : Real -> Real
  hBf1 : 0 <= Bf1
  hBf2 : 0 <= Bf2
  hBg1 : 0 <= Bg1
  hBg2 : 0 <= Bg2
  hf1 : IntegrableOn f (Set.Icc ((N : Real)^2) (2*(N : Real)^2))
  hf2 : IntegrableOn f (Set.Icc (2*(N : Real)^2) (4*(N : Real)^2))
  hg1 : IntegrableOn g (Set.Icc ((N : Real)^2) (2*(N : Real)^2))
  hg2 : IntegrableOn g (Set.Icc (2*(N : Real)^2) (4*(N : Real)^2))
  hfull : IntegrableOn (fun x => f x + g x)
    (Set.Icc ((N : Real)^2) (4*(N : Real)^2))
  hnonneg : forall x, 0 <= f x + g x
  hbf1 : integral
    (MeasureTheory.volume.restrict
      (Set.Icc ((N : Real)^2) (2*(N : Real)^2))) f <= Bf1
  hbf2 : integral
    (MeasureTheory.volume.restrict
      (Set.Icc (2*(N : Real)^2) (4*(N : Real)^2))) f <= Bf2
  hbg1 : integral
    (MeasureTheory.volume.restrict
      (Set.Icc ((N : Real)^2) (2*(N : Real)^2))) g <= Bg1
  hbg2 : integral
    (MeasureTheory.volume.restrict
      (Set.Icc (2*(N : Real)^2) (4*(N : Real)^2))) g <= Bg2
  hcost : ENNReal.ofReal
    (((actualPrimeExceptionalBlock N delta).card : Real) * delta^5 *
      (N : Real)^5 / 8192) <=
    lintegral
      (MeasureTheory.volume.restrict
        (Set.Icc ((N : Real)^2) (4*(N : Real)^2)))
      (fun x => ENNReal.ofReal (f x + g x))
  hmoment : ENNReal.ofReal (Bf1 + Bf2 + Bg1 + Bg2) <=
    ENNReal.ofReal (C * (N : Real)^((11 / 2 : Real) + epsilon))

theorem prime_count_actual_exceptional_block_eventual_bound
    {delta C epsilon : Real} {N0 : Nat}
    (hd : 0 < delta) (hC : 0 <= C)
    (hN0 : 0 < N0)
    (hbound : forall N : Nat, N0 <= N ->
      Nonempty (ActualPrimeMomentWitness N delta C epsilon)) :
    forall N : Nat, N0 <= N ->
      ((actualPrimeExceptionalBlock N delta).card : Real) <=
        (8192 * C / delta^5) * (N : Real)^((1 / 2 : Real) + epsilon) := by
  intro N hN
  let W : ActualPrimeMomentWitness N delta C epsilon := Classical.choice (hbound N hN)
  exact prime_count_actual_exceptional_block_bound_from_real_moment
    (N := N) (delta := delta) (C := C) (epsilon := epsilon)
    (Bf1 := W.Bf1) (Bf2 := W.Bf2) (Bg1 := W.Bg1) (Bg2 := W.Bg2)
    (f := W.f) (g := W.g) (lt_of_lt_of_le hN0 hN) hd hC W.hcost
    W.hf1 W.hf2 W.hg1 W.hg2 W.hfull W.hnonneg W.hbf1 W.hbf2 W.hbg1 W.hbg2
    W.hmoment

theorem prime_count_dyadic_density_from_eventual_witness
    {delta C epsilon : Real} (k0 : Nat)
    (hd : 0 < delta) (hC : 0 <= C)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hsmall : forall k : Nat, k < k0 -> exists M : ENNReal,
      ENNReal.ofReal
          (((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real) *
            delta ^ 5 * ((2 ^ k : Nat) : Real) ^ 5 / 8192) <= M /\
      M <= ENNReal.ofReal
        (C * ((2 ^ k : Nat) : Real)^((11 / 2 : Real) + epsilon)))
    (hlarge : forall k : Nat, k0 <= k ->
      Nonempty (ActualPrimeMomentWitness (2 ^ k) delta C epsilon)) :
    Tendsto (fun m : Nat =>
      (Finset.sum (Finset.range m) (fun k =>
        ((actualPrimeExceptionalBlock (2 ^ k) delta).card : Real))) /
        (2 : Real) ^ m) atTop (nhds 0) := by
  apply prime_count_dyadic_density_from_actual_moment_bounds_after
    k0 hd hC he0 he1 hsmall
  intro k hk
  let W : ActualPrimeMomentWitness (2 ^ k) delta C epsilon :=
    Classical.choice (hlarge k hk)
  let M : ENNReal := lintegral
    (MeasureTheory.volume.restrict
      (Set.Icc (((2 ^ k : Nat) : Real)^2)
        (4*(((2 ^ k : Nat) : Real)^2))))
    (fun x => ENNReal.ofReal (W.f x + W.g x))
  have hsplit := _root_.almost_all_lintegral_sum_Icc_four_of_halves
    (X := ((2 ^ k : Nat) : Real)^2) (Bf1 := W.Bf1) (Bf2 := W.Bf2)
    (Bg1 := W.Bg1) (Bg2 := W.Bg2) (f := W.f) (g := W.g)
    (by positivity) W.hf1 W.hf2 W.hg1 W.hg2 W.hfull W.hnonneg
    W.hbf1 W.hbf2 W.hbg1 W.hbg2
  refine Exists.intro M (And.intro W.hcost ?_)
  exact hsplit.trans W.hmoment

end RobinBV.Sieve
