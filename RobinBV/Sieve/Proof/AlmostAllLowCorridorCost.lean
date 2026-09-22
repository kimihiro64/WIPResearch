/- Copyright (c) 2026 Jonas Whidden. -/
import RobinBV.Sieve.Assembly.SquareCorridorDeviation
import RobinBV.Sieve.Assembly.SquareCorridorMomentCost

/-!
# Low-zero exceptional-block cost

This module gives the disjoint-corridor measure lower bound and its actual
prime-count specialization, including endpoints and the factor 8192.
-/

set_option autoImplicit false

open scoped Classical
open MeasureTheory

theorem rob_bv_disjoint_corridor_low_cost
    {N : Nat} {delta : Real} {B : Finset Nat}
    {J : Nat -> Set Real} {U I : Set Real} {F : Real -> ENNReal}
    (hN : 4 <= N) (hd0 : 0 < delta)
    (hBsub : forall n, Membership.mem B n -> Membership.mem (Finset.Ico N (2*N)) n)
    (hdisjoint : (B : Set Nat).PairwiseDisjoint J)
    (hJsub : forall n, Membership.mem B n -> Set.Subset (J n) U)
    (hcover : Set.Subset U I)
    (hJmeas : forall n, MeasurableSet (J n))
    (hUmeas : MeasurableSet U) (hImeas : MeasurableSet I)
    (hmeasure : forall n, Membership.mem B n ->
      MeasureTheory.volume (J n) = ENNReal.ofReal (delta*n/512))
    (hpoint : forall n, Membership.mem B n -> forall x, J n x ->
      ENNReal.ofReal ((delta*(N : Real)/2)^4) <= F x) :
    ENNReal.ofReal
      (((B.card : Real)*delta^5*(N : Real)^5)/8192) <=
    MeasureTheory.lintegral (MeasureTheory.volume.restrict I) F := by
  let V : Set Real := Set.iUnion (fun n : Nat =>
    Set.iUnion (fun _ : Membership.mem B n => J n))
  have hVmeas : MeasurableSet V :=
    MeasurableSet.iUnion (fun n : Nat =>
      MeasurableSet.iUnion (fun _ : Membership.mem B n =>
        hJmeas n))
  have hVsub : Set.Subset V U := by
    intro x hx
    choose n hn using Set.mem_iUnion.mp hx
    choose hnB hxn using Set.mem_iUnion.mp hn
    exact hJsub n hnB hxn
  have hUnionMeasure : MeasureTheory.volume V =
      Finset.sum B (fun n => MeasureTheory.volume (J n)) :=
    MeasureTheory.measure_biUnion_finset hdisjoint
      (fun n hn => hJmeas n)
  have hUnionCast : MeasureTheory.volume V =
      ENNReal.ofReal (Finset.sum B (fun n => delta*n/512)) := by
    rw [hUnionMeasure]
    calc
      _ = Finset.sum B (fun n => ENNReal.ofReal (delta*n/512)) :=
        Finset.sum_congr rfl (fun n hn => hmeasure n hn)
      _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)).symm
  have hsum : (B.card : Real)*(delta*(N : Real)/512) <=
      Finset.sum B (fun n => delta*n/512) := by
    calc
      _ = Finset.sum B (fun _ => delta*(N : Real)/512) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ <= _ := by
        apply Finset.sum_le_sum
        intro n hn
        have hi := hBsub n hn
        have hNR : (N : Real) <= n := by
          exact_mod_cast (Finset.mem_Ico.mp hi).1
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNR hd0.le) (by norm_num)
  have hind (x : Real) :
      V.indicator (fun _ => ENNReal.ofReal ((delta*(N : Real)/2)^4)) x <=
        U.indicator F x := by
    by_cases hx : V x
    next =>
      rw [Set.indicator_of_mem (s := V) (a := x) hx
        (fun _ => ENNReal.ofReal ((delta*(N : Real)/2)^4))]
      rw [Set.indicator_of_mem (s := U) (a := x) (hVsub hx) F]
      choose n hn using Set.mem_iUnion.mp hx
      choose hnB hxn using Set.mem_iUnion.mp hn
      exact hpoint n hnB x hxn
    next =>
      rw [Set.indicator_of_notMem (s := V) (a := x) hx
        (fun _ => ENNReal.ofReal ((delta*(N : Real)/2)^4))]
      exact zero_le
  have hInt :
      MeasureTheory.lintegral MeasureTheory.volume
        (V.indicator (fun _ => ENNReal.ofReal ((delta*(N : Real)/2)^4))) <=
      MeasureTheory.lintegral MeasureTheory.volume (U.indicator F) := by
    apply MeasureTheory.lintegral_mono
    exact hind
  rw [MeasureTheory.lintegral_indicator_const hVmeas,
    MeasureTheory.lintegral_indicator hUmeas] at hInt
  have hInt' : ENNReal.ofReal ((delta*(N : Real)/2)^4) *
        ENNReal.ofReal (Finset.sum B (fun n => delta*n/512)) <=
      MeasureTheory.lintegral (MeasureTheory.volume.restrict U) F := by
    rw [<- hUnionCast]
    simpa only [MeasureTheory.lintegral_indicator hUmeas] using hInt
  calc
    _ = ENNReal.ofReal ((delta*(N : Real)/2)^4) *
        ENNReal.ofReal ((B.card : Real)*delta*(N : Real)/512) := by
      rw [<- ENNReal.ofReal_mul]
      ring_nf
      positivity
    _ <= ENNReal.ofReal ((delta*(N : Real)/2)^4) *
        ENNReal.ofReal (Finset.sum B (fun n => delta*n/512)) := by
      gcongr
      convert hsum using 1 <;> ring
    _ <= MeasureTheory.lintegral (MeasureTheory.volume.restrict U) F := hInt'
    _ <= MeasureTheory.lintegral (MeasureTheory.volume.restrict I) F := by
      apply MeasureTheory.lintegral_mono'
      exact Measure.restrict_mono hcover le_rfl
      exact le_rfl

namespace RobinBV.Sieve

theorem prime_count_bad_block_low_zero_fourth_moment_cost
    {N : Nat} (hN : 4 <= N) {delta : Real}
    (hd0 : 0 < delta) (hd1 : delta <= 1)
    (hlarge : (5000/delta)^6 <= (N : Real))
    (hlowpoint : forall n, Membership.mem
      ((Finset.Ico N (2*N)).filter (fun n : Nat =>
        Or (((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) <
          (1-delta)*(n : Real)/Real.log n)
          ((1+delta)*(n : Real)/Real.log n <
            ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real)))) n ->
      forall x, Set.Icc ((n : Real)^2) ((n : Real)^2+delta*n/512) x ->
      ENNReal.ofReal ((delta*(N : Real)/2)^4) <=
        ENNReal.ofReal (
          norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
            if (rho : Complex).re <= 79/100 then
              (Zeta23.zetaZeroConfig.mult rho : Complex) *
                Zeta23.paperFT (squareCorridorInnerTest (delta/128) (delta/512) x)
                  (Zeta23.gammaOf rho) else 0))^4 +
          norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
            if (rho : Complex).re <= 79/100 then
              (Zeta23.zetaZeroConfig.mult rho : Complex) *
                Zeta23.paperFT (squareCorridorOuterTest (delta/128) (delta/512) x)
                  (Zeta23.gammaOf rho) else 0))^4)) :
    ENNReal.ofReal
      ((((Finset.Ico N (2*N)).filter (fun n : Nat =>
        Or (((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) <
          (1-delta)*(n : Real)/Real.log n)
          ((1+delta)*(n : Real)/Real.log n <
            ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real)))).card : Real)*
        delta^5*(N : Real)^5/8192) <=
    MeasureTheory.lintegral
      (MeasureTheory.volume.restrict (Set.Icc ((N : Real)^2) (4*(N : Real)^2)))
      (fun x : Real => ENNReal.ofReal
        (norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          if (rho : Complex).re <= 79/100 then
            (Zeta23.zetaZeroConfig.mult rho : Complex) *
              Zeta23.paperFT (squareCorridorInnerTest (delta/128) (delta/512) x)
                (Zeta23.gammaOf rho) else 0))^4 +
         norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          if (rho : Complex).re <= 79/100 then
            (Zeta23.zetaZeroConfig.mult rho : Complex) *
              Zeta23.paperFT (squareCorridorOuterTest (delta/128) (delta/512) x)
                (Zeta23.gammaOf rho) else 0))^4)) := by
  classical
  let B : Finset Nat := (Finset.Ico N (2*N)).filter (fun n : Nat =>
    Or (((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) <
      (1-delta)*(n : Real)/Real.log n)
      ((1+delta)*(n : Real)/Real.log n <
        ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real)))
  let J : Nat -> Set Real := fun n =>
    Set.Icc ((n : Real)^2) ((n : Real)^2+delta*n/512)
  let U : Set Real := Set.iUnion (fun n : Nat =>
    Set.iUnion (fun _ : Membership.mem B n => J n))
  let I : Set Real := Set.Icc ((N : Real)^2) (4*(N : Real)^2)
  let F : Real -> ENNReal := fun x => ENNReal.ofReal
    (norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if (rho : Complex).re <= 79/100 then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorInnerTest (delta/128) (delta/512) x)
            (Zeta23.gammaOf rho) else 0))^4 +
     norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if (rho : Complex).re <= 79/100 then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorOuterTest (delta/128) (delta/512) x)
            (Zeta23.gammaOf rho) else 0))^4)
  change ENNReal.ofReal ((B.card : Real)*delta^5*(N : Real)^5/8192) <=
    MeasureTheory.lintegral (MeasureTheory.volume.restrict I) F
  have hshort (n : Nat) :
      (n : Real)^2+delta*n/512 < ((n : Real)+1)^2 := by
    have h := mul_le_mul_of_nonneg_right hd1 (Nat.cast_nonneg n)
    nlinarith only [h, show (0 : Real) <= n from Nat.cast_nonneg n]
  have hdisjoint : (B : Set Nat).PairwiseDisjoint J := by
    intro n _hn m _hm hne
    apply Set.disjoint_left.mpr
    intro x hxn hxm
    rcases lt_or_gt_of_ne hne with hnm | hmn
    next =>
      have hs : (n : Real)+1 <= m := by
        exact_mod_cast (show n+1 <= m by omega)
      have hprod := mul_le_mul hs hs
        (show (0 : Real) <= (n : Real)+1 by positivity) (Nat.cast_nonneg m)
      nlinarith only [hprod, hshort n, hxn.2, hxm.1]
    next =>
      have hs : (m : Real)+1 <= n := by
        exact_mod_cast (show m+1 <= n by omega)
      have hprod := mul_le_mul hs hs
        (show (0 : Real) <= (m : Real)+1 by positivity) (Nat.cast_nonneg n)
      nlinarith only [hprod, hshort m, hxm.2, hxn.1]
  have hJsub (n : Nat) (hn : Membership.mem B n) : Set.Subset (J n) U := by
    intro x hx
    exact Set.mem_iUnion.mpr (Exists.intro n
      (Set.mem_iUnion.mpr (Exists.intro hn hx)))
  have hcover : Set.Subset U I := by
    intro x hx
    choose n hn using Set.mem_iUnion.mp hx
    choose hnB hxn using Set.mem_iUnion.mp hn
    have hi := Finset.mem_Ico.mp (Finset.mem_filter.mp hnB).1
    have hlow : (N : Real) <= n := by exact_mod_cast hi.1
    have hlowprod := mul_le_mul hlow hlow (Nat.cast_nonneg N) (Nat.cast_nonneg n)
    have hhigh : (n : Real)+1 <= 2*(N : Real) := by
      exact_mod_cast (show n+1 <= 2*N by omega)
    have hhighprod := mul_le_mul hhigh hhigh
      (show (0 : Real) <= (n : Real)+1 by positivity)
      (show (0 : Real) <= 2*(N : Real) by positivity)
    change (N : Real)^2 <= x /\ x <= 4*(N : Real)^2
    exact And.intro (by nlinarith only [hlowprod, hxn.1])
      (by nlinarith only [hhighprod, hshort n, hxn.2])
  have hpoint (n : Nat) (hn : Membership.mem B n) (x : Real) (hx : J n x) :
      ENNReal.ofReal ((delta*(N : Real)/2)^4) <= F x := by
    exact hlowpoint n hn x hx
  apply rob_bv_disjoint_corridor_low_cost hN hd0
    (fun n hn => (Finset.mem_filter.mp hn).1)
    hdisjoint hJsub hcover (fun _ => measurableSet_Icc)
    (MeasurableSet.iUnion (fun n =>
      MeasurableSet.iUnion (fun _ : Membership.mem B n => measurableSet_Icc)))
    measurableSet_Icc (fun n hn => by rw [Real.volume_Icc]; congr 1; ring)
    hpoint

end RobinBV.Sieve
