/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Sieve.Assembly.SquareCorridorDeviation

/-!
# Complete actual-prime exceptional-block cost in the zero fourth moment

Every bad square interval contributes a disjoint positive-length corridor.
The full actual inner/outer zero sums are used jointly. All arithmetic,
endpoints and cardinality factors are included. The nonnegative extended
integral may be infinite; no integrability or analytic moment bound is assumed.

This is the counting consumer, not an almost-all theorem or a moment upper
estimate. Import separately from the general RobinBV root to preserve the
existing Zeta23/PNT namespace separation.
-/

set_option autoImplicit false

open scoped Classical

namespace RobinBV.Sieve

theorem prime_count_bad_block_full_zero_fourth_moment_cost
    {N : Nat} (hN : 4 <= N) {delta : Real}
    (hd0 : 0 < delta) (hd1 : delta <= 1)
    (hlarge : (5000/delta)^6 <= (N : Real)) :
    ENNReal.ofReal
      ((((Finset.Ico N (2*N)).filter (fun n : Nat =>
        Or (((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) <
          (1-delta)*(n : Real)/Real.log n)
          ((1+delta)*(n : Real)/Real.log n <
            ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real)))).card : Real)*
        delta^5*(N : Real)^5/512) <=
    MeasureTheory.lintegral
      (MeasureTheory.volume.restrict (Set.Icc ((N : Real)^2) (4*(N : Real)^2)))
      (fun x : Real => ENNReal.ofReal
        (norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex)*
            Zeta23.paperFT (squareCorridorInnerTest (delta/128) (delta/512) x)
              (Zeta23.gammaOf rho)))^4 +
         norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex)*
            Zeta23.paperFT (squareCorridorOuterTest (delta/128) (delta/512) x)
              (Zeta23.gammaOf rho)))^4)) := by
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
  let Zi : Real -> Complex := fun x => tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
    (Zeta23.zetaZeroConfig.mult rho : Complex)*
      Zeta23.paperFT (squareCorridorInnerTest (delta/128) (delta/512) x)
        (Zeta23.gammaOf rho))
  let Zo : Real -> Complex := fun x => tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
    (Zeta23.zetaZeroConfig.mult rho : Complex)*
      Zeta23.paperFT (squareCorridorOuterTest (delta/128) (delta/512) x)
        (Zeta23.gammaOf rho))
  let F : Real -> ENNReal := fun x => ENNReal.ofReal (norm (Zi x)^4+norm (Zo x)^4)
  change ENNReal.ofReal ((B.card : Real)*delta^5*(N : Real)^5/512) <=
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
  have hUmeas : MeasurableSet U :=
    MeasurableSet.iUnion (fun n : Nat =>
      MeasurableSet.iUnion (fun _ : Membership.mem B n => measurableSet_Icc))
  have hImeas : MeasurableSet I := measurableSet_Icc
  have hUnionMeasure : MeasureTheory.volume U =
      Finset.sum B (fun n => MeasureTheory.volume (J n)) :=
    MeasureTheory.measure_biUnion_finset hdisjoint (fun _ _ => measurableSet_Icc)
  have hJMeasure (n : Nat) :
      MeasureTheory.volume (J n) = ENNReal.ofReal (delta*n/512) := by
    change MeasureTheory.volume
      (Set.Icc ((n : Real)^2) ((n : Real)^2+delta*n/512)) = _
    rw [Real.volume_Icc]
    congr 1
    ring
  have hUnionCast : MeasureTheory.volume U =
      ENNReal.ofReal (Finset.sum B (fun n => delta*n/512)) := by
    rw [hUnionMeasure]
    calc
      _ = Finset.sum B (fun n => ENNReal.ofReal (delta*n/512)) :=
        Finset.sum_congr rfl (fun n _ => hJMeasure n)
      _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)).symm
  have hsum : (B.card : Real)*(delta*N/512) <= Finset.sum B (fun n => delta*n/512) := by
    calc
      _ = Finset.sum B (fun _ => delta*(N : Real)/512) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ <= _ := by
        apply Finset.sum_le_sum
        intro n hn
        have hi := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
        have hNR : (N : Real) <= n := by exact_mod_cast hi
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNR hd0.le)
          (by norm_num)
  have hfourth {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hab : a <= b) :
      a^4 <= b^4 := by
    have hs := mul_le_mul hab hab ha hb
    have h4 := mul_le_mul hs hs (mul_nonneg ha ha) (mul_nonneg hb hb)
    calc
      a^4 = (a*a)*(a*a) := by ring
      _ <= (b*b)*(b*b) := h4
      _ = b^4 := by ring
  have hpoint (n : Nat) (hn : Membership.mem B n) (x : Real) (hx : (J n) x) :
      ENNReal.ofReal ((delta*(N : Real))^4) <= F x := by
    have hb := Finset.mem_filter.mp hn
    have hi := Finset.mem_Ico.mp hb.1
    have hn4 : 4 <= n := hN.trans hi.1
    have hNR : (N : Real) <= n := by exact_mod_cast hi.1
    have hL : (5000/delta)^6 <= (n : Real) := hlarge.trans hNR
    have hxlo : (n : Real)^2 <= x := hx.1
    have hxhi : x <= (n : Real)^2+(delta/128)*n/4 := by
      have he : (n : Real)^2+delta*n/512 =
          (n : Real)^2+(delta/128)*n/4 := by ring
      rw [<- he]
      exact hx.2
    have hforce := prime_count_deviation_forces_corridor_zero hn4 hd0 hd1 hL hxlo hxhi
    have hDN : delta*(N : Real) <= delta*n := mul_le_mul_of_nonneg_left hNR hd0.le
    have hDN0 : 0 <= delta*(N : Real) := mul_nonneg hd0.le (Nat.cast_nonneg N)
    change ENNReal.ofReal ((delta*(N : Real))^4) <=
      ENNReal.ofReal (norm (Zi x)^4+norm (Zo x)^4)
    apply ENNReal.ofReal_le_ofReal
    rcases hb.2 with hlow | hhigh
    next =>
      have hz : delta*n <= (Zi x).re := hforce.1 hlow
      have hnorm : delta*(N : Real) <= norm (Zi x) :=
        hDN.trans (hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _)))
      have h4 := hfourth hDN0 (norm_nonneg _) hnorm
      linarith only [h4, show 0 <= norm (Zo x)^4 by positivity]
    next =>
      have hz : delta*n <= -(Zo x).re := hforce.2 hhigh
      have hneg : -(Zo x).re <= norm (Zo x) := by
        calc
          _ <= abs (-(Zo x).re) := le_abs_self _
          _ = abs (Zo x).re := abs_neg _
          _ <= _ := Complex.abs_re_le_norm _
      have hnorm : delta*(N : Real) <= norm (Zo x) := hDN.trans (hz.trans hneg)
      have h4 := hfourth hDN0 (norm_nonneg _) hnorm
      linarith only [h4, show 0 <= norm (Zi x)^4 by positivity]
  have hind (x : Real) :
      U.indicator (fun _ => ENNReal.ofReal ((delta*(N : Real))^4)) x <=
        I.indicator F x := by
    by_cases hx : U x
    next =>
      have hxI := hcover hx
      rw [Set.indicator_of_mem (s := U) (a := x) hx
        (fun _ => ENNReal.ofReal ((delta*(N : Real))^4)),
        Set.indicator_of_mem (s := I) (a := x) hxI F]
      choose n hn using Set.mem_iUnion.mp hx
      choose hnB hxn using Set.mem_iUnion.mp hn
      exact hpoint n hnB x hxn
    next =>
      rw [Set.indicator_of_notMem (s := U) (a := x) hx
        (fun _ => ENNReal.ofReal ((delta*(N : Real))^4))]
      exact zero_le
  have hInt :
      MeasureTheory.lintegral MeasureTheory.volume
        (U.indicator (fun _ => ENNReal.ofReal ((delta*(N : Real))^4))) <=
      MeasureTheory.lintegral MeasureTheory.volume (I.indicator F) :=
    MeasureTheory.lintegral_mono hind
  rw [MeasureTheory.lintegral_indicator_const hUmeas,
    MeasureTheory.lintegral_indicator hImeas] at hInt
  calc
    _ = ENNReal.ofReal
        ((delta*(N : Real))^4*((B.card : Real)*(delta*N/512))) := by
      congr 1
      ring
    _ <= ENNReal.ofReal
        ((delta*(N : Real))^4*Finset.sum B (fun n => delta*n/512)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = ENNReal.ofReal ((delta*(N : Real))^4)*
        ENNReal.ofReal (Finset.sum B (fun n => delta*n/512)) :=
      ENNReal.ofReal_mul (by positivity)
    _ = ENNReal.ofReal ((delta*(N : Real))^4)*MeasureTheory.volume U := by
      rw [hUnionCast]
    _ <= _ := hInt

end RobinBV.Sieve
