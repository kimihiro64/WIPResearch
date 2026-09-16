/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Sieve.Assembly.SquareCorridorZeroBounds
import RobinBV.Sieve.Proof.SquareCorridorArithmetic

/-!
# A prime-count deviation persists as a large actual zero packet

Every lower or upper deviation forces the corresponding signed full actual
zero sum to have size at least delta*n on a whole positive-length corridor.
All test and arithmetic-budget conditions are discharged at an explicit
arithmetic threshold. No zero-energy hypothesis, moment upper bound, or
almost-all theorem is assumed or concluded.

Import separately from the general RobinBV root to preserve the existing
Zeta23/PNT namespace separation.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem prime_count_deviation_forces_corridor_zero
    {n : Nat} (hn : 4 <= n) {delta x : Real}
    (hd0 : 0 < delta) (hd1 : delta <= 1)
    (hlarge : (5000/delta)^6 <= (n : Real))
    (hx0 : (n : Real)^2 <= x)
    (hx1 : x <= (n : Real)^2+(delta/128)*n/4) :
    ((((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) <
        (1-delta)*(n : Real)/Real.log n) ->
      delta*n <= (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        (Zeta23.zetaZeroConfig.mult rho : Complex)*
          Zeta23.paperFT (squareCorridorInnerTest (delta/128) (delta/512) x)
            (Zeta23.gammaOf rho))).re) /\
    (((1+delta)*(n : Real)/Real.log n <
        ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real)) ->
      delta*n <= -(tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        (Zeta23.zetaZeroConfig.mult rho : Complex)*
          Zeta23.paperFT (squareCorridorOuterTest (delta/128) (delta/512) x)
            (Zeta23.gammaOf rho))).re) := by
  have hnR : (4 : Real) <= n := by exact_mod_cast hn
  have hn0 : (0 : Real) < n := by linarith only [hnR]
  have hn1 : (1 : Real) <= n := by linarith only [hnR]
  have hnp : 0 < (n : Real)+1 := by linarith only [hnR]
  have htheta0 : 0 < delta/128 := by positivity
  have htheta1 : delta/128 <= 1/4 := by linarith only [hd1]
  have heta0 : 0 < delta/512 := by positivity
  have heta1 : delta/512 <= 1/2 := by linarith only [hd1]
  have het : (delta/512)*(1+2*(delta/128)) <= (delta/128)/2 := by
    have h := mul_nonneg hd0.le (show 0 <= 1-delta by linarith only [hd1])
    nlinarith only [h, hd0]
  let P : Real := ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real)
  let A : Real := (((n+1)*(n+1) : Nat) : Real)
  let E : Real := A^(1/3 : Real)*(Real.log A)^2/Real.log 2
  let Zi : Real := (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
    (Zeta23.zetaZeroConfig.mult rho : Complex)*
      Zeta23.paperFT (squareCorridorInnerTest (delta/128) (delta/512) x)
        (Zeta23.gammaOf rho))).re
  let Zo : Real := (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
    (Zeta23.zetaZeroConfig.mult rho : Complex)*
      Zeta23.paperFT (squareCorridorOuterTest (delta/128) (delta/512) x)
        (Zeta23.gammaOf rho))).re
  have htest := prime_count_corridor_zero_bounds hn htheta0 htheta1 heta0 heta1 het hx0 hx1
  change (((2*(n : Real)-2)*(1-2*(delta/128))*(1-2*(delta/512))-1-Zi) /
    Real.log A-A^(1/3 : Real)*Real.log A/Real.log 2 <= P) /\
    (P*Real.log (n*n : Nat) <= (2*(n : Real)+7)*(1+4*(delta/128))+1-Zo) at htest
  have hA : A = ((n : Real)+1)^2 := by dsimp [A]; push_cast; ring
  have hLA : Real.log A = 2*Real.log ((n : Real)+1) := by
    rw [hA, Real.log_pow]
    norm_num
  have hlogn : 1 <= Real.log (n : Real) := by
    have h := Real.le_log_one_add_of_nonneg
      (show 0 <= (n : Real)-1 by linarith only [hnR])
    have h1 : 1+((n : Real)-1) = n := by ring
    have h2 : ((n : Real)-1)+2 = (n : Real)+1 := by ring
    rw [h1, h2] at h
    have hfrac : 1 <= 2*((n : Real)-1)/((n : Real)+1) :=
      (_root_.one_le_div hnp).mpr (by linarith only [hnR])
    exact hfrac.trans h
  have hln0 : 0 < Real.log (n : Real) := by linarith only [hlogn]
  have hlog20 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hlogA0 : 0 < Real.log A := by
    rw [hLA]
    exact mul_pos (by norm_num) (Real.log_pos (by linarith only [hnR]))
  have hlognn : Real.log (n*n : Nat) = 2*Real.log (n : Real) := by
    rw [Nat.cast_mul, Real.log_mul hn0.ne' hn0.ne']
    ring
  have hb := squareCorridor_primePower_budget_at_explicit_threshold hn1 hd0 hlarge
  have hBudget : E+5 <= delta*n/2 := by
    dsimp [E]
    rw [hA]
    exact hb.1
  have hdn0 : 0 <= delta*(n : Real) := mul_nonneg hd0.le hn0.le
  have hcore : 2*(n : Real)-2-(5/128)*delta*n <=
      (2*(n : Real)-2)*(1-2*(delta/128))*(1-2*(delta/512)) := by
    have hq : 1-5*delta/256 <= (1-2*(delta/128))*(1-2*(delta/512)) := by
      nlinarith only [sq_nonneg delta]
    have h := mul_le_mul_of_nonneg_left hq (show 0 <= 2*(n : Real)-2 by linarith only [hnR])
    nlinarith only [h, hd0]
  have hdiff : Real.log ((n : Real)+1)-Real.log (n : Real) <= 1/(n : Real) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hnp hn0)
    rw [Real.log_div hnp.ne' hn0.ne'] at h
    have hid : ((n : Real)+1)/(n : Real)-1 = 1/(n : Real) := by
      field_simp [hn0.ne']
      ring
    rwa [hid] at h
  have hLAupper : Real.log A <= 2*Real.log (n : Real)+2/(n : Real) := by
    rw [hLA, show 2/(n : Real) = 2*(1/(n : Real)) by ring]
    linarith only [hdiff]
  change (P < (1-delta)*(n : Real)/Real.log n -> delta*n <= Zi) /\
    ((1+delta)*(n : Real)/Real.log n < P -> delta*n <= -Zo)
  refine And.intro ?_ ?_
  next =>
    intro hbad
    have hF0 : 0 <= (1-delta)*(n : Real)/Real.log n :=
      div_nonneg (mul_nonneg (by linarith only [hd1]) hn0.le) hln0.le
    have hD : (1-delta)/Real.log n <= 1 := by
      calc
        _ <= Real.log n/Real.log n :=
          div_le_div_of_nonneg_right (by linarith only [hlogn, hd0]) hln0.le
        _ = 1 := div_self hln0.ne'
    have hPmass : P*Real.log A < 2*(1-delta)*(n : Real)+2 := by
      calc
        _ < ((1-delta)*(n : Real)/Real.log n)*Real.log A :=
          mul_lt_mul_of_pos_right hbad hlogA0
        _ <= ((1-delta)*(n : Real)/Real.log n)*
            (2*Real.log n+2/(n : Real)) :=
          mul_le_mul_of_nonneg_left hLAupper hF0
        _ = 2*(1-delta)*(n : Real)+2*((1-delta)/Real.log n) := by
          field_simp [hn0.ne', hln0.ne']
        _ <= 2*(1-delta)*(n : Real)+2 := by linarith only [hD]
    have hmul := mul_le_mul_of_nonneg_right htest.1 hlogA0.le
    have hid : (((2*(n : Real)-2)*(1-2*(delta/128))*(1-2*(delta/512))-1-Zi) /
        Real.log A-A^(1/3 : Real)*Real.log A/Real.log 2)*Real.log A =
        (2*(n : Real)-2)*(1-2*(delta/128))*(1-2*(delta/512))-1-Zi-E := by
      dsimp [E]
      field_simp [hlogA0.ne', hlog20.ne']
    rw [hid] at hmul
    nlinarith only [hmul, hcore, hPmass, hBudget, hdn0]
  next =>
    intro hbad
    have hPmass := mul_lt_mul_of_pos_right hbad
      (show 0 < 2*Real.log (n : Real) by positivity)
    have hid : ((1+delta)*(n : Real)/Real.log n)*(2*Real.log n) =
        2*(1+delta)*(n : Real) := by field_simp [hln0.ne']
    rw [hid] at hPmass
    have hupper := htest.2
    rw [hlognn] at hupper
    nlinarith only [hPmass, hupper, hb.2, hd1]

end RobinBV.Sieve
