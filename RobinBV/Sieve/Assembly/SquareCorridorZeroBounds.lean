/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Sieve.Assembly.SquareCorridorBounds
import RobinBV.Sieve.Helpers.SquareCorridorPole
import RobinBV.Sieve.Proof.SquareIntervalGammaCorrection

/-!
# Actual prime bounds with only the zero packets unestimated

Both growing poles have explicit envelopes. The full other-pole-plus-gamma
packet has norm at most one for each shifted test. The lower prime-power
allowance remains unchanged, and every actual zero with its multiplicity is
retained. No zero-moment, almost-all or uniform positivity claim is made.

Import separately from the general RobinBV root, preserving the documented
Zeta23/PNT namespace separation.
-/

set_option autoImplicit false

open MeasureTheory

namespace RobinBV.Sieve

theorem scaledLogWindowTest_gamma_norm_le {eta L c : Real}
    (he : 0 < eta) (hL : 0 < L) (hc : 0 < c) :
    norm ((1/(2*Real.pi) : Complex)*MeasureTheory.integral MeasureTheory.volume
      (fun r : Real => Zeta23.paperFT (scaledLogWindowTest eta L c) r *
        (Zeta23.EF.gammaBracket r : Complex)) +
      Zeta23.paperFT (scaledLogWindowTest eta L c) (Complex.I/2)) <=
        L/(Real.exp (2*c)-1) := by
  have hsupp (u : Real) (hu : Not ((Set.Icc c (c+L)) u)) :
      scaledLogWindowTest eta L c u = 0 := by
    by_cases hc' : u <= c
    next =>
      have hz := logWindowCutoff_zero_left (v := (u-c)/L) he
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le)
      simp only [scaledLogWindowTest, hz, Complex.ofReal_zero, mul_zero]
    next =>
      have hright : c+L <= u := by
        by_contra h
        exact hu (And.intro (le_of_lt (lt_of_not_ge hc'))
          (le_of_lt (lt_of_not_ge h)))
      have hv : 1 <= (u-c)/L := by
        calc
          (1 : Real) = L/L := (div_self hL.ne').symm
          _ <= (u-c)/L := div_le_div_of_nonneg_right (by linarith) hL.le
      have hz := logWindowCutoff_zero_right he hv
      simp only [scaledLogWindowTest, hz, Complex.ofReal_zero, mul_zero]
  have hb (u : Real) (_hu : (Set.Icc c (c+L)) u) :
      norm (scaledLogWindowTest eta L c u) <= Real.exp (u/2) := by
    change norm (Complex.exp ((u : Complex)/2)*logWindowProfile eta ((u-c)/L)) <= _
    rw [norm_mul, Complex.norm_exp]
    have hRe : ((u : Complex)/2).re = u/2 := by simp
    rw [hRe]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (logWindowProfile_norm_le_one eta ((u-c)/L)) (Real.exp_pos (u/2)).le
  have h := Zeta23.EF.gammaCorrection_norm_le (scaledLogWindowTest_contDiff eta L c)
    (scaledLogWindowTest_hasCompactSupport he hL c) hc
    (show c <= c+L by linarith) hsupp hb
  simpa only [add_sub_cancel_left] using h

theorem prime_count_corridor_zero_bounds
    {n : Nat} (hn : 4 <= n) {theta eta x : Real}
    (ht0 : 0 < theta) (ht1 : theta <= 1/4) (he : 0 < eta) (he2 : eta <= 1/2)
    (het : eta*(1+2*theta) <= theta/2)
    (hx0 : (n : Real)^2 <= x) (hx1 : x <= (n : Real)^2+theta*n/4) :
    (((2*(n : Real)-2)*(1-2*theta)*(1-2*eta)-1-
        (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex)*
            Zeta23.paperFT (squareCorridorInnerTest theta eta x)
              (Zeta23.gammaOf rho))).re) /
        Real.log ((n+1)*(n+1) : Nat) -
      (((n+1)*(n+1) : Nat) : Real)^(1/3 : Real)*
        Real.log ((n+1)*(n+1) : Nat)/Real.log 2 <=
      ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real)) /\
    (((Nat.PrimeSieve.squareIntervalPrimes n).card : Real)*Real.log (n*n : Nat) <=
      (2*(n : Real)+7)*(1+4*theta)+1-
        (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex)*
            Zeta23.paperFT (squareCorridorOuterTest theta eta x)
              (Zeta23.gammaOf rho))).re) := by
  have hnR : (4 : Real) <= n := by exact_mod_cast hn
  have hp := squareCorridor_scalar_parameters hnR ht0 ht1 hx0 hx1
  have hpo := squareCorridor_pole_bounds hnR ht0 ht1 he he2 hx0 hx1
  let g : (Real -> Complex) -> Complex := fun k =>
    (1/(2*Real.pi) : Complex)*MeasureTheory.integral MeasureTheory.volume
      (fun r : Real => Zeta23.paperFT k r*(Zeta23.EF.gammaBracket r : Complex)) +
      Zeta23.paperFT k (Complex.I/2)
  have hg (L c : Real) (hL : 0 < L) (hL1 : L <= 1) (hc1 : 1 <= c) :
      norm (g (scaledLogWindowTest eta L c)) <= 1 := by
    have hc : 0 < c := by linarith only [hc1]
    have h := scaledLogWindowTest_gamma_norm_le he hL hc
    have hE := Real.add_one_le_exp (2*c)
    have hd : 0 < Real.exp (2*c)-1 := by linarith only [hE, hc1]
    have hnum : L <= Real.exp (2*c)-1 := by linarith only [hL1, hE, hc1]
    calc
      _ <= L/(Real.exp (2*c)-1) := h
      _ <= (Real.exp (2*c)-1)/(Real.exp (2*c)-1) :=
        div_le_div_of_nonneg_right hnum hd.le
      _ = 1 := div_self hd.ne'
  have htL : theta*movingSquareLogWidth x <= 1/8 := by
    have h := mul_le_mul_of_nonneg_right ht1 hp.1.le
    linarith only [h, hp.2.1]
  have htL0 : 0 <= theta*movingSquareLogWidth x := mul_nonneg ht0.le hp.1.le
  have hLi : 0 < (1-2*theta)*movingSquareLogWidth x :=
    mul_pos (by linarith only [ht1]) hp.1
  have hLo : 0 < (1+2*theta)*movingSquareLogWidth x :=
    mul_pos (by linarith only [ht0]) hp.1
  have hLi1 : (1-2*theta)*movingSquareLogWidth x <= 1 := by
    nlinarith only [hp.2.1, htL0]
  have hLo1 : (1+2*theta)*movingSquareLogWidth x <= 1 := by
    nlinarith only [hp.2.1, htL]
  have hci : 1 <= Real.log x+theta*movingSquareLogWidth x := by
    linarith only [hp.2.2.1, htL0]
  have hco : 1 <= Real.log x-theta*movingSquareLogWidth x := by
    linarith only [hp.2.2.1, htL]
  have hgi : norm (g (squareCorridorInnerTest theta eta x)) <= 1 :=
    hg _ _ hLi hLi1 hci
  have hgo : norm (g (squareCorridorOuterTest theta eta x)) <= 1 :=
    hg _ _ hLo hLo1 hco
  have hgiRe : -1 <= (g (squareCorridorInnerTest theta eta x)).re :=
    (neg_le_neg ((Complex.abs_re_le_norm _).trans hgi)).trans (neg_abs_le _)
  have hgoRe : (g (squareCorridorOuterTest theta eta x)).re <= 1 :=
    (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans hgo)
  have hPi := prime_count_ge_contracted_square_corridor_test hn ht0 ht1 he hx0 hx1
  have hPu := prime_count_le_expanded_square_corridor_test hn ht0 ht1 he het hx0 hx1
  have hlogA : 0 < Real.log ((n+1)*(n+1) : Nat) :=
    Real.log_pos (by exact_mod_cast (show 1 < (n+1)*(n+1) by nlinarith))
  have hEi : (2*(n : Real)-2)*(1-2*theta)*(1-2*eta)-1-
        (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex)*
            Zeta23.paperFT (squareCorridorInnerTest theta eta x)
              (Zeta23.gammaOf rho))).re <=
      (squareIntervalExplicitValue (squareCorridorInnerTest theta eta x)).re := by
    simp only [squareIntervalExplicitValue, Complex.add_re, Complex.sub_re]
    simp only [g, Complex.add_re] at hgiRe
    linarith only [hpo.1, hgiRe]
  have hEo : (squareIntervalExplicitValue (squareCorridorOuterTest theta eta x)).re <=
      (2*(n : Real)+7)*(1+4*theta)+1-
        (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex)*
            Zeta23.paperFT (squareCorridorOuterTest theta eta x)
              (Zeta23.gammaOf rho))).re := by
    simp only [squareIntervalExplicitValue, Complex.add_re, Complex.sub_re]
    simp only [g, Complex.add_re] at hgoRe
    linarith only [hpo.2, hgoRe]
  exact And.intro
    ((sub_le_sub_right (div_le_div_of_nonneg_right hEi hlogA.le) _).trans hPi)
    (hPu.trans hEo)

end RobinBV.Sieve
