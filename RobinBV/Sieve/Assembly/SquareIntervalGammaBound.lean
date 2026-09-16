/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Sieve.Helpers.SquareIntervalMovingTest
import RobinBV.Sieve.Proof.SquareIntervalExplicitFormula
import RobinBV.Sieve.Proof.SquareIntervalGammaCorrection
import RobinBV.Sieve.Proof.SquareIntervalPoleSupply
import RobinBV.Sieve.Proof.SquareIntervalZeroKernel

/-!
# Prime-count explicit formula with complete gamma correction

The concrete square-interval test discharges every test-function condition.
The gamma packet is replaced by an explicit negative allowance. A second
consumer also bounds the growing pole from below on the inner core, retaining
the full signed actual-zeta sum. No zero estimate or almost-all prime-count
theorem is asserted. Import this module separately
from the existing RobinBV root; the pinned providers have a documented
joint-namespace limitation.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem prime_count_ge_square_interval_moving_test {n : Nat} (hn : 2 <= n)
    {w : Real} (hw : 0 < w) :
    (squareIntervalExplicitValue (squareIntervalLogTest n w)).re /
        Real.log ((n+1)*(n+1) : Nat) -
      (((n+1)*(n+1) : Nat) : Real)^(1/3 : Real) *
        Real.log ((n+1)*(n+1) : Nat) / Real.log 2 <=
      ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) :=
  prime_count_ge_square_interval_explicit_formula hn
    (squareIntervalLogTest_contDiff n w)
    (squareIntervalLogTest_hasCompactSupport hw)
    (squareIntervalLogTest_arithmetic_support hn hw)
    (squareIntervalLogTest_negative hn hw)
    (squareIntervalLogTest_weight hn w)

theorem squareIntervalLogTest_gamma_lower {n : Nat} (hn : 2 <= n)
    {w : Real} (hw : 0 < w) :
    -(Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat))/((n : Real)^4-1) <=
      ((1/(2*Real.pi) : Complex)*MeasureTheory.integral MeasureTheory.volume
        (fun r : Real => Zeta23.paperFT (squareIntervalLogTest n w) r *
          (Zeta23.EF.gammaBracket r : Complex)) +
        Zeta23.paperFT (squareIntervalLogTest n w) (Complex.I/2)).re := by
  have hnn : (0 : Real) < (n*n : Nat) := by exact_mod_cast (by nlinarith : 0 < n*n)
  have hc : 0 < Real.log (n*n : Nat) :=
    Real.log_pos (by exact_mod_cast (by nlinarith : 1 < n*n))
  have hcd : Real.log (n*n : Nat) <= Real.log ((n+1)*(n+1) : Nat) :=
    Real.log_le_log hnn (by exact_mod_cast (by nlinarith : n*n <= (n+1)*(n+1)))
  have hsupport : forall u : Real,
      Not (Membership.mem (Set.Icc (Real.log (n*n : Nat))
        (Real.log ((n+1)*(n+1) : Nat))) u) -> squareIntervalLogTest n w u = 0 := by
    intro u hu
    by_cases hleft : u <= Real.log (n*n : Nat)
    next =>
      exact squareIntervalLogTest_zero_left hw hleft
    next =>
      apply squareIntervalLogTest_zero_right hw
      by_contra hright
      exact hu (And.intro (le_of_lt (lt_of_not_ge hleft))
        (le_of_lt (lt_of_not_ge hright)))
  have h := Zeta23.EF.gammaCorrection_norm_le
    (squareIntervalLogTest_contDiff n w) (squareIntervalLogTest_hasCompactSupport hw)
    hc hcd hsupport (fun u _ => squareIntervalLogTest_norm_le n w u)
  have hexp : Real.exp (2*Real.log (n*n : Nat)) = (n : Real)^4 := by
    rw [show 2*Real.log (n*n : Nat) =
      Real.log (n*n : Nat)+Real.log (n*n : Nat) by ring,
      Real.exp_add, Real.exp_log hnn]
    push_cast
    ring
  rw [hexp] at h
  have hre := Complex.abs_re_le_norm
    ((1/(2*Real.pi) : Complex)*MeasureTheory.integral MeasureTheory.volume
      (fun r : Real => Zeta23.paperFT (squareIntervalLogTest n w) r *
        (Zeta23.EF.gammaBracket r : Complex)) +
      Zeta23.paperFT (squareIntervalLogTest n w) (Complex.I/2))
  have hneg := neg_abs_le
    (((1/(2*Real.pi) : Complex)*MeasureTheory.integral MeasureTheory.volume
      (fun r : Real => Zeta23.paperFT (squareIntervalLogTest n w) r *
        (Zeta23.EF.gammaBracket r : Complex)) +
      Zeta23.paperFT (squareIntervalLogTest n w) (Complex.I/2)).re)
  rw [neg_div]
  exact (neg_le_neg (hre.trans h)).trans hneg

theorem prime_count_ge_square_interval_gamma_bound {n : Nat} (hn : 2 <= n)
    {w : Real} (hw : 0 < w) :
    ((Zeta23.paperFT (squareIntervalLogTest n w) (-Complex.I/2) -
        tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareIntervalLogTest n w) (Zeta23.gammaOf rho))).re -
      (Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat))/((n : Real)^4-1)) /
        Real.log ((n+1)*(n+1) : Nat) -
      (((n+1)*(n+1) : Nat) : Real)^(1/3 : Real) *
        Real.log ((n+1)*(n+1) : Nat)/Real.log 2 <=
      ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) := by
  have hlog : 0 < Real.log ((n+1)*(n+1) : Nat) :=
    Real.log_pos (by exact_mod_cast (by nlinarith : 1 < (n+1)*(n+1)))
  have hg := squareIntervalLogTest_gamma_lower hn hw
  have hP := prime_count_ge_square_interval_moving_test hn hw
  have hnum :
      (Zeta23.paperFT (squareIntervalLogTest n w) (-Complex.I/2) -
        tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareIntervalLogTest n w) (Zeta23.gammaOf rho))).re -
      (Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat))/((n : Real)^4-1) <=
        (squareIntervalExplicitValue (squareIntervalLogTest n w)).re := by
    simp only [squareIntervalExplicitValue, Complex.add_re, Complex.sub_re]
    simp only [Complex.add_re] at hg
    rw [neg_div] at hg
    linarith only [hg]
  exact (sub_le_sub_right (div_le_div_of_nonneg_right hnum hlog.le) _).trans hP

theorem prime_count_ge_square_interval_pole_bound {n : Nat} (hn : 2 <= n)
    {w : Real} (hw : 0 < w)
    (hwidth : 2*w <= Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat)) :
    ((n : Real)^2*(Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat)-2*w) -
      (Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat))/((n : Real)^4-1) -
      (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareIntervalLogTest n w) (Zeta23.gammaOf rho))).re) /
        Real.log ((n+1)*(n+1) : Nat) -
      (((n+1)*(n+1) : Nat) : Real)^(1/3 : Real) *
        Real.log ((n+1)*(n+1) : Nat)/Real.log 2 <=
      ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) := by
  have hlog : 0 < Real.log ((n+1)*(n+1) : Nat) :=
    Real.log_pos (by exact_mod_cast (by nlinarith : 1 < (n+1)*(n+1)))
  have hpole := squareIntervalLogTest_pole_lower hn hw hwidth
  have hP := prime_count_ge_square_interval_gamma_bound hn hw
  have hnum :
      (n : Real)^2*(Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat)-2*w) -
        (Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat))/((n : Real)^4-1) -
        (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareIntervalLogTest n w) (Zeta23.gammaOf rho))).re <=
      (Zeta23.paperFT (squareIntervalLogTest n w) (-Complex.I/2) -
        tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareIntervalLogTest n w) (Zeta23.gammaOf rho))).re -
        (Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat))/((n : Real)^4-1) := by
    rw [Complex.sub_re]
    linarith only [hpole]
  exact (sub_le_sub_right (div_le_div_of_nonneg_right hnum hlog.le) _).trans hP

theorem prime_count_ge_square_interval_unit_profile {n : Nat} (hn : 2 <= n)
    {eta : Real} (he : 0 < eta) (he2 : eta <= 1/2) :
    ((n : Real)^2*(squareIntervalLogWidth n-2*(eta*squareIntervalLogWidth n)) -
      squareIntervalLogWidth n/((n : Real)^4-1) -
      (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          ((squareIntervalLogWidth n : Complex) *
            Complex.exp ((rho : Complex)*(Real.log (n*n : Nat) : Complex)) *
            Zeta23.WeilEF.Hfn (unitLogWindowTest eta)
              ((squareIntervalLogWidth n : Complex)*(rho : Complex))))).re) /
        Real.log ((n+1)*(n+1) : Nat) -
      (((n+1)*(n+1) : Nat) : Real)^(1/3 : Real) *
        Real.log ((n+1)*(n+1) : Nat)/Real.log 2 <=
      ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) := by
  have hL := squareIntervalLogWidth_pos hn
  have hwidth : 2*(eta*squareIntervalLogWidth n) <=
      Real.log ((n+1)*(n+1) : Nat)-Real.log (n*n : Nat) := by
    change 2*(eta*squareIntervalLogWidth n) <= squareIntervalLogWidth n
    nlinarith
  have hP := prime_count_ge_square_interval_pole_bound hn (mul_pos he hL) hwidth
  rw [squareIntervalLogTest_eq_scaled hn he] at hP
  simp_rw [scaledLogWindowTest_paperFT_eq hL] at hP
  exact hP

end RobinBV.Sieve
