/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalPrimePowerMass
import Zeta23.WeilEF.Main

/-!
# Square-interval prime counts from the actual zeta explicit formula

The arithmetic side is exactly supported in the open square interval. Both
pole terms, the signed gamma integral and the full absolutely summable zeta-zero
series are retained. The prime-power correction is fully explicit. This module
does not assert an estimate for the zero series or an almost-all theorem.

The explicit-formula provider is Zeta23.WeilEF.EF_lit_zetaZeroConfig, from the
pinned Apache-2.0 dependency documented in SIBLING_CAPABILITIES.md.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

noncomputable def squareIntervalExplicitValue (k : Real -> Complex) : Complex :=
  Zeta23.paperFT k (Complex.I/2) + Zeta23.paperFT k (-Complex.I/2) +
    (1/(2*Real.pi) : Complex) *
      MeasureTheory.integral MeasureTheory.volume (fun r : Real =>
        Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : Complex)) -
    tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT k (Zeta23.gammaOf rho))

theorem square_interval_mangoldt_test_eq_explicit
    {n : Nat} {k : Real -> Complex}
    (hk : ContDiff Real 2 k) (hkc : HasCompactSupport k)
    (hsupport : forall m : Nat,
      Not (Membership.mem (Finset.Ioo (n*n) ((n+1)*(n+1))) m) ->
        k (Real.log m) = 0)
    (hnegative : forall m : Nat, k (-Real.log m) = 0) :
    Finset.sum (Finset.Ioo (n*n) ((n+1)*(n+1)))
      (fun m => ArithmeticFunction.vonMangoldt m *
        ((k (Real.log m)).re / Real.sqrt m)) =
      (squareIntervalExplicitValue k).re := by
  classical
  let I : Finset Nat := Finset.Ioo (n*n) ((n+1)*(n+1))
  let a : Nat -> Complex := fun m =>
    ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : Real) : Complex) *
      (k (Real.log m) + k (-Real.log m))
  have ef := (Zeta23.WeilEF.EF_lit_zetaZeroConfig k hk hkc).2
  have ha : tsum a = squareIntervalExplicitValue k := by
    dsimp [a, squareIntervalExplicitValue]
    unfold Zeta23.EF.literatureRHS at ef
    dsimp [Zeta23.zetaZeroConfig] at ef
    linear_combination ef
  have hfinite : tsum a = Finset.sum I a := by
    apply tsum_eq_sum
    intro m hm
    change ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : Real) : Complex) *
      (k (Real.log m) + k (-Real.log m)) = 0
    rw [hsupport m hm, hnegative m]
    simp only [add_zero, mul_zero]
  have hmap : (Finset.sum I a).re = Finset.sum I (fun m => (a m).re) :=
    map_sum Complex.reAddGroupHom a I
  calc
    _ = Finset.sum I (fun m => (a m).re) := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp [a]
      rw [hnegative m]
      simp only [add_zero, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      ring
    _ = (Finset.sum I a).re := hmap.symm
    _ = (tsum a).re := congrArg Complex.re hfinite.symm
    _ = (squareIntervalExplicitValue k).re := congrArg Complex.re ha

theorem prime_count_ge_square_interval_explicit_formula
    {n : Nat} (hn : 2 <= n) {k : Real -> Complex}
    (hk : ContDiff Real 2 k) (hkc : HasCompactSupport k)
    (hsupport : forall m : Nat,
      Not (Membership.mem (Finset.Ioo (n*n) ((n+1)*(n+1))) m) ->
        k (Real.log m) = 0)
    (hnegative : forall m : Nat, k (-Real.log m) = 0)
    (hweight : forall m : Nat,
      Membership.mem (Finset.Ioo (n*n) ((n+1)*(n+1))) m ->
        0 <= (k (Real.log m)).re / Real.sqrt m /\
          (k (Real.log m)).re / Real.sqrt m <= 1) :
    (squareIntervalExplicitValue k).re /
        Real.log ((n+1)*(n+1) : Nat) -
      (((n+1)*(n+1) : Nat) : Real)^(1/3 : Real) *
        Real.log ((n+1)*(n+1) : Nat) / Real.log 2 <=
      ((Nat.PrimeSieve.squareIntervalPrimes n).card : Real) := by
  let A : Nat := (n+1)*(n+1)
  let P : Real := (Nat.PrimeSieve.squareIntervalPrimes n).card
  let E : Real := (A : Real)^(1/3 : Real) *
    (Real.log (A : Real))^2 / Real.log 2
  have hA : 1 < A := by dsimp [A]; nlinarith
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast hA)
  have hlog2 : Not (Real.log (2 : Real) = 0) :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : Real) < 2))
  have hmass := Nat.PrimeSieve.square_interval_weighted_mangoldt_le n
    (fun m => (k (Real.log m)).re / Real.sqrt m) hweight
  rw [square_interval_mangoldt_test_eq_explicit hk hkc hsupport hnegative] at hmass
  change (squareIntervalExplicitValue k).re <= P*Real.log (A : Real)+E at hmass
  have hsub : (squareIntervalExplicitValue k).re-E <= P*Real.log (A : Real) := by
    linarith only [hmass]
  calc
    _ = ((squareIntervalExplicitValue k).re-E) *
        Inv.inv (Real.log (A : Real)) := by
      dsimp [E, A]
      field_simp [hlogA.ne', hlog2]
    _ <= (P*Real.log (A : Real))*Inv.inv (Real.log (A : Real)) :=
      mul_le_mul_of_nonneg_right hsub (inv_nonneg.mpr hlogA.le)
    _ = P := by field_simp [hlogA.ne']

end RobinBV.Sieve
