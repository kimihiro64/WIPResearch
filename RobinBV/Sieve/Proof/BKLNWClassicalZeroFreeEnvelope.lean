/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import PrimeNumberTheoremAnd.StrongPNT

/-!
# Uniform classical zero-free envelope

The maintained dependency proves a classical `E / log |t|` zero-free
inequality.  This file transfers it to a uniform finite-height envelope.  It
is an unconditional source input, but it is deliberately not advertised as
the stronger Korobov--Vinogradov `log^(2/3) loglog^(1/3)` envelope required by
the final almost-all theorem.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem rob_bv_classical_zero_free_uniform_envelope
    {T : Real} (hT : 2 <= T) :
    exists E : Real, 0 < E /\
      forall rho : Complex, riemannZeta rho = 0 ->
        2 <= |rho.im| -> |rho.im| <= T ->
          rho.re <= 1 - E / Real.log T := by
  have hE0 : 0 < (_root_.E : Real) := by
    exact EinIoo.1
  have hspec := ZeroInequalitySpec
  refine Exists.intro _root_.E (And.intro hE0 ?_)
  intro rho hz hlow hhigh
  have hlogrho : 0 < Real.log |rho.im| :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hlow)
  have hlogT : 0 < Real.log T :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hT)
  have hlog : Real.log |rho.im| <= Real.log T :=
    Real.log_le_log (by positivity) hhigh
  have hinv : 1 / Real.log T <= 1 / Real.log |rho.im| := by
    exact one_div_le_one_div_of_le hlogrho hlog
  have hspec' := hspec rho hz rho.re rfl rho.im rfl hlow
  have hscaled : _root_.E / Real.log T <= _root_.E / Real.log |rho.im| := by
    have hmul : _root_.E * (1 / Real.log T) <=
        _root_.E * (1 / Real.log |rho.im|) :=
      mul_le_mul_of_nonneg_left hinv hE0.le
    simpa [div_eq_mul_inv, one_div] using hmul
  calc
    rho.re <= 1 - _root_.E / Real.log |rho.im| := hspec'
    _ <= 1 - _root_.E / Real.log T := sub_le_sub_left hscaled 1

end RobinBV.Sieve
