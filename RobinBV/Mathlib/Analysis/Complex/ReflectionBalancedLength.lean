/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Balanced reflection length

This explicit length choice and its algebraic identities are consumed by the
reflection energy estimate. The bounds retain the full epsilon dependence.
-/

set_option autoImplicit false

noncomputable def reflectionBalancedLength (R T epsilon : Real) : Real :=
  R^(1/4 : Real)*T^((1+epsilon)/2)

theorem reflection_balanced_length_spec {R T epsilon : Real}
    (hR : 1 <= R) (hT : 2 <= T) (hepsilon : 0 < epsilon)
    (hRT : R <= T^3) :
    1 <= reflectionBalancedLength R T epsilon /\
    reflectionBalancedLength R T epsilon <= T^(3+2*epsilon) /\
    (reflectionBalancedLength R T epsilon)^2 =
      Real.sqrt R*T^(1+epsilon) /\
    R*reflectionBalancedLength R T epsilon =
      R^(5/4 : Real)*T^(1/2 : Real)*T^(epsilon/2) := by
  have hR0 : 0 <= R := zero_le_one.trans hR
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hT1 : 1 <= T := by linarith only [hT]
  have hT0 : 0 <= T := zero_le_one.trans hT1
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hRp : 1 <= R^(1/4 : Real) := Real.one_le_rpow hR (by norm_num)
  have hTp : 1 <= T^((1+epsilon)/2) :=
    Real.one_le_rpow hT1 (by linarith only [hepsilon])
  have hU : 1 <= reflectionBalancedLength R T epsilon := by
    unfold reflectionBalancedLength
    simpa only [one_mul] using! mul_le_mul hRp hTp zero_le_one
      (zero_le_one.trans hRp)
  have hquarter : R^(1/4 : Real) <= T^(3/4 : Real) := by
    calc
      _ <= (T^3)^(1/4 : Real) := Real.rpow_le_rpow hR0 hRT (by norm_num)
      _ = _ := by
        rw [<- Real.rpow_natCast_mul hT0]
        norm_num only [Nat.cast_ofNat]
  have hupper : reflectionBalancedLength R T epsilon <= T^(3+2*epsilon) := by
    calc
      _ <= T^(3/4 : Real)*T^((1+epsilon)/2) :=
        mul_le_mul_of_nonneg_right hquarter (Real.rpow_nonneg hT0 _)
      _ = T^((3/4 : Real)+(1+epsilon)/2) :=
        (Real.rpow_add hTpos _ _).symm
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hepsilon])
  have hRtwo : (R^(1/4 : Real))^2 = Real.sqrt R := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_mul_natCast hR0]
    norm_num only [Nat.cast_ofNat]
  have hTtwo : (T^((1+epsilon)/2))^2 = T^(1+epsilon) := by
    rw [<- Real.rpow_mul_natCast hT0]
    norm_num only [Nat.cast_ofNat]
    have he : (1+epsilon)/2*(2 : Real) = 1+epsilon := by ring
    rw [he]
  have hsquare : (reflectionBalancedLength R T epsilon)^2 =
      Real.sqrt R*T^(1+epsilon) := by
    unfold reflectionBalancedLength
    rw [mul_pow, hRtwo, hTtwo]
  have hRmass : R*R^(1/4 : Real) = R^(5/4 : Real) := by
    calc
      _ = R^((1 : Real)+1/4) := by rw [Real.rpow_add hRpos, Real.rpow_one]
      _ = _ := by norm_num
  have hTmass : T^((1+epsilon)/2) = T^(1/2 : Real)*T^(epsilon/2) := by
    have he : (1+epsilon)/2 = (1/2 : Real)+epsilon/2 := by ring
    rw [he, Real.rpow_add hTpos]
  refine And.intro hU (And.intro hupper (And.intro hsquare ?_))
  unfold reflectionBalancedLength
  rw [<- mul_assoc, hRmass, hTmass]
  ring
