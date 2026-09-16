/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Arithmetic error budget for the square-corridor deviation proof

These deliberately coarse constants pay the particular complete prime-power
and logarithmic errors in the actual prime-count corridor. The arithmetic
threshold is explicit; it is not a threshold for an analytic zero estimate.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem squareCorridor_primePower_budget {n : Real} (hn : 1 <= n) :
    ((n+1)^2)^(1/3 : Real)*(Real.log ((n+1)^2))^2/Real.log 2+5 <=
      2309*n^(5/6 : Real) := by
  have hn0 : 0 < n := by linarith only [hn]
  have ht : 0 < n+1 := by linarith only [hn]
  have hlog2 : 1/2 <= Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hlog20 : 0 < Real.log 2 := by linarith only [hlog2]
  have hrec : 1/Real.log 2 <= 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1/2) hlog2
    norm_num at h
    simpa only [one_div] using h
  have hlog := Real.log_le_rpow_div ht.le (by norm_num : (0 : Real) < 1/12)
  have hlogA : Real.log ((n+1)^2) <= 24*(n+1)^(1/12 : Real) := by
    rw [Real.log_pow]
    norm_num
    linarith only [hlog]
  have hlogA0 : 0 <= Real.log ((n+1)^2) :=
    Real.log_nonneg (by nlinarith only [hn])
  have hsq : (Real.log ((n+1)^2))^2 <= 576*((n+1)^(1/12 : Real))^2 := by
    have h := mul_le_mul hlogA hlogA hlogA0 (show 0 <= 24*(n+1)^(1/12 : Real) by positivity)
    calc
      _ = Real.log ((n+1)^2)*Real.log ((n+1)^2) := by ring
      _ <= (24*(n+1)^(1/12 : Real))*(24*(n+1)^(1/12 : Real)) := h
      _ = _ := by ring
  have hpow : ((n+1)^2)^(1/3 : Real) = (n+1)^(2/3 : Real) := by
    calc
      _ = ((n+1)^(2 : Real))^(1/3 : Real) := by norm_num
      _ = (n+1)^((2 : Real)*(1/3)) := (Real.rpow_mul ht.le 2 (1/3)).symm
      _ = _ := by norm_num
  have hsqpow : ((n+1)^(1/12 : Real))^2 = (n+1)^(1/6 : Real) := by
    calc
      _ = ((n+1)^(1/12 : Real))^(2 : Real) := by norm_num
      _ = (n+1)^((1/12 : Real)*2) := (Real.rpow_mul ht.le (1/12) 2).symm
      _ = _ := by norm_num
  have hprod : (n+1)^(2/3 : Real)*((n+1)^(1/12 : Real))^2 =
      (n+1)^(5/6 : Real) := by
    rw [hsqpow, <- Real.rpow_add ht]
    norm_num
  have hmass : ((n+1)^2)^(1/3 : Real)*(Real.log ((n+1)^2))^2/Real.log 2 <=
      1152*(n+1)^(5/6 : Real) := by
    rw [hpow]
    calc
      _ <= ((n+1)^(2/3 : Real)*(576*((n+1)^(1/12 : Real))^2))/Real.log 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg ht.le _)) hlog20.le
      _ = 576*((n+1)^(2/3 : Real)*((n+1)^(1/12 : Real))^2)/Real.log 2 := by ring
      _ = (576*(n+1)^(5/6 : Real))*(1/Real.log 2) := by rw [hprod]; ring
      _ <= (576*(n+1)^(5/6 : Real))*2 :=
        mul_le_mul_of_nonneg_left hrec (by positivity)
      _ = _ := by ring
  have htwo : (2 : Real)^(5/6 : Real) <= 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2)
      (by norm_num : (5/6 : Real) <= 1)
    simpa only [Real.rpow_one] using h
  have hnp : (n+1)^(5/6 : Real) <= 2*n^(5/6 : Real) := by
    calc
      _ <= (2*n)^(5/6 : Real) :=
        Real.rpow_le_rpow ht.le (by linarith only [hn]) (by norm_num)
      _ = (2 : Real)^(5/6 : Real)*n^(5/6 : Real) :=
        Real.mul_rpow (by norm_num) hn0.le
      _ <= _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hn0.le _)
  have hscale := mul_le_mul_of_nonneg_left hnp (by norm_num : (0 : Real) <= 1152)
  have hbig := Real.one_le_rpow hn (by norm_num : (0 : Real) <= 5/6)
  linarith only [hmass, hscale, hbig]

theorem squareCorridor_primePower_budget_at_explicit_threshold
    {n delta : Real} (hn : 1 <= n) (hd : 0 < delta)
    (hlarge : (5000/delta)^6 <= n) :
    ((n+1)^2)^(1/3 : Real)*(Real.log ((n+1)^2))^2/Real.log 2+5 <=
      delta*n/2 /\ 5000 <= delta*n := by
  have hn0 : 0 < n := by linarith only [hn]
  have hbase : 0 < 5000/delta := div_pos (by norm_num) hd
  have hroot : 5000/delta <= n^(1/6 : Real) := by
    have hpow : (5000/delta)^(6 : Real) <= n := by
      norm_num
      exact hlarge
    have h := (Real.le_rpow_inv_iff_of_pos hbase.le hn0.le
      (by norm_num : (0 : Real) < 6)).mpr hpow
    simpa only [one_div] using h
  have h5000 : 5000 <= delta*n^(1/6 : Real) := by
    have h := mul_le_mul_of_nonneg_left hroot hd.le
    have he : delta*(5000/delta) = 5000 := by field_simp
    rwa [he] at h
  have hid : n^(1/6 : Real)*n^(5/6 : Real) = n := by
    rw [<- Real.rpow_add hn0]
    norm_num
  have hbudget : ((n+1)^2)^(1/3 : Real)*(Real.log ((n+1)^2))^2/Real.log 2+5 <=
      delta*n/2 := by
    calc
      _ <= 2309*n^(5/6 : Real) := squareCorridor_primePower_budget hn
      _ <= (delta*n^(1/6 : Real)/2)*n^(5/6 : Real) :=
        mul_le_mul_of_nonneg_right (by linarith only [h5000])
          (Real.rpow_nonneg hn0.le _)
      _ = (delta/2)*(n^(1/6 : Real)*n^(5/6 : Real)) := by ring
      _ = delta*n/2 := by rw [hid]; ring
  have hrn : n^(1/6 : Real) <= n :=
    Real.rpow_le_self_of_one_le hn (by norm_num)
  exact And.intro hbudget (h5000.trans (mul_le_mul_of_nonneg_left hrn hd.le))

end RobinBV.Sieve
