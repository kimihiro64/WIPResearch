import RobinBV.NumberField.Proof.PrimeMomentTail

/-!
# Complete prime-cap errors at general hierarchy scales

At x=P^m, a root layer j>=m+1 has its exact cap threshold P^j.
The ratio to the selected L-root normalization has a strictly negative
power exponent. The full late-start integral bound is retained throughout.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter

noncomputable section

/-- Every complete prime-cap error from an omitted layer is negligible
at any selected L-root scale, with exact finite threshold normalization. -/
theorem rootPrimeCharacterTail_hierarchy_cap_error_tendsto
    {N : Nat} (chi : DirichletCharacter Complex N) (m L j : Nat)
    (hm : 1 <= m) (hL : 2 <= L) (hj : m + 1 <= j) :
    Tendsto (fun P : Nat =>
      (((((P : Real) ^ m) ^ (1 - Inv.inv (L : Real)) * Real.log ((P : Real) ^ m) : Real) : Complex) *
        (rootPrimeCharacterTail chi (Inv.inv (j : Real)) ((P : Real) ^ m) -
          cappedRootPrimeCharacterTail chi P (Inv.inv (j : Real)) ((P : Real) ^ m))))
      atTop (nhds (0 : Complex)) := by
  let r : Real := Inv.inv (j : Real)
  let s : Real := Inv.inv (L : Real)
  let b : Real := (m : Real) * (1 - s) - ((j : Real) - 1)
  let C : Real := (Real.log 4 + 4) / (1 - r) + (Real.log 4 + 4)
  let R : Nat -> Real := fun P => ((m : Real) / (j : Real)) * (P : Real) ^ b
  have hmPos : (0 : Real) < m := by exact_mod_cast (show 0 < m by omega)
  have hjPos : (0 : Real) < j := by exact_mod_cast (show 0 < j by omega)
  have hJReal : (m : Real) + 1 <= j := by exact_mod_cast hj
  have hsPos : 0 < s := by dsimp only [s]; positivity
  have hb : b < 0 := by dsimp only [b]; nlinarith [mul_pos hmPos hsPos]
  have hr0 : 0 <= r := by dsimp only [r]; positivity
  have hr1 : r < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le (n := 1) (k := j)
      (by norm_num) (by omega)
  have hPowerLimit : Tendsto (fun P : Nat => (P : Real) ^ b) atTop (nhds (0 : Real)) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hb)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  have hUpper : Tendsto (fun P : Nat => R P * C) atTop (nhds (0 : Real)) := by
    simpa only [mul_zero, zero_mul] using (hPowerLimit.const_mul ((m : Real) / (j : Real))).mul_const C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with P hP
  have hPPos : 0 < (P : Real) := by exact_mod_cast (show 0 < P by omega)
  have hGeNat : P <= P ^ m := by
    have hPositive : 0 < P ^ (m - 1) := Nat.pow_pos (by omega)
    have hIndex : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have hProduct : P ^ m = P ^ (m - 1) * P := by
      calc
        _ = P ^ (m - 1 + 1) := congrArg (fun i : Nat => P ^ i) hIndex.symm
        _ = _ := pow_succ P (m - 1)
    rw [hProduct]
    nlinarith
  have hx : 1 < (P : Real) ^ m := by exact_mod_cast (show 1 < P ^ m by omega)
  have hLeNat : P ^ m <= P ^ j := by
    have hPositive : 0 < P ^ (j - m) := Nat.pow_pos (by omega)
    have hIndex : j - m + m = j := Nat.sub_add_cancel (show m <= j by omega)
    have hProduct : P ^ j = P ^ (j - m) * P ^ m := by
      calc
        _ = P ^ (j - m + m) := congrArg (fun i : Nat => P ^ i) hIndex.symm
        _ = _ := pow_add P (j - m) m
    rw [hProduct]
    nlinarith
  have hxT : (P : Real) ^ m <= (P : Real) ^ j := by exact_mod_cast hLeNat
  have hCap : ((P : Real) ^ j) ^ r = (P : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hPPos.le]
    dsimp only [r]
    rw [show (j : Real) * Inv.inv (j : Real) = 1 by field_simp, Real.rpow_one]
  have hThresholdPower : ((P : Real) ^ j) ^ (1 - r) = (P : Real) ^ ((j : Real) - 1) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hPPos.le]
    congr 1
    dsimp only [r]
    field_simp [hjPos.ne']
  have hMainPower : ((P : Real) ^ m) ^ (1 - s) = (P : Real) ^ ((m : Real) * (1 - s)) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hPPos.le]
  have hPowers : (P : Real) ^ b * (P : Real) ^ ((j : Real) - 1) =
      (P : Real) ^ ((m : Real) * (1 - s)) := by
    rw [<- Real.rpow_add hPPos]
    congr 1
    dsimp only [b]
    ring
  have hNormalize : ((P : Real) ^ m) ^ (1 - s) * Real.log ((P : Real) ^ m) =
      R P * (((P : Real) ^ j) ^ (1 - r) * Real.log ((P : Real) ^ j)) := by
    rw [hMainPower, Real.log_pow, hThresholdPower, Real.log_pow]
    dsimp only [R]
    rw [<- hPowers]
    field_simp [hjPos.ne']
  have hR : 0 <= R P := by dsimp only [R]; positivity
  have hBound := rootPrimeCharacterTail_cap_error_scaled_le chi P hr0 hr1 hx hxT hCap
  rw [hNormalize, Complex.ofReal_mul, mul_assoc, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hR]
  exact mul_le_mul_of_nonneg_left hBound hR

end

end RobinBV.NumberField
