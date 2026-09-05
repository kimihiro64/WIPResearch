import PrimeNumberTheoremAnd.Consequences
import RobinBV.NumberField.Proof.MovingPrimorialEndpoint

/-!
# Moving primorial corrections at every prime-power scale

The complete positive-integral sandwich is squeezed using the ordinary PNT
for theta and pi. The PNT providers are the proved declarations
chebyshev_asymptotic and pi_alt' from PrimeNumberTheoremAnd, reviewed at
f8f58c749d6cde8a641348fcd5e4702993651cd6. Only theta(P)/P -> 1 is used;
there is no square-root error assumption and no fixed-modulus substitution.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter Asymptotics

noncomputable section

/-- The real part of the complete moving primorial correction has its exact
leading coefficient at every fixed positive integer power scale. -/
theorem movingPrimorialCorrection_normalized_re_tendsto (k : Nat) :
    Tendsto (fun P : Nat => ((P : Real) ^ k * Real.log P) *
      (movingPrimorialCorrection P ((P : Real) ^ (k + 1))).re) atTop (nhds (-1 : Real)) := by
  have hThetaNe : Filter.Eventually (fun x : Real => Not (id x = 0)) atTop := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    exact hx.ne'
  have hThetaReal : Tendsto (fun x : Real => Chebyshev.theta x / x) atTop (nhds (1 : Real)) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hThetaNe).1 chebyshev_asymptotic
  have hTheta : Tendsto (fun P : Nat => Chebyshev.theta (P : Real) / (P : Real))
      atTop (nhds (1 : Real)) := hThetaReal.comp tendsto_natCast_atTop_atTop
  have hPiNe : Filter.Eventually (fun x : Real => Not (x / Real.log x = 0)) atTop := by
    filter_upwards [Filter.eventually_gt_atTop (1 : Real)] with x hx
    exact div_ne_zero (by linarith) (Real.log_pos hx).ne'
  have hPiReal := (Asymptotics.isEquivalent_iff_tendsto_one hPiNe).1 pi_alt'
  have hPi : Tendsto (fun P : Nat => (Nat.primeCounting P : Real) * Real.log P / (P : Real))
      atTop (nhds (1 : Real)) := by
    have hComp := hPiReal.comp (tendsto_natCast_atTop_atTop :
      Tendsto (fun P : Nat => (P : Real)) atTop atTop)
    change Tendsto (fun P : Nat => (Nat.primeCounting (Nat.floor (P : Real)) : Real) /
      ((P : Real) / Real.log P)) atTop (nhds (1 : Real)) at hComp
    simpa only [Nat.floor_natCast, div_div_eq_mul_div] using hComp
  have hLog : Tendsto (fun P : Nat => Real.log (P : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hInvLog : Tendsto (fun P : Nat => 1 / Real.log (P : Real)) atTop (nhds (0 : Real)) := by
    have hInv : Tendsto (fun P : Nat => Inv.inv (Real.log (P : Real))) atTop (nhds (0 : Real)) :=
      tendsto_inv_atTop_zero.comp hLog
    simpa only [one_div] using hInv
  have hSmall : Tendsto (fun P : Nat => 1 / (((k + 1 : Nat) : Real) * Real.log P))
      atTop (nhds (0 : Real)) := by
    have hRaw := hInvLog.const_mul (1 / ((k + 1 : Nat) : Real))
    simpa [div_eq_mul_inv, mul_comm] using hRaw
  have hUpper : Tendsto (fun P : Nat =>
      ((Nat.primeCounting P : Real) * Real.log P / (P : Real)) *
        (1 + 1 / (((k + 1 : Nat) : Real) * Real.log P))) atTop (nhds (1 : Real)) := by
    simpa only [add_zero, mul_one] using hPi.mul (hSmall.const_add 1)
  have hBounds := (Filter.eventually_ge_atTop (3 : Nat)).mono
    (fun P hP => movingPrimorialCorrection_normalized_sandwich P k hP)
  have hPositive : Tendsto (fun P : Nat => ((P : Real) ^ k * Real.log P) *
      -(movingPrimorialCorrection P ((P : Real) ^ (k + 1))).re) atTop (nhds (1 : Real)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hTheta hUpper
      (hBounds.mono (fun _ h => h.1)) (hBounds.mono (fun _ h => h.2))
  convert hPositive.neg using 1
  funext P
  ring

/-- The entire complex moving primorial correction, not merely its real
part or a selected prime-power truncation, has normalized limit -1. -/
theorem movingPrimorialCorrection_normalized_tendsto (k : Nat) :
    Tendsto (fun P : Nat => (((P : Real) ^ k * Real.log P : Real) : Complex) *
      movingPrimorialCorrection P ((P : Real) ^ (k + 1))) atTop (nhds (-1 : Complex)) := by
  have hReal := movingPrimorialCorrection_normalized_re_tendsto k
  have hCast : Tendsto (fun P : Nat =>
      ((((P : Real) ^ k * Real.log P) *
        (movingPrimorialCorrection P ((P : Real) ^ (k + 1))).re : Real) : Complex))
      atTop (nhds (-1 : Complex)) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_one] using hReal.ofReal
  apply hCast.congr'
  filter_upwards [Filter.eventually_ge_atTop (3 : Nat)] with P hP
  have hPow : 0 < P ^ k := Nat.pow_pos (show 0 < P by omega)
  have hNat : 3 <= P ^ (k + 1) := by rw [pow_succ]; nlinarith
  have hx : 3 <= (P : Real) ^ (k + 1) := by exact_mod_cast hNat
  have hIm := movingPrimorialCorrection_im P hx
  apply Complex.ext
  next =>
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  next =>
    simp only [Complex.mul_im, Complex.ofReal_im, hIm, mul_zero, zero_mul, add_zero]

/-- At the moving square-root sieve scale, the complete correction has
coefficient -2 in the exact RH normalization sqrt(x)*log(x), x=P^2. -/
theorem movingPrimorial_square_critical_shift :
    Tendsto (fun P : Nat =>
      ((Real.sqrt ((P : Real) ^ 2) * Real.log ((P : Real) ^ 2) : Real) : Complex) *
        movingPrimorialCorrection P ((P : Real) ^ 2)) atTop (nhds (-2 : Complex)) := by
  have h := (movingPrimorialCorrection_normalized_tendsto 1).const_mul (2 : Complex)
  convert h using 1
  next =>
    funext P
    simp only [Real.sqrt_sq (Nat.cast_nonneg P), Real.log_pow, pow_one]
    push_cast
    ring
  next =>
    norm_num

end

end RobinBV.NumberField
