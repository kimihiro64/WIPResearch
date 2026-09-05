import RobinBV.NumberField.Proof.MovingCharacterEndpoint
import RobinBV.NumberField.Proof.MovingPrimorialAsymptotic

/-!
# Complete principal domination after removing character power moments

The first m powers are removed exactly. Every remaining admitted power and
the full integration tail stay in the remainder, whose norm is bounded by
the complete positive principal residual, uniformly in the character.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

/-- Exact-prefix remainder domination for every complex character. The
right side is the entire principal residual, not a finite power truncation. -/
theorem movingCharacterCorrection_remainder_le
    {N : Nat} (chi : DirichletCharacter Complex N) (P m : Nat)
    {x : Real} (hx : 3 <= x) (hPm : ((P ^ m : Nat) : Real) <= x) :
    norm (movingCharacterCorrection chi P x +
      Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
        Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
          ((x : Complex) * (Real.log x : Complex))) <=
      -(movingPrimorialCorrection P x).re -
        (m : Real) * Chebyshev.theta (P : Real) / (x * Real.log x) := by
  let : NeZero (primorial P) := NeZero.mk (primorial_ne_zero P)
  let B : Complex := Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
    Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j))
  let S : Real -> Real := fun t => Finset.sum (Nat.primesLE P) (fun p =>
    Real.log p * (Nat.log p (Nat.floor t) : Real))
  let C : Real := (m : Real) * Chebyshev.theta (P : Real)
  have hxOne : 1 < x := by linarith
  have hWeight := Robin1984.integrableOn_robinRealWeight
    (by norm_num : 1 <= (1 : Nat)) hxOne
  have hFirst := (movingCharacterCorrection_integral_data chi P hx).1
  have hConst : IntegrableOn (fun t : Real => B * (Robin1984.robinRealWeight 1 t : Complex))
      (Ioi x) := hWeight.ofReal.const_mul B
  have hConstIntegral : integral (volume.restrict (Ioi x))
      (fun t : Real => B * (Robin1984.robinRealWeight 1 t : Complex)) =
        B / ((x : Complex) * (Real.log x : Complex)) := by
    rw [integral_const_mul, integral_complex_ofReal, Robin1984.integral_robinRealWeight
      (by norm_num : 1 <= (1 : Nat)) hxOne]
    norm_num [Real.rpow_neg_one]
    ring
  have hDifference := integrableOn_imprimitiveChebyshevStep_mul_weight
    (1 : DirichletCharacter Complex (primorial P)) hx
  have hSInt : IntegrableOn (fun t : Real => S t * Robin1984.robinRealWeight 1 t) (Ioi x) := by
    apply hDifference.neg.re.congr
    filter_upwards [] with t
    simp only [Pi.neg_apply, principalChebyshevStep_sub_primitive_eq_logFloorSum,
      neg_mul, neg_neg, <- Complex.ofReal_mul, primeFactors_primorial]
    rfl
  have hCInt := hWeight.const_mul C
  have hMajor : IntegrableOn (fun t : Real => (S t - C) * Robin1984.robinRealWeight 1 t) (Ioi x) := by
    have hRaw := hSInt.sub hCInt
    change IntegrableOn (fun t : Real => S t * Robin1984.robinRealWeight 1 t -
      C * Robin1984.robinRealWeight 1 t) (Ioi x) at hRaw
    simpa only [sub_mul] using hRaw
  have hBoundAE : Filter.Eventually (fun t : Real =>
      norm ((Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t) - B) *
        (Robin1984.robinRealWeight 1 t : Complex)) <= (S t - C) * Robin1984.robinRealWeight 1 t)
      (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hWeightNonneg := Robin1984.robinRealWeight_nonneg (n := 1) (hxOne.trans ht)
    have hSumEq : Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t) - B =
        Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t -
          (Real.log p : Complex) * Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) := by
      rw [Finset.sum_sub_distrib]
    have hSum : norm (Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t) - B) <=
        S t - C := by
      rw [hSumEq]
      calc
        _ <= Finset.sum (Nat.primesLE P) (fun p => norm (chi.primePowerChebyshevStep p t -
            (Real.log p : Complex) * Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j))) :=
          norm_sum_le _ _
        _ <= Finset.sum (Nat.primesLE P) (fun p =>
            Real.log p * ((Nat.log p (Nat.floor t) : Real) - (m : Real))) := by
          apply Finset.sum_le_sum
          intro p hp
          have hPrime := (Nat.mem_primesLE.mp hp).2
          have hLe := (Nat.mem_primesLE.mp hp).1
          have hPower : ((p ^ m : Nat) : Real) <= ((P ^ m : Nat) : Real) := by
            exact_mod_cast Nat.pow_le_pow_left hLe m
          have hExponent : m <= Nat.log p (Nat.floor t) :=
            Nat.le_log_of_pow_le hPrime.one_lt (Nat.le_floor ((hPower.trans hPm).trans ht.le))
          exact chi.norm_primePowerChebyshevStep_sub_prefix_le hPrime hExponent
        _ = _ := by
          simp only [mul_sub, Finset.sum_sub_distrib, <- Finset.sum_mul]
          rw [<- Chebyshev.theta_eq_sum_primesLE_log]
          dsimp only [S, C]
          ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeightNonneg]
    exact mul_le_mul_of_nonneg_right hSum hWeightNonneg
  have hNorm := norm_integral_le_of_norm_le hMajor hBoundAE
  have hCharacterIdentity : movingCharacterCorrection chi P x +
      B / ((x : Complex) * (Real.log x : Complex)) =
        -integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t) - B) *
            (Robin1984.robinRealWeight 1 t : Complex)) := by
    simp_rw [sub_mul]
    rw [integral_sub hFirst hConst, hConstIntegral]
    unfold movingCharacterCorrection
    ring
  have hSIntegral : integral (volume.restrict (Ioi x))
      (fun t : Real => S t * Robin1984.robinRealWeight 1 t) = -(movingPrimorialCorrection P x).re := by
    dsimp only [movingPrimorialCorrection]
    rw [principalCenteredWeightedIntegral_sub_zeta_eq_logFloorIntegral hx,
      Complex.neg_re, Complex.ofReal_re, neg_neg, primeFactors_primorial]
  have hCIntegral : integral (volume.restrict (Ioi x))
      (fun t : Real => C * Robin1984.robinRealWeight 1 t) = C / (x * Real.log x) := by
    rw [integral_const_mul, Robin1984.integral_robinRealWeight
      (by norm_num : 1 <= (1 : Nat)) hxOne]
    norm_num [Real.rpow_neg_one]
    ring
  have hMajorIntegral : integral (volume.restrict (Ioi x))
      (fun t : Real => (S t - C) * Robin1984.robinRealWeight 1 t) =
        -(movingPrimorialCorrection P x).re - C / (x * Real.log x) := by
    simp_rw [sub_mul]
    rw [integral_sub hSInt hCInt, hSIntegral, hCIntegral]
  change norm (movingCharacterCorrection chi P x + B / ((x : Complex) * (Real.log x : Complex))) <= _
  rw [hCharacterIdentity, norm_neg]
  exact hNorm.trans_eq hMajorIntegral

/-- The complete higher-power transfer error at a power-scale endpoint is
bounded independently of the modulus and of the character. -/
theorem movingCharacterCorrection_normalized_remainder_le
    {N : Nat} (chi : DirichletCharacter Complex N) (P k : Nat) (hP : 3 <= P) :
    norm ((((P : Real) ^ k * Real.log P : Real) : Complex) *
      movingCharacterCorrection chi P ((P : Real) ^ (k + 1)) +
        Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
          Finset.sum (Finset.Icc 1 (k + 1)) (fun j => chi (p : ZMod N) ^ j)) /
            (((k + 1 : Nat) : Complex) * (P : Complex))) <=
      -(((P : Real) ^ k * Real.log P) *
        (movingPrimorialCorrection P ((P : Real) ^ (k + 1))).re) -
          Chebyshev.theta (P : Real) / (P : Real) := by
  let x : Real := (P : Real) ^ (k + 1)
  let F : Real := (P : Real) ^ k * Real.log P
  let B : Complex := Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
    Finset.sum (Finset.Icc 1 (k + 1)) (fun j => chi (p : ZMod N) ^ j))
  have hPPos : (0 : Real) < P := by exact_mod_cast (show 0 < P by omega)
  have hPNe : Not ((P : Real) = 0) := hPPos.ne'
  have hLogPos : 0 < Real.log (P : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hK : Not (((k + 1 : Nat) : Real) = 0) := by exact_mod_cast Nat.succ_ne_zero k
  have hPC : Not ((P : Complex) = 0) := by exact_mod_cast hPNe
  have hKC : Not (((k + 1 : Nat) : Complex) = 0) := by exact_mod_cast hK
  have hLogC : Not ((Real.log (P : Real) : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hLogPos.ne'
  have hx : 3 <= x := by
    have hPow : 0 < P ^ k := Nat.pow_pos (show 0 < P by omega)
    have hNat : 3 <= P ^ (k + 1) := by rw [pow_succ]; nlinarith
    dsimp only [x]
    exact_mod_cast hNat
  have hF : 0 <= F := by dsimp only [F]; positivity
  have hBase := movingCharacterCorrection_remainder_le chi P (k + 1) hx
    (by simp only [x, Nat.cast_pow]; exact le_rfl)
  have hScaled := mul_le_mul_of_nonneg_left hBase hF
  have hPrefix : (F : Complex) * (B / ((x : Complex) * (Real.log x : Complex))) =
      B / (((k + 1 : Nat) : Complex) * (P : Complex)) := by
    dsimp only [F, x]
    rw [Real.log_pow]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
    rw [pow_succ]
    field_simp [hPC, hKC, hLogC]
  have hTheta : F * (((k + 1 : Nat) : Real) * Chebyshev.theta (P : Real) /
      (x * Real.log x)) = Chebyshev.theta (P : Real) / (P : Real) := by
    dsimp only [F, x]
    rw [Real.log_pow, pow_succ]
    field_simp [hPNe, hLogPos.ne', hK]
  have hNorm : norm ((F : Complex) * (movingCharacterCorrection chi P x +
      B / ((x : Complex) * (Real.log x : Complex)))) =
        F * norm (movingCharacterCorrection chi P x +
          B / ((x : Complex) * (Real.log x : Complex))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hF]
  rw [<- hNorm, mul_add, hPrefix, mul_sub, hTheta, mul_neg] at hScaled
  exact hScaled

/-- The character-independent complete residual tends to zero. This uses
only the ordinary PNT and the proved full moving principal limit. -/
theorem movingCharacterCorrection_remainder_majorant_tendsto (k : Nat) :
    Filter.Tendsto (fun P : Nat => -(((P : Real) ^ k * Real.log P) *
      (movingPrimorialCorrection P ((P : Real) ^ (k + 1))).re) -
        Chebyshev.theta (P : Real) / (P : Real)) Filter.atTop (nhds (0 : Real)) := by
  have hThetaNe : Filter.Eventually (fun x : Real => Not (id x = 0)) Filter.atTop := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    exact hx.ne'
  have hThetaReal : Filter.Tendsto (fun x : Real => Chebyshev.theta x / x)
      Filter.atTop (nhds (1 : Real)) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hThetaNe).1 chebyshev_asymptotic
  have hTheta : Filter.Tendsto (fun P : Nat => Chebyshev.theta (P : Real) / (P : Real))
      Filter.atTop (nhds (1 : Real)) := hThetaReal.comp tendsto_natCast_atTop_atTop
  simpa only [neg_neg, sub_self] using
    (movingPrimorialCorrection_normalized_re_tendsto k).neg.sub hTheta

/-- Uniform vanishing of the entire transfer error, even when the character
and its modulus vary with the cutoff. This asserts no uniform prime moment
estimate: the finite character moments remain explicitly in the formula. -/
theorem movingCharacterCorrection_uniform_moment_transfer (k : Nat)
    {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun P : Nat => forall N : Nat,
      forall chi : DirichletCharacter Complex N,
        norm ((((P : Real) ^ k * Real.log P : Real) : Complex) *
          movingCharacterCorrection chi P ((P : Real) ^ (k + 1)) +
            Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
              Finset.sum (Finset.Icc 1 (k + 1)) (fun j => chi (p : ZMod N) ^ j)) /
                (((k + 1 : Nat) : Complex) * (P : Complex))) < epsilon) Filter.atTop := by
  have hSmall := (movingCharacterCorrection_remainder_majorant_tendsto k).eventually
    (eventually_lt_nhds hEpsilon)
  filter_upwards [Filter.eventually_ge_atTop (3 : Nat), hSmall] with P hP hSmallP
  intro N chi
  exact (movingCharacterCorrection_normalized_remainder_le chi P k hP).trans_lt hSmallP

/-- For each character, the complete normalized integral differs from its
explicit finite power moment by a quantity tending to zero. -/
theorem movingCharacterCorrection_moment_transfer_tendsto
    {N : Nat} (chi : DirichletCharacter Complex N) (k : Nat) :
    Filter.Tendsto (fun P : Nat =>
      (((P : Real) ^ k * Real.log P : Real) : Complex) *
        movingCharacterCorrection chi P ((P : Real) ^ (k + 1)) +
          Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 (k + 1)) (fun j => chi (p : ZMod N) ^ j)) /
              (((k + 1 : Nat) : Complex) * (P : Complex))) Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    ((Filter.eventually_ge_atTop (3 : Nat)).mono
      (fun P hP => movingCharacterCorrection_normalized_remainder_le chi P k hP))
    (movingCharacterCorrection_remainder_majorant_tendsto k)

end

end RobinBV.NumberField
