import RobinBV.NumberField.Proof.MovingCharacterLevelBridge
import RobinBV.NumberField.Proof.MovingPrimorialRealCutoff

/-!
# Complete moving character corrections at arbitrary real cutoffs

Every sufficiently large real x is used, with prime cutoff floor(sqrt(x)).
The full principal residual dominates the character remainder, and the
proved SW prime moments determine the shift of the actual centered integral.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter
open scoped Classical

noncomputable section

/-- The normalized complete character remainder is bounded independently
of the character and modulus at every real endpoint x>=3. -/
theorem movingCharacter_real_remainder_le
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Real} (hx : 3 <= x) :
    norm (((Real.sqrt x * Real.log x : Real) : Complex) *
      movingCharacterCorrection chi (Nat.floor (Real.sqrt x)) x +
        Finset.sum (Nat.primesLE (Nat.floor (Real.sqrt x))) (fun p => (Real.log p : Complex) *
          Finset.sum (Finset.Icc 1 2) (fun j => chi (p : ZMod N) ^ j)) / (Real.sqrt x : Complex)) <=
      -((Real.sqrt x * Real.log x) *
        (movingPrimorialCorrection (Nat.floor (Real.sqrt x)) x).re) -
          2 * Chebyshev.theta (Real.sqrt x) / Real.sqrt x := by
  let P := Nat.floor (Real.sqrt x)
  let F := Real.sqrt x * Real.log x
  let B : Complex := Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
    Finset.sum (Finset.Icc 1 2) (fun j => chi (p : ZMod N) ^ j))
  have hxPos : 0 < x := by linarith
  have hLogPos : 0 < Real.log x := Real.log_pos (by linarith)
  have hSqrtPos := Real.sqrt_pos_of_pos hxPos
  have hSq := Real.sq_sqrt hxPos.le
  have hFloor : (P : Real) <= Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hPNonneg : (0 : Real) <= (P : Real) := Nat.cast_nonneg _
  have hPowers : ((P ^ 2 : Nat) : Real) <= x := by push_cast; nlinarith
  have hF : 0 <= F := mul_nonneg hSqrtPos.le hLogPos.le
  have hBase := movingCharacterCorrection_remainder_le chi P 2 hx hPowers
  have hScaled := mul_le_mul_of_nonneg_left hBase hF
  have hCancel : F / (x * Real.log x) = 1 / Real.sqrt x := by
    dsimp only [F]
    field_simp [hxPos.ne', hLogPos.ne', hSqrtPos.ne']
    nlinarith
  have hCancelC : (F : Complex) / ((x : Complex) * (Real.log x : Complex)) =
      1 / (Real.sqrt x : Complex) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one] using
      congrArg Complex.ofReal hCancel
  have hPrefix : (F : Complex) * (B / ((x : Complex) * (Real.log x : Complex))) =
      B / (Real.sqrt x : Complex) := by
    calc
      _ = B * ((F : Complex) / ((x : Complex) * (Real.log x : Complex))) := by ring
      _ = _ := by rw [hCancelC]; ring
  have hTheta : F * (2 * Chebyshev.theta (P : Real) / (x * Real.log x)) =
      2 * Chebyshev.theta (Real.sqrt x) / Real.sqrt x := by
    calc
      _ = (2 * Chebyshev.theta (P : Real)) * (F / (x * Real.log x)) := by ring
      _ = _ := by
        rw [hCancel]
        dsimp only [P]
        rw [<- Chebyshev.theta_eq_theta_coe_floor]
        ring
  have hNorm : norm ((F : Complex) * (movingCharacterCorrection chi P x +
      B / ((x : Complex) * (Real.log x : Complex)))) =
        F * norm (movingCharacterCorrection chi P x +
          B / ((x : Complex) * (Real.log x : Complex))) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hF]
  norm_num only [Nat.cast_ofNat] at hScaled
  rw [<- hNorm, mul_add, hPrefix, mul_sub, hTheta, mul_neg] at hScaled
  exact hScaled

/-- The complete transfer error tends to zero along all real endpoints,
not just along an integer-power subsequence. -/
theorem movingCharacter_real_moment_transfer_tendsto
    {N : Nat} (chi : DirichletCharacter Complex N) :
    Tendsto (fun x : Real => ((Real.sqrt x * Real.log x : Real) : Complex) *
      movingCharacterCorrection chi (Nat.floor (Real.sqrt x)) x +
        Finset.sum (Nat.primesLE (Nat.floor (Real.sqrt x))) (fun p => (Real.log p : Complex) *
          Finset.sum (Finset.Icc 1 2) (fun j => chi (p : ZMod N) ^ j)) / (Real.sqrt x : Complex))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    ((Filter.eventually_ge_atTop (3 : Real)).mono (fun x hx => movingCharacter_real_remainder_le chi hx))
    movingPrimorial_real_prefix_remainder_tendsto

private theorem characterPrimeSquareMoment_sqrt_div_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    Tendsto (fun x : Real =>
      Finset.sum (Nat.primesLE (Nat.floor (Real.sqrt x))) (fun p => (Real.log p : Complex) *
        Finset.sum (Finset.Icc 1 2) (fun j => chi (p : ZMod N) ^ j)) / (Real.sqrt x : Complex))
      atTop (nhds (Finset.sum (Finset.Icc 1 2)
        (fun j => if chi ^ j = 1 then (1 : Complex) else 0))) := by
  have hCutoff : Tendsto (fun x : Real => Nat.floor (Real.sqrt x)) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_sqrt_atTop
  have hMoment := (characterPrimePowerMoment_div_tendsto chi 2).comp hCutoff
  have hRatioReal : Tendsto (fun x : Real => (Nat.floor (Real.sqrt x) : Real) / Real.sqrt x)
      atTop (nhds (1 : Real)) := tendsto_nat_floor_div_atTop.comp Real.tendsto_sqrt_atTop
  have hRatio : Tendsto (fun x : Real => (Nat.floor (Real.sqrt x) : Complex) /
      (Real.sqrt x : Complex)) atTop (nhds (1 : Complex)) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_one] using hRatioReal.ofReal
  have hRaw := hMoment.mul hRatio
  rw [mul_one] at hRaw
  apply hRaw.congr'
  filter_upwards [hCutoff.eventually (Filter.eventually_gt_atTop (0 : Nat))] with x hx
  have hNe : Not ((Nat.floor (Real.sqrt x) : Complex) = 0) := by exact_mod_cast hx.ne'
  dsimp only [Function.comp_apply]
  field_simp [hNe]

/-- For every fixed character, the complete all-real moving correction
has the critical shift determined by its first two positive powers. -/
theorem movingCharacter_real_critical_shift
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    Tendsto (fun x : Real => ((Real.sqrt x * Real.log x : Real) : Complex) *
      movingCharacterCorrection chi (Nat.floor (Real.sqrt x)) x) atTop
      (nhds (-(if chi = 1 then (1 : Complex) else 0) -
        (if chi ^ 2 = 1 then (1 : Complex) else 0))) := by
  have h := (movingCharacter_real_moment_transfer_tendsto chi).sub
    (characterPrimeSquareMoment_sqrt_div_tendsto chi)
  have hSet : Finset.Icc 1 2 = ({1, 2} : Finset Nat) := by decide
  rw [hSet, Finset.sum_insert (by decide : Not (Membership.mem ({2} : Finset Nat) 1)),
    Finset.sum_singleton, pow_one] at h
  convert h using 1
  next =>
    funext x
    ring
  next =>
    ring

/-- The full-real critical shift belongs to the actual induced-character
centered integral difference at the moving lcm level. -/
theorem centeredCharacter_real_moving_critical_shift
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    Tendsto (fun x : Real => ((Real.sqrt x * Real.log x : Real) : Complex) *
      (centeredCharacterWeightedIntegral
        (chi.changeLevel (Nat.dvd_lcm_left N (primorial (Nat.floor (Real.sqrt x))))) x -
          centeredCharacterWeightedIntegral chi x)) atTop
      (nhds (-(if chi = 1 then (1 : Complex) else 0) -
        (if chi ^ 2 = 1 then (1 : Complex) else 0))) := by
  apply (movingCharacter_real_critical_shift chi).congr'
  filter_upwards [Filter.eventually_ge_atTop (3 : Real)] with x hx
  rw [centeredCharacterWeightedIntegral_changeLevel_primorial_sub chi _ hx]

end

end RobinBV.NumberField
