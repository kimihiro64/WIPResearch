import RobinBV.Mathlib.NumberTheory.DirichletCharacter.PrimePowerSquareRemainder
import RobinBV.NumberField.Proof.CharacterRootPrimeERH

/-!
# Complete third-root remainder after square-layer extraction

The first-root character Chebyshev tail contains its prime root layer
and its doubled-index prime layer exactly. The entire remaining
prime-power contribution has a third-root bound after integration.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex Filter MeasureTheory Set

noncomputable section

private theorem rootSquare_log_weight_identity
    (a : Real) {t : Real} (ht : 1 < t) :
    (t ^ a * Real.log t) * Robin1984.robinRealWeight 1 t =
      t ^ (a - 2) * (1 + 1 / Real.log t) := by
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  have hLog := (Real.log_pos ht).ne'
  have hPower : t ^ a * t ^ (-2 : Real) = t ^ (a - 2) := by
    rw [<- Real.rpow_add htPos]
    congr 1
  unfold Robin1984.robinRealWeight
  norm_num only [Nat.cast_one, one_mul]
  calc
    _ = (t ^ a * t ^ (-2 : Real)) * ((Real.log t + 1) / Real.log t) := by field_simp [hLog]
    _ = _ := by rw [hPower]; field_simp [hLog]

/-- Complete integral bound after extracting the first and doubled
root-prime layers. No character cancellation or ERH is assumed. -/
theorem norm_rootChebyshevTail_sub_prime_sub_square_le
    {N : Nat} (chi : DirichletCharacter Complex N) {k : Nat} (hk : 2 <= k)
    {x : Real} (hx : 1 < x) :
    norm (rootCharacterChebyshevTail chi k x -
      rootPrimeCharacterTail chi (Inv.inv (k : Real)) x -
        rootPrimeCharacterTail (chi ^ 2) (Inv.inv ((2 * k : Nat) : Real)) x) <=
      (Inv.inv (k : Real) * (1 + 1 / Real.log x)) /
        (1 - Inv.inv ((3 * k : Nat) : Real)) * x ^ (Inv.inv ((3 * k : Nat) : Real) - 1) := by
  let r : Real := Inv.inv (k : Real)
  let b : Real := Inv.inv ((2 * k : Nat) : Real)
  let a : Real := Inv.inv ((3 * k : Nat) : Real)
  let C : Real := r * (1 + 1 / Real.log x)
  let F : Real -> Complex := fun t =>
    (characterChebyshevSum (Nat.floor (t ^ r)) chi - chi.primeChebyshevSum (Nat.floor (t ^ r)) -
      (chi ^ 2).primeChebyshevSum (Nat.floor (t ^ b))) * (Robin1984.robinRealWeight 1 t : Complex)
  have hkPos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hrPos : 0 < r := inv_pos.mpr hkPos
  have hr : r < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le (n := 1) (k := k) (by norm_num) hk
  have hb : b < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le (n := 1) (k := 2 * k)
      (by norm_num) (by omega)
  have ha : a < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le (n := 1) (k := 3 * k)
      (by norm_num) (by omega)
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLogPos := Real.log_pos hx
  have hStep (t : Real) (ht : 1 < t) :
      norm (characterChebyshevSum (Nat.floor (t ^ r)) chi - chi.primeChebyshevSum (Nat.floor (t ^ r)) -
        (chi ^ 2).primeChebyshevSum (Nat.floor (t ^ b))) <= r * (t ^ a * Real.log t) := by
    have htPos : 0 < t := lt_trans Real.zero_lt_one ht
    have hRoot : 1 <= t ^ r := (Real.one_lt_rpow ht hrPos).le
    have hSquare : (t ^ r) ^ (Inv.inv (2 : Real)) = t ^ b := by
      rw [<- Real.rpow_mul htPos.le]
      congr 1
      dsimp only [r, b]
      push_cast
      field_simp [hkPos.ne']
    have hCube : (t ^ r) ^ (Inv.inv (3 : Real)) = t ^ a := by
      rw [<- Real.rpow_mul htPos.le]
      congr 1
      dsimp only [r, a]
      push_cast
      field_simp [hkPos.ne']
    have hRaw := chi.norm_sum_vonMangoldt_sub_prime_sub_square_le hRoot
    change norm (characterChebyshevSum (Nat.floor (t ^ r)) chi - chi.primeChebyshevSum (Nat.floor (t ^ r)) -
      (chi ^ 2).primeChebyshevSum (Nat.floor ((t ^ r) ^ (Inv.inv (2 : Real))))) <=
        (t ^ r) ^ (Inv.inv (3 : Real)) * Real.log (t ^ r) at hRaw
    rw [hSquare, hCube, Real.log_rpow htPos] at hRaw
    exact hRaw.trans_eq (by ring)
  have hStepMeas : Measurable (fun t : Real =>
      characterChebyshevSum (Nat.floor (t ^ r)) chi - chi.primeChebyshevSum (Nat.floor (t ^ r)) -
        (chi ^ 2).primeChebyshevSum (Nat.floor (t ^ b))) := by
    exact ((measurable_of_countable (fun n : Nat => characterChebyshevSum n chi - chi.primeChebyshevSum n)).comp
      (Nat.measurable_floor.comp (by fun_prop))).sub
        ((measurable_of_countable (fun n : Nat => (chi ^ 2).primeChebyshevSum n)).comp
          (Nat.measurable_floor.comp (by fun_prop)))
  have hWeightMeas : Measurable (fun t : Real => (Robin1984.robinRealWeight 1 t : Complex)) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  have hExponent : a - 2 < -1 := by linarith
  have hMajor : IntegrableOn (fun t : Real => C * t ^ (a - 2)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt hExponent hxPos).const_mul C
  have hBound : Filter.Eventually (fun t : Real => norm (F t) <= C * t ^ (a - 2))
      (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t := hx.trans ht
    have htPos : 0 < t := lt_trans Real.zero_lt_one htOne
    have hWeight := Robin1984.robinRealWeight_nonneg (n := 1) htOne
    have hInv : 1 / Real.log t <= 1 / Real.log x :=
      one_div_le_one_div_of_le hLogPos (Real.log_le_log hxPos ht.le)
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeight]
    calc
      _ <= (r * (t ^ a * Real.log t)) * Robin1984.robinRealWeight 1 t :=
        mul_le_mul_of_nonneg_right (hStep t htOne) hWeight
      _ = r * (t ^ (a - 2) * (1 + 1 / Real.log t)) := by
        rw [mul_assoc, rootSquare_log_weight_identity a htOne]
      _ <= r * (t ^ (a - 2) * (1 + 1 / Real.log x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl hInv) (Real.rpow_nonneg htPos.le _)) hrPos.le
      _ = _ := by dsimp only [C]; ring
  have hDifference : IntegrableOn F (Ioi x) :=
    hMajor.mono' (hStepMeas.mul hWeightMeas).aestronglyMeasurable hBound
  have hPrime := integrableOn_rootPrimeCharacterTail chi hr hx
  have hSquare := integrableOn_rootPrimeCharacterTail (chi ^ 2) hb hx
  have hPsi : IntegrableOn (fun t : Real => characterChebyshevSum (Nat.floor (t ^ r)) chi *
      (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
    apply ((hDifference.add hPrime).add hSquare).congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only [F, Pi.add_apply]
    ring
  have hIdentity : rootCharacterChebyshevTail chi k x - rootPrimeCharacterTail chi r x -
      rootPrimeCharacterTail (chi ^ 2) b x = integral (volume.restrict (Ioi x)) F := by
    unfold rootCharacterChebyshevTail rootPrimeCharacterTail
    rw [<- integral_sub hPsi hPrime]
    have hSecond := integral_sub (hPsi.sub hPrime) hSquare
    simp only [Pi.sub_apply] at hSecond
    rw [<- hSecond]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  rw [hIdentity]
  have hNorm := norm_integral_le_of_norm_le hMajor hBound
  have hIntegral : integral (volume.restrict (Ioi x)) (fun t : Real => C * t ^ (a - 2)) =
      C / (1 - a) * x ^ (a - 1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hExponent hxPos]
    rw [show a - 2 + 1 = a - 1 by ring]
    field_simp [show Not (a - 1 = 0) by linarith, show Not (1 - a = 0) by linarith]
    ring
  exact hNorm.trans_eq hIntegral

/-- Above the third-root exponent, the entire error after the first two
root-prime layers vanishes unconditionally for every complex character. -/
theorem rootChebyshevTail_sub_prime_sub_square_scaled_tendsto
    {N : Nat} (chi : DirichletCharacter Complex N) (k : Nat) (hk : 2 <= k)
    {s : Real} (hs : Inv.inv ((3 * k : Nat) : Real) < s) :
    Tendsto (fun x : Real => ((x ^ (1 - s) * Real.log x : Real) : Complex) *
      (rootCharacterChebyshevTail chi k x - rootPrimeCharacterTail chi (Inv.inv (k : Real)) x -
        rootPrimeCharacterTail (chi ^ 2) (Inv.inv ((2 * k : Nat) : Real)) x))
      atTop (nhds (0 : Complex)) := by
  let a : Real := Inv.inv ((3 * k : Nat) : Real)
  let r : Real := Inv.inv (k : Real)
  have hLogPower : Tendsto (fun x : Real => Real.log x / x ^ (s - a)) atTop (nhds (0 : Real)) :=
    (isLittleO_log_rpow_atTop (show 0 < s - a from sub_pos.mpr hs)).tendsto_div_nhds_zero
  have hSmall : Tendsto (fun x : Real => x ^ (a - s) * Real.log x) atTop (nhds (0 : Real)) := by
    apply hLogPower.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    rw [show a - s = -(s - a) by ring, Real.rpow_neg hx.le]
    ring
  have hInvLog : Tendsto (fun x : Real => 1 / Real.log x) atTop (nhds (0 : Real)) :=
    Real.tendsto_log_atTop.const_div_atTop 1
  have hCoefficient : Tendsto (fun x : Real => r * (1 + 1 / Real.log x) / (1 - a))
      atTop (nhds (r / (1 - a))) := by
    simpa only [add_zero, mul_one] using ((hInvLog.const_add 1).const_mul r).div_const (1 - a)
  have hUpper : Tendsto (fun x : Real => (r * (1 + 1 / Real.log x) / (1 - a)) *
      (x ^ (a - s) * Real.log x)) atTop (nhds (0 : Real)) := by
    simpa only [mul_zero] using hCoefficient.mul hSmall
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_gt_atTop (1 : Real)] with x hx
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hScale : 0 <= x ^ (1 - s) * Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_pos hx).le
  have hPowers : x ^ (1 - s) * x ^ (a - 1) = x ^ (a - s) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale]
  apply (mul_le_mul_of_nonneg_left (norm_rootChebyshevTail_sub_prime_sub_square_le chi hk hx) hScale).trans_eq
  change (x ^ (1 - s) * Real.log x) * ((r * (1 + 1 / Real.log x) / (1 - a)) * x ^ (a - 1)) = _
  calc
    _ = (r * (1 + 1 / Real.log x) / (1 - a)) *
        (x ^ (1 - s) * x ^ (a - 1)) * Real.log x := by ring
    _ = _ := by rw [hPowers]; ring

end

end RobinBV.NumberField
