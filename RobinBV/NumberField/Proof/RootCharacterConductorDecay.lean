import RobinBV.NumberField.Proof.CharacterRootPrimeERH
import RobinBV.NumberField.Proof.ImprimitiveEndpointAsymptotic

/-!
# Full conductor corrections for root Chebyshev integrals

Every excluded prime power is retained in the actual BV conductor-step
bound. Its root-scaled integral has an explicit inverse-cutoff bound
and vanishes above every positive root normalization exponent.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex Filter MeasureTheory Set

noncomputable section

/-- Absolute integrability of every complete character root Chebyshev
tail, including principal characters and arbitrary ambient moduli. -/
theorem integrableOn_rootCharacterChebyshevTail
    {N : Nat} (chi : DirichletCharacter Complex N) {k : Nat} (hk : 2 <= k)
    {x : Real} (hx : 1 < x) :
    IntegrableOn (fun t : Real => characterChebyshevSum (Nat.floor (t ^ (Inv.inv (k : Real)))) chi *
      (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
  have hBase := Robin1984.integrableOn_psi_root_mul_robinRealWeight (by norm_num : 1 <= (1 : Nat)) hk hx
  have hStepMeas : Measurable (fun t : Real => characterChebyshevSum (Nat.floor (t ^ (Inv.inv (k : Real)))) chi) :=
    (measurable_of_countable (fun n : Nat => characterChebyshevSum n chi)).comp
      (Nat.measurable_floor.comp (by fun_prop))
  have hWeightMeas : Measurable (fun t : Real => (Robin1984.robinRealWeight 1 t : Complex)) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  apply hBase.mono' (hStepMeas.mul hWeightMeas).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hWeight := Robin1984.robinRealWeight_nonneg (n := 1) (hx.trans ht)
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeight]
  apply mul_le_mul_of_nonneg_right _ hWeight
  exact (norm_characterChebyshevSum_le_psi chi _).trans_eq (Chebyshev.psi_eq_psi_coe_floor _).symm

/-- Explicit full root conductor correction. It contains all excluded
prime powers and requires neither ERH nor nonprincipality. -/
theorem norm_rootCharacterChebyshevTail_sub_primitive_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) {k : Nat} (hk : 2 <= k)
    {x : Real} (hx : 3 <= x) :
    norm (rootCharacterChebyshevTail chi k x - rootCharacterChebyshevTail chi.primitiveCharacter k x) <=
      (Real.log N / Real.log 2 * Inv.inv (k : Real)) * (1 + 1 / Real.log x) / x := by
  let r : Real := Inv.inv (k : Real)
  let A : Real := Real.log N / Real.log 2 * r
  let F : Real -> Complex := fun t =>
    (characterChebyshevSum (Nat.floor (t ^ r)) chi -
      characterChebyshevSum (Nat.floor (t ^ r)) chi.primitiveCharacter) *
        (Robin1984.robinRealWeight 1 t : Complex)
  have hxOne : 1 < x := by linarith
  have hxPos : 0 < x := by linarith
  have hkPos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hrPos : 0 < r := inv_pos.mpr hkPos
  have hLogN : 0 <= Real.log N := Real.log_nonneg
    (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)))
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hA : 0 <= A := mul_nonneg (div_nonneg hLogN hLogTwo.le) hrPos.le
  have hLogData := log_mul_robinRealWeight_one_integral_data hx
  have hMajor : IntegrableOn (fun t : Real => A * (Real.log t * Robin1984.robinRealWeight 1 t)) (Ioi x) :=
    hLogData.1.const_mul A
  have hBound : Filter.Eventually (fun t : Real => norm (F t) <=
      A * (Real.log t * Robin1984.robinRealWeight 1 t)) (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t := hxOne.trans ht
    have htPos : 0 < t := lt_trans Real.zero_lt_one htOne
    have hRoot : 1 < t ^ r := Real.one_lt_rpow htOne hrPos
    have hFloor : 0 < Nat.floor (t ^ r) := by
      have hOne : 1 <= Nat.floor (t ^ r) := Nat.le_floor (by simpa only [Nat.cast_one] using hRoot.le)
      omega
    have hFloorPos : (0 : Real) < (Nat.floor (t ^ r) : Nat) := by exact_mod_cast hFloor
    have hLogFloor : Real.log (Nat.floor (t ^ r) : Nat) <= Real.log (t ^ r) :=
      Real.log_le_log hFloorPos (Nat.floor_le (Real.rpow_nonneg htPos.le _))
    have hRaw := norm_characterChebyshevSum_sub_primitive_le (NeZero.ne N) chi hFloor
    have hStep : norm (characterChebyshevSum (Nat.floor (t ^ r)) chi -
        characterChebyshevSum (Nat.floor (t ^ r)) chi.primitiveCharacter) <= A * Real.log t := by
      calc
        _ <= Real.log N * Real.log (t ^ r) / Real.log 2 := hRaw.trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLogFloor hLogN) hLogTwo.le)
        _ = _ := by rw [Real.log_rpow htPos]; dsimp only [A]; ring
    have hWeight := Robin1984.robinRealWeight_nonneg (n := 1) htOne
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeight]
    exact (mul_le_mul_of_nonneg_right hStep hWeight).trans_eq (by ring)
  have hLeft := integrableOn_rootCharacterChebyshevTail chi hk hxOne
  have hRight := integrableOn_rootCharacterChebyshevTail chi.primitiveCharacter hk hxOne
  have hIdentity : rootCharacterChebyshevTail chi k x - rootCharacterChebyshevTail chi.primitiveCharacter k x =
      integral (volume.restrict (Ioi x)) F := by
    unfold rootCharacterChebyshevTail
    rw [<- integral_sub hLeft hRight]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  rw [hIdentity]
  have hNorm := norm_integral_le_of_norm_le hMajor hBound
  rw [integral_const_mul, hLogData.2.1] at hNorm
  calc
    _ <= A * (1 / x + integral (volume.restrict (Ioi x)) (fun t : Real => 1 / (t ^ 2 * Real.log t))) := hNorm
    _ <= A * (1 / x + 1 / (x * Real.log x)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hLogData.2.2.2) hA
    _ = _ := by dsimp only [A, r]; field_simp [hxPos.ne', hkPos.ne', (Real.log_pos hxOne).ne']

/-- At every positive root normalization exponent, the complete
conductor correction vanishes without ERH, including principal characters. -/
theorem rootCharacterChebyshevTail_sub_primitive_scaled_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (k : Nat) (hk : 2 <= k)
    {s : Real} (hs : 0 < s) :
    Tendsto (fun x : Real => ((x ^ (1 - s) * Real.log x : Real) : Complex) *
      (rootCharacterChebyshevTail chi k x - rootCharacterChebyshevTail chi.primitiveCharacter k x))
      atTop (nhds (0 : Complex)) := by
  let A : Real := Real.log N / Real.log 2 * Inv.inv (k : Real)
  have hSmall : Tendsto (fun x : Real => x ^ (-s) * Real.log x) atTop (nhds (0 : Real)) := by
    have h := (isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with x hx
    rw [Real.rpow_neg hx.le]
    ring
  have hInv : Tendsto (fun x : Real => 1 / Real.log x) atTop (nhds (0 : Real)) :=
    Real.tendsto_log_atTop.const_div_atTop 1
  have hUpper : Tendsto (fun x : Real => (A * (1 + 1 / Real.log x)) * (x ^ (-s) * Real.log x))
      atTop (nhds (0 : Real)) := by
    simpa only [add_zero, mul_one, mul_zero] using (((hInv.const_add 1).const_mul A).mul hSmall)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_ge_atTop (3 : Real)] with x hx
  have hxPos : 0 < x := by linarith
  have hxOne : 1 < x := by linarith
  have hScale : 0 <= x ^ (1 - s) * Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_pos hxOne).le
  have hPower : x ^ (1 - s) / x = x ^ (-s) := by
    calc
      _ = x ^ (1 - s) / x ^ (1 : Real) := by rw [Real.rpow_one]
      _ = _ := by rw [<- Real.rpow_sub hxPos]; congr 1; ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale]
  apply (mul_le_mul_of_nonneg_left (norm_rootCharacterChebyshevTail_sub_primitive_le chi hk hx) hScale).trans_eq
  change (x ^ (1 - s) * Real.log x) * (A * (1 + 1 / Real.log x) / x) = _
  calc
    _ = (A * (1 + 1 / Real.log x)) * (x ^ (1 - s) / x) * Real.log x := by ring
    _ = _ := by rw [hPower]; ring

end

end RobinBV.NumberField
