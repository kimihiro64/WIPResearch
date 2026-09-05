import RobinBV.NumberField.Proof.CharacterWeightedHigherExponent
import RobinBV.NumberField.Proof.ImprimitiveDirichletERH
import RobinBV.NumberField.Proof.PrimeMomentTail

/-!
# ERH cancellation for complete character root-prime tails

Complex root substitution transfers the actual higher-weight arithmetic
estimate to a root scale. The full psi-minus-theta correction is handled
by the proved elementary square-root bound, not a new prime-error premise.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex Filter MeasureTheory Set

noncomputable section

/-- Exact root substitution for the complete complex Robin-weighted
integral. This is the complex extension of the committed Robin identity. -/
theorem integral_complex_root_mul_robinRealWeight
    (g : Real -> Complex) (n k : Nat) (hk : 0 < k) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real =>
      g (t ^ (Inv.inv (k : Real))) * (Robin1984.robinRealWeight n t : Complex)) =
      (Inv.inv (k : Real) : Complex) *
        integral (volume.restrict (Ioi (x ^ (Inv.inv (k : Real)))))
          (fun u : Real => g u * (Robin1984.robinRealWeight (k * n) u : Complex)) := by
  have hkPos : (0 : Real) < k := by exact_mod_cast hk
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hRoot : 1 < x ^ (Inv.inv (k : Real)) := Real.one_lt_rpow hx (inv_pos.mpr hkPos)
  have hChange := integral_comp_rpow_Ioi_of_pos'
    (g := fun t : Real => g (t ^ (Inv.inv (k : Real))) * (Robin1984.robinRealWeight n t : Complex))
    hkPos hxPos.le
  rw [<- hChange, <- integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have huOne : 1 < u := hRoot.trans hu
  have huPos : 0 < u := lt_trans Real.zero_lt_one huOne
  have hRootBack : (u ^ (k : Real)) ^ (Inv.inv (k : Real)) = u := by
    rw [<- Real.rpow_mul huPos.le,
      show (k : Real) * Inv.inv (k : Real) = 1 by field_simp, Real.rpow_one]
  dsimp only
  rw [Complex.real_smul, hRootBack]
  calc
    _ = g u * (((k : Real) * u ^ ((k : Real) - 1) *
        Robin1984.robinRealWeight n (u ^ (k : Real)) : Real) : Complex) := by push_cast; ring
    _ = _ := by rw [Robin1984.robinRealWeight_rpow_pullback n k hk huOne]; push_cast; ring

/-- The full character-weighted Chebyshev integral at a root cutoff. -/
def rootCharacterChebyshevTail
    {N : Nat} (chi : DirichletCharacter Complex N) (k : Nat) (x : Real) : Complex :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    characterChebyshevSum (Nat.floor (t ^ (Inv.inv (k : Real)))) chi *
      (Robin1984.robinRealWeight 1 t : Complex))

/-- Exact identification with the actual higher-weight character integral. -/
theorem rootCharacterChebyshevTail_eq_higherIntegral
    {N : Nat} (chi : DirichletCharacter Complex N) {k : Nat} (hk : 0 < k)
    {x : Real} (hx : 1 < x) :
    rootCharacterChebyshevTail chi k x = (Inv.inv (k : Real) : Complex) *
      dirichletCharacterWeightedIntegral chi k (x ^ (Inv.inv (k : Real))) := by
  simpa only [rootCharacterChebyshevTail, dirichletCharacterWeightedIntegral, Nat.mul_one] using
    integral_complex_root_mul_robinRealWeight (fun u : Real => characterChebyshevSum (Nat.floor u) chi)
      1 k hk hx

/-- Actual ERH cancellation transfers to every root Chebyshev integral
above its half-root exponent, with the exact change-of-scale coefficient. -/
theorem primitiveRootCharacterChebyshevTail_scaled_tendsto
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hChi : Not (chi = 1)) (hPrimitive : chi.IsPrimitive) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) {s : Real} (hs : 1 / 2 < (k : Real) * s) :
    Tendsto (fun x : Real => ((x ^ (1 - s) * Real.log x : Real) : Complex) *
      rootCharacterChebyshevTail chi k x) atTop (nhds (0 : Complex)) := by
  have hkPos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hRoot : Tendsto (fun x : Real => x ^ (Inv.inv (k : Real))) atTop atTop :=
    tendsto_rpow_atTop (inv_pos.mpr hkPos)
  have h := (primitiveCharacterWeightedIntegral_higher_scaled_tendsto hChi hPrimitive hERH hk hs).comp hRoot
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : Real)] with x hx
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hPower : (x ^ (Inv.inv (k : Real))) ^ ((k : Real) - (k : Real) * s) = x ^ (1 - s) := by
    rw [<- Real.rpow_mul hxPos.le]
    congr 1
    field_simp [hkPos.ne']
  dsimp only [Function.comp_def]
  rw [rootCharacterChebyshevTail_eq_higherIntegral chi (by omega) hx, hPower, Real.log_rpow hxPos]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- The complete root psi-minus-theta correction has an elementary
half-root bound, uniformly in the character and modulus. -/
theorem exists_rootCharacterChebyshevTail_sub_prime_bound
    (k : Nat) (hk : 2 <= k) :
    exists C : Real, And (0 <= C) (forall (N : Nat) (chi : DirichletCharacter Complex N)
      (x : Real), 1 < x ->
      norm (rootCharacterChebyshevTail chi k x -
        rootPrimeCharacterTail chi (Inv.inv (k : Real)) x) <=
        C * x ^ (Inv.inv (k : Real) / 2 - 1) /
          ((1 - Inv.inv (k : Real) / 2) * Real.log x)) := by
  choose C0 hC0 using Chebyshev.psi_sub_theta_le_mul_sqrt
  let C : Real := abs C0
  let r : Real := Inv.inv (k : Real)
  let a : Real := r / 2
  have hC : 0 <= C := abs_nonneg _
  have hr0 : 0 <= r := by dsimp only [r]; positivity
  have hr1 : r < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le (n := 1) (k := k)
      (by norm_num) hk
  have ha0 : 0 <= a := div_nonneg hr0 (by norm_num)
  have ha1 : a < 1 := by dsimp only [a]; linarith
  refine Exists.intro C (And.intro hC ?_)
  intro N chi x hx
  let F : Real -> Complex := fun t =>
    (characterChebyshevSum (Nat.floor (t ^ r)) chi - chi.primeChebyshevSum (Nat.floor (t ^ r))) *
      (Robin1984.robinRealWeight 1 t : Complex)
  have hStep (t : Real) (ht : 1 < t) :
      norm (characterChebyshevSum (Nat.floor (t ^ r)) chi - chi.primeChebyshevSum (Nat.floor (t ^ r))) <=
        C * t ^ a := by
    have htPos : 0 < t := lt_trans Real.zero_lt_one ht
    have hRootNonneg : 0 <= t ^ r := Real.rpow_nonneg htPos.le _
    have hRaw := chi.norm_sum_vonMangoldt_sub_primeChebyshevSum_le (Nat.floor (t ^ r))
    change norm (characterChebyshevSum (Nat.floor (t ^ r)) chi -
      chi.primeChebyshevSum (Nat.floor (t ^ r))) <=
        Chebyshev.psi (Nat.floor (t ^ r) : Real) - Chebyshev.theta (Nat.floor (t ^ r) : Real) at hRaw
    have hSqrt : Real.sqrt (t ^ r) = t ^ a := by
      rw [Real.sqrt_eq_rpow, <- Real.rpow_mul htPos.le]
      congr 1
      dsimp only [a]
      ring
    calc
      _ <= C0 * Real.sqrt (Nat.floor (t ^ r) : Real) := hRaw.trans (hC0 _)
      _ <= C * Real.sqrt (Nat.floor (t ^ r) : Real) :=
        mul_le_mul_of_nonneg_right (le_abs_self C0) (Real.sqrt_nonneg _)
      _ <= C * Real.sqrt (t ^ r) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le hRootNonneg)) hC
      _ = _ := by rw [hSqrt]
  have hStepMeas : Measurable (fun t : Real =>
      characterChebyshevSum (Nat.floor (t ^ r)) chi - chi.primeChebyshevSum (Nat.floor (t ^ r))) :=
    (measurable_of_countable (fun j : Nat => characterChebyshevSum j chi - chi.primeChebyshevSum j)).comp
      (Nat.measurable_floor.comp (by fun_prop))
  have hWeightMeas : Measurable (fun t : Real => (Robin1984.robinRealWeight 1 t : Complex)) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  have hMajor : IntegrableOn (fun t : Real => C * (t ^ a * Robin1984.robinRealWeight 1 t)) (Ioi x) :=
    (Robin1984.integrableOn_rpow_mul_robinRealWeight (n := 1) hx
      (by simpa only [Nat.cast_one] using ha1)).const_mul C
  have hBound : Filter.Eventually (fun t : Real => norm (F t) <=
      C * (t ^ a * Robin1984.robinRealWeight 1 t)) (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t := hx.trans ht
    have hWeight := Robin1984.robinRealWeight_nonneg (n := 1) htOne
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeight]
    exact (mul_le_mul_of_nonneg_right (hStep t htOne) hWeight).trans_eq (by ring)
  have hDifference : IntegrableOn F (Ioi x) :=
    hMajor.mono' (hStepMeas.mul hWeightMeas).aestronglyMeasurable hBound
  have hPrime := integrableOn_rootPrimeCharacterTail chi hr1 hx
  have hPsi : IntegrableOn (fun t : Real => characterChebyshevSum (Nat.floor (t ^ r)) chi *
      (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
    apply (hDifference.add hPrime).congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only [F, Pi.add_apply]
    ring
  have hIdentity : rootCharacterChebyshevTail chi k x - rootPrimeCharacterTail chi r x =
      integral (volume.restrict (Ioi x)) F := by
    unfold rootCharacterChebyshevTail rootPrimeCharacterTail
    rw [<- integral_sub hPsi hPrime]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  rw [hIdentity]
  have hNorm := norm_integral_le_of_norm_le hMajor hBound
  rw [integral_const_mul] at hNorm
  have hModel : integral (volume.restrict (Ioi x)) (fun t : Real => t ^ a * Robin1984.robinRealWeight 1 t) <=
      x ^ (a - 1) / ((1 - a) * Real.log x) := by
    have h := (robinPowerTail_secondary_bounds ha0 ha1 hx).1
    linarith
  exact hNorm.trans ((mul_le_mul_of_nonneg_left hModel hC).trans_eq (by ring))

/-- The complete root psi-minus-theta correction vanishes above its
half-root exponent, unconditionally and for every complex character. -/
theorem rootCharacterChebyshevTail_sub_prime_scaled_tendsto
    {N : Nat} (chi : DirichletCharacter Complex N) (k : Nat) (hk : 2 <= k)
    {s : Real} (hs : 1 / 2 < (k : Real) * s) :
    Tendsto (fun x : Real => ((x ^ (1 - s) * Real.log x : Real) : Complex) *
      (rootCharacterChebyshevTail chi k x - rootPrimeCharacterTail chi (Inv.inv (k : Real)) x))
      atTop (nhds (0 : Complex)) := by
  choose C hC hBound using exists_rootCharacterChebyshevTail_sub_prime_bound k hk
  let a : Real := Inv.inv (k : Real) / 2
  have hkPos : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hProduct : (k : Real) * a = 1 / 2 := by dsimp only [a]; field_simp [hkPos.ne']
  have hAs : a < s := by nlinarith
  have hPower : Tendsto (fun x : Real => x ^ (a - s)) atTop (nhds (0 : Real)) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hAs)
  have hUpper : Tendsto (fun x : Real => (C / (1 - a)) * x ^ (a - s)) atTop (nhds (0 : Real)) := by
    simpa only [mul_zero] using hPower.const_mul (C / (1 - a))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_gt_atTop (1 : Real)] with x hx
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLog := (Real.log_pos hx).ne'
  have hScale : 0 <= x ^ (1 - s) * Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_pos hx).le
  have hPowers : x ^ (1 - s) * x ^ (a - 1) = x ^ (a - s) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hScale]
  calc
    _ <= (x ^ (1 - s) * Real.log x) *
        (C * x ^ (a - 1) / ((1 - a) * Real.log x)) :=
      mul_le_mul_of_nonneg_left (hBound N chi x hx) hScale
    _ = (C / (1 - a)) * (x ^ (1 - s) * x ^ (a - 1)) := by field_simp [hLog]
    _ = _ := by rw [hPowers]

/-- ERH gives full root-prime cancellation for every primitive
nonprincipal complex character, at every scale above 1/(2k). -/
theorem primitiveRootPrimeCharacterTail_scaled_tendsto
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hChi : Not (chi = 1)) (hPrimitive : chi.IsPrimitive) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) {s : Real} (hs : 1 / 2 < (k : Real) * s) :
    Tendsto (fun x : Real => ((x ^ (1 - s) * Real.log x : Real) : Complex) *
      rootPrimeCharacterTail chi (Inv.inv (k : Real)) x) atTop (nhds (0 : Complex)) := by
  have h := (primitiveRootCharacterChebyshevTail_scaled_tendsto hChi hPrimitive hERH hk hs).sub
    (rootCharacterChebyshevTail_sub_prime_scaled_tendsto chi k hk hs)
  convert h using 1
  next =>
    funext x
    ring
  next =>
    simp

/-- Complete root-prime ERH cancellation for every nonprincipal complex
character at every positive ambient modulus, with no primitivity or parity
restriction and no unproved finite-conductor correction premise. -/
theorem rootPrimeCharacterTail_scaled_tendsto_of_ERH
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hChi : Not (chi = 1)) (hERH : DirichletERH chi)
    {k : Nat} (hk : 2 <= k) {s : Real} (hs : 1 / 2 < (k : Real) * s) :
    Tendsto (fun x : Real => ((x ^ (1 - s) * Real.log x : Real) : Complex) *
      rootPrimeCharacterTail chi (Inv.inv (k : Real)) x) atTop (nhds (0 : Complex)) := by
  let : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  have hPrimitiveChi := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hChi
  have hPrimitiveERH := (dirichletERH_iff_primitive chi hChi).1 hERH
  have hr : Inv.inv (k : Real) < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le (n := 1) (k := k)
      (by norm_num) hk
  have hsPos : 0 < s := by
    by_contra hNot
    have hsLe : s <= 0 := le_of_not_gt hNot
    have hProduct := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k : (0 : Real) <= k) hsLe
    linarith
  have h := (rootPrimeCharacterTail_sub_primitive_scaled_tendsto chi hr hsPos).add
    (primitiveRootPrimeCharacterTail_scaled_tendsto hPrimitiveChi chi.primitiveCharacter_isPrimitive
      hPrimitiveERH hk hs)
  simp only [zero_add] at h
  convert h using 1
  funext x
  ring

end

end RobinBV.NumberField
