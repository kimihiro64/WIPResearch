import RobinBV.NumberField.Proof.PrincipalCharacterEndpoint
import RobinBV.NumberField.Proof.RiemannCriticalCriterion

/-!
# Signed secondary terms for centered principal characters

Each complete logarithmic-floor gap is nonnegative and smaller than the
corresponding prime logarithm. Keeping those signs gives an exact secondary
residual identity and asymmetric error bounds for the actual principal tail.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

/-- The full logarithmic-floor remainder is integrable with its exact sign
and an explicit bound retaining every prime divisor of the ambient level. -/
theorem principalLogFloorRemainder_integral_data
    (N : Nat) {x : Real} (hx : 3 <= x) :
    let Q : Real -> Real := fun t => Finset.sum N.primeFactors (fun p =>
      Real.log t - Real.log p * (Nat.log p (Nat.floor t) : Real))
    And (IntegrableOn (fun t : Real => Q t * Robin1984.robinRealWeight 1 t) (Ioi x))
      (And
        (0 <= integral (volume.restrict (Ioi x)) (fun t : Real => Q t * Robin1984.robinRealWeight 1 t))
        (integral (volume.restrict (Ioi x)) (fun t : Real => Q t * Robin1984.robinRealWeight 1 t) <=
          Finset.sum N.primeFactors (fun p => Real.log p) / (x * Real.log x))) := by
  let Q : Real -> Real := fun t => Finset.sum N.primeFactors (fun p =>
    Real.log t - Real.log p * (Nat.log p (Nat.floor t) : Real))
  let C : Real := Finset.sum N.primeFactors (fun p => Real.log p)
  have hxOne : 1 < x := by linarith
  have hPoint : forall t : Real, 1 <= t -> And (0 <= Q t) (Q t <= C) := by
    intro t ht
    constructor
    next =>
      apply Finset.sum_nonneg
      intro p hp
      have hGap := Nat.log_sub_log_floor_mul_log_bounds
        (Nat.prime_of_mem_primeFactors hp).one_lt ht
      simpa only [mul_comm] using hGap.1
    next =>
      apply Finset.sum_le_sum
      intro p hp
      have hGap := Nat.log_sub_log_floor_mul_log_bounds
        (Nat.prime_of_mem_primeFactors hp).one_lt ht
      simpa only [mul_comm] using hGap.2.le
  have hQMeas : Measurable Q := by
    apply Finset.measurable_sum
    intro p hp
    have hFloor : Measurable (fun t : Real => (Nat.log p (Nat.floor t) : Real)) :=
      (measurable_of_countable (fun k : Nat => (Nat.log p k : Real))).comp Nat.measurable_floor
    exact Real.measurable_log.sub (measurable_const.mul hFloor)
  have hWeightMeas : Measurable (Robin1984.robinRealWeight 1) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  have hWeight := Robin1984.integrableOn_robinRealWeight
    (by norm_num : 1 <= (1 : Nat)) hxOne
  have hMajor := hWeight.const_mul C
  have hNonnegAE : Filter.Eventually (fun t : Real =>
      0 <= Q t * Robin1984.robinRealWeight 1 t) (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (hPoint t (hxOne.trans ht).le).1
      (Robin1984.robinRealWeight_nonneg (n := 1) (hxOne.trans ht))
  have hBoundAE : Filter.Eventually (fun t : Real =>
      Q t * Robin1984.robinRealWeight 1 t <= C * Robin1984.robinRealWeight 1 t)
        (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_le_mul_of_nonneg_right (hPoint t (hxOne.trans ht).le).2
      (Robin1984.robinRealWeight_nonneg (n := 1) (hxOne.trans ht))
  have hInt : IntegrableOn (fun t : Real => Q t * Robin1984.robinRealWeight 1 t) (Ioi x) := by
    apply hMajor.mono' (hQMeas.mul hWeightMeas).aestronglyMeasurable
    filter_upwards [hNonnegAE, hBoundAE] with t hNonneg hBound
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg hNonneg] using hBound
  have hNonneg := integral_nonneg_of_ae hNonnegAE
  have hBound := integral_mono_ae hInt hMajor hBoundAE
  have hMajorIntegral : integral (volume.restrict (Ioi x)) (fun t : Real =>
      C * Robin1984.robinRealWeight 1 t) = C / (x * Real.log x) := by
    rw [integral_const_mul, Robin1984.integral_robinRealWeight
      (by norm_num : 1 <= (1 : Nat)) hxOne]
    norm_num [Real.rpow_neg_one]
    ring
  rw [hMajorIntegral] at hBound
  exact And.intro hInt (And.intro hNonneg hBound)

/-- Exact complete secondary identity. The floor residual and the positive
logarithmic kernel residual are both retained, with their actual signs. -/
theorem principalCenteredWeightedIntegral_secondary_identity
    {N : Nat} [NeZero N] {x : Real} (hx : 3 <= x) :
    principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex) +
        (N.primeFactors.card : Complex) / (x : Complex) =
      ((integral (volume.restrict (Ioi x)) (fun t : Real =>
          Finset.sum N.primeFactors (fun p =>
            Real.log t - Real.log p * (Nat.log p (Nat.floor t) : Real)) *
              Robin1984.robinRealWeight 1 t) -
        (N.primeFactors.card : Real) * integral (volume.restrict (Ioi x))
          (fun t : Real => 1 / (t ^ 2 * Real.log t)) : Real) : Complex) := by
  let r : Nat := N.primeFactors.card
  let S : Real -> Real := fun t => Finset.sum N.primeFactors (fun p =>
    Real.log p * (Nat.log p (Nat.floor t) : Real))
  let Q : Real -> Real := fun t => Finset.sum N.primeFactors (fun p =>
    Real.log t - Real.log p * (Nat.log p (Nat.floor t) : Real))
  let B : Real := integral (volume.restrict (Ioi x)) (fun t : Real => S t * Robin1984.robinRealWeight 1 t)
  let U : Real := integral (volume.restrict (Ioi x)) (fun t : Real => Q t * Robin1984.robinRealWeight 1 t)
  let G : Real := integral (volume.restrict (Ioi x)) (fun t : Real => 1 / (t ^ 2 * Real.log t))
  have hQEq : forall t : Real, Q t = (r : Real) * Real.log t - S t := by
    intro t
    simp [Q, S, r, Finset.sum_sub_distrib]
  have hQData := principalLogFloorRemainder_integral_data N hx
  have hLogData := log_mul_robinRealWeight_one_integral_data hx
  have hQInt : IntegrableOn (fun t : Real => Q t * Robin1984.robinRealWeight 1 t) (Ioi x) := hQData.1
  have hLogInt := hLogData.1.const_mul (r : Real)
  have hSInt : IntegrableOn (fun t : Real => S t * Robin1984.robinRealWeight 1 t) (Ioi x) := by
    apply (hLogInt.sub hQInt).congr
    filter_upwards [] with t
    dsimp only [Pi.sub_apply]
    rw [hQEq]
    ring
  have hQIntegral : U = (r : Real) * (1 / x + G) - B := by
    calc
      _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
          (r : Real) * (Real.log t * Robin1984.robinRealWeight 1 t) -
            S t * Robin1984.robinRealWeight 1 t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [hQEq]
        ring
      _ = _ := by
        rw [integral_sub hLogInt hSInt, integral_const_mul, hLogData.2.1]
  have hReal : -B + (r : Real) / x = U - (r : Real) * G := by
    rw [hQIntegral]
    ring
  rw [principalCenteredWeightedIntegral_sub_zeta_eq_logFloorIntegral hx]
  change -(B : Complex) + (r : Complex) / (x : Complex) = ((U - (r : Real) * G : Real) : Complex)
  have hCast := congrArg (fun y : Real => (y : Complex)) hReal
  push_cast at hCast
  push_cast
  exact hCast

/-- Sharper asymmetric error interval for the actual principal secondary
term. The lower coefficient is the number of excluded primes; the upper
coefficient is their complete logarithmic sum. -/
theorem principalCenteredWeightedIntegral_secondary_bounds
    {N : Nat} [NeZero N] {x : Real} (hx : 3 <= x) :
    And
      (-(N.primeFactors.card : Real) / (x * Real.log x) <=
        (principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex) +
          (N.primeFactors.card : Complex) / (x : Complex)).re)
      ((principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex) +
          (N.primeFactors.card : Complex) / (x : Complex)).re <=
        Finset.sum N.primeFactors (fun p => Real.log p) / (x * Real.log x)) := by
  rw [principalCenteredWeightedIntegral_secondary_identity hx, Complex.ofReal_re]
  have hQData := principalLogFloorRemainder_integral_data N hx
  have hLogData := log_mul_robinRealWeight_one_integral_data hx
  have hRNonneg : 0 <= (N.primeFactors.card : Real) := Nat.cast_nonneg _
  have hGNonneg := mul_nonneg hRNonneg hLogData.2.2.1
  have hGUpper := mul_le_mul_of_nonneg_left hLogData.2.2.2 hRNonneg
  constructor
  next =>
    calc
      _ = -((N.primeFactors.card : Real) * (1 / (x * Real.log x))) := by ring
      _ <= -(N.primeFactors.card : Real) * integral (volume.restrict (Ioi x))
          (fun t : Real => 1 / (t ^ 2 * Real.log t)) := by linarith
      _ <= _ := by linarith [hQData.2.1]
  next =>
    linarith [hQData.2.2]

/-- The full principal correction has a sharper absolute bound depending
only on the number of excluded primes, not their total logarithmic size.
This bound is explicit even when the ambient modulus varies. -/
theorem norm_principalCenteredWeightedIntegral_sub_zeta_le
    {N : Nat} [NeZero N] {x : Real} (hx : 3 <= x) :
    norm (principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex)) <=
      (N.primeFactors.card : Real) * (1 + 1 / Real.log x) / x := by
  let r : Nat := N.primeFactors.card
  let S : Real -> Real := fun t => Finset.sum N.primeFactors (fun p =>
    Real.log p * (Nat.log p (Nat.floor t) : Real))
  have hxOne : 1 < x := by linarith
  have hLogData := log_mul_robinRealWeight_one_integral_data hx
  have hMajor := hLogData.1.const_mul (r : Real)
  have hBoundAE : Filter.Eventually (fun t : Real =>
      norm (S t * Robin1984.robinRealWeight 1 t) <=
        (r : Real) * (Real.log t * Robin1984.robinRealWeight 1 t))
      (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t := hxOne.trans ht
    have hWeightNonneg := Robin1984.robinRealWeight_nonneg (n := 1) htOne
    have hSNonneg : 0 <= S t := by
      apply Finset.sum_nonneg
      intro p hp
      have hLogP : 0 <= Real.log p := Real.log_nonneg (by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
      exact mul_nonneg hLogP (Nat.cast_nonneg _)
    have hSLe : S t <= (r : Real) * Real.log t := by
      calc
        _ <= Finset.sum N.primeFactors (fun _ => Real.log t) := by
          apply Finset.sum_le_sum
          intro p hp
          have hGap := Nat.log_sub_log_floor_mul_log_bounds
            (Nat.prime_of_mem_primeFactors hp).one_lt htOne.le
          nlinarith [hGap.1]
        _ = _ := by simp [r]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hSNonneg hWeightNonneg)]
    calc
      _ <= ((r : Real) * Real.log t) * Robin1984.robinRealWeight 1 t :=
        mul_le_mul_of_nonneg_right hSLe hWeightNonneg
      _ = _ := by ring
  have hNorm := norm_integral_le_of_norm_le hMajor hBoundAE
  rw [integral_const_mul, hLogData.2.1] at hNorm
  rw [principalCenteredWeightedIntegral_sub_zeta_eq_logFloorIntegral hx,
    norm_neg, Complex.norm_real]
  calc
    _ <= (r : Real) * (1 / x + integral (volume.restrict (Ioi x))
        (fun t : Real => 1 / (t ^ 2 * Real.log t))) := hNorm
    _ <= (r : Real) * (1 / x + 1 / (x * Real.log x)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hLogData.2.2.2) (Nat.cast_nonneg r)
    _ = _ := by dsimp only [r]; ring

/-- At every fixed ambient level, the complete principal correction is
smaller than every positive multiple of the RH critical scale. -/
theorem eventually_principalCenteredWeightedIntegral_sub_zeta_le
    {N : Nat} [NeZero N] {epsilon : Real} (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      norm (principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex)) <=
        epsilon / (Real.sqrt x * Real.log x)) Filter.atTop := by
  let A : Real := (N.primeFactors.card : Real) * (1 + 1 / Real.log 3)
  have hLogThree : 0 < Real.log (3 : Real) := Real.log_pos (by norm_num)
  have hA : 0 <= A := by dsimp only [A]; positivity
  let eta : Real := epsilon / (A + 1)
  have hEta : 0 < eta := by dsimp only [eta]; positivity
  have hAEta : A * eta <= epsilon := by
    calc
      _ <= (A + 1) * eta := mul_le_mul_of_nonneg_right (by linarith) hEta.le
      _ = epsilon := by dsimp only [eta]; field_simp
  have hSmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).bound hEta
  filter_upwards [hSmall, Filter.eventually_ge_atTop (3 : Real)] with x hSmall hx
  have hxPos : 0 < x := by linarith
  have hLogX : 0 < Real.log x := Real.log_pos (by linarith)
  have hSqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxPos
  have hDenPos : 0 < Real.sqrt x * Real.log x := mul_pos hSqrtPos hLogX
  have hInvLog : 1 / Real.log x <= 1 / Real.log 3 :=
    one_div_le_one_div_of_le hLogThree (Real.log_le_log (by norm_num) hx)
  have hCoeff : (N.primeFactors.card : Real) * (1 + 1 / Real.log x) <= A :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hCorrection : norm (principalCenteredWeightedIntegral N x -
      (Robin1984.nicolasJ x : Complex)) <= A / x :=
    (norm_principalCenteredWeightedIntegral_sub_zeta_le hx).trans
      (div_le_div_of_nonneg_right hCoeff hxPos.le)
  have hLog : Real.log x <= eta * Real.sqrt x := by
    have hRpow : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hxPos _
    simpa only [Real.norm_eq_abs, abs_of_pos hLogX, abs_of_pos hRpow,
      Real.sqrt_eq_rpow] using hSmall
  have hScaled : A * Real.log x <= epsilon * Real.sqrt x := by
    calc
      _ <= A * (eta * Real.sqrt x) := mul_le_mul_of_nonneg_left hLog hA
      _ = (A * eta) * Real.sqrt x := by ring
      _ <= _ := mul_le_mul_of_nonneg_right hAEta (Real.sqrt_nonneg x)
  have hKey : (A / x) * (Real.sqrt x * Real.log x) <= epsilon := by
    calc
      _ = (A * Real.log x) * (Real.sqrt x / x) := by ring
      _ <= (epsilon * Real.sqrt x) * (Real.sqrt x / x) :=
        mul_le_mul_of_nonneg_right hScaled (by positivity)
      _ = epsilon := by
        calc
          _ = epsilon * (Real.sqrt x * Real.sqrt x) / x := by ring
          _ = epsilon * x / x := by rw [Real.mul_self_sqrt hxPos.le]
          _ = epsilon := by field_simp [hxPos.ne']
  have hCritical : A / x <= epsilon / (Real.sqrt x * Real.log x) := by
    calc
      _ = ((A / x) * (Real.sqrt x * Real.log x)) / (Real.sqrt x * Real.log x) := by
        field_simp [hDenPos.ne']
      _ <= _ := div_le_div_of_nonneg_right hKey hDenPos.le
  exact hCorrection.trans hCritical

/-- The actual centered principal ambient tail with the canonical zeta
zero-mass coefficient. Cutoffs may depend on N and epsilon. -/
def PrincipalCenteredCriticalBound (N : Nat) [NeZero N] : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    Filter.Eventually (fun x : Real => norm (principalCenteredWeightedIntegral N x) <=
      (riemannXiZeroMass + epsilon) / (Real.sqrt x * Real.log x)) Filter.atTop

/-- The fixed-level principal centered criterion is invariant under removing
the complete finite Euler correction. -/
theorem principalCenteredCriticalBound_iff_riemannCriticalBound
    {N : Nat} [NeZero N] :
    PrincipalCenteredCriticalBound N <-> RiemannCriticalBound := by
  constructor
  next =>
    intro hBound epsilon hEpsilon
    have hHalf : 0 < epsilon / 2 := by linarith
    have hError := eventually_principalCenteredWeightedIntegral_sub_zeta_le (N := N) hHalf
    filter_upwards [hBound (epsilon / 2) hHalf, hError] with x hMain hError
    have hTriangle : norm (Robin1984.nicolasJ x : Complex) <=
        norm (principalCenteredWeightedIntegral N x) +
          norm (principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex)) := by
      calc
        _ = norm (principalCenteredWeightedIntegral N x -
            (principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex))) := by
          congr 1
          ring
        _ <= _ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at hTriangle
    calc
      _ <= _ := hTriangle
      _ <= (riemannXiZeroMass + epsilon / 2) / (Real.sqrt x * Real.log x) +
          (epsilon / 2) / (Real.sqrt x * Real.log x) := add_le_add hMain hError
      _ = _ := by ring
  next =>
    intro hBound epsilon hEpsilon
    have hHalf : 0 < epsilon / 2 := by linarith
    have hError := eventually_principalCenteredWeightedIntegral_sub_zeta_le (N := N) hHalf
    filter_upwards [hBound (epsilon / 2) hHalf, hError] with x hMain hError
    have hTriangle : norm (principalCenteredWeightedIntegral N x) <=
        norm (Robin1984.nicolasJ x : Complex) +
          norm (principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex)) := by
      calc
        _ = norm ((Robin1984.nicolasJ x : Complex) +
            (principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex))) := by
          congr 1
          ring
        _ <= _ := norm_add_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at hTriangle
    calc
      _ <= _ := hTriangle
      _ <= (riemannXiZeroMass + epsilon / 2) / (Real.sqrt x * Real.log x) +
          (epsilon / 2) / (Real.sqrt x * Real.log x) := add_le_add hMain hError
      _ = _ := by ring

/-- RH is equivalent to the critical bound on the actual centered principal
tail at every positive ambient modulus. -/
theorem principalCenteredCriticalBound_iff_riemannHypothesis
    {N : Nat} [NeZero N] :
    PrincipalCenteredCriticalBound N <-> RiemannHypothesis :=
  principalCenteredCriticalBound_iff_riemannCriticalBound.trans
    riemannHypothesis_iff_riemannCriticalBound.symm

end

end RobinBV.NumberField
