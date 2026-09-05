import Mathlib.NumberTheory.Primorial
import RobinBV.NumberField.Proof.PrincipalCharacterAsymptotic

/-!
# Complete moving-primorial endpoint bounds

The first k admitted powers of every excluded prime give a positive lower
bound on the complete correction integral. Every remaining prime power stays
in that positive integral. Together with the omega-only upper bound, this
gives a joint sandwich in the primorial cutoff and integration endpoint.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

/-- Any k powers already admitted at the endpoint give a lower bound on the
entire positive principal correction, without truncating its remaining tail. -/
theorem principalCenteredCorrection_lower_bound
    {N : Nat} [NeZero N] {k : Nat} {x : Real} (hx : 3 <= x)
    (hPowers : forall p : Nat, Membership.mem N.primeFactors p ->
      ((p ^ k : Nat) : Real) <= x) :
    (k : Real) * Finset.sum N.primeFactors (fun p => Real.log p) / (x * Real.log x) <=
      -(principalCenteredWeightedIntegral N x - (Robin1984.nicolasJ x : Complex)).re := by
  let S : Real -> Real := fun t => Finset.sum N.primeFactors (fun p =>
    Real.log p * (Nat.log p (Nat.floor t) : Real))
  let C : Real := (k : Real) * Finset.sum N.primeFactors (fun p => Real.log p)
  have hxOne : 1 < x := by linarith
  have hDifference := integrableOn_imprimitiveChebyshevStep_mul_weight
    (1 : DirichletCharacter Complex N) hx
  have hSInt : IntegrableOn (fun t : Real => S t * Robin1984.robinRealWeight 1 t) (Ioi x) := by
    apply hDifference.neg.re.congr
    filter_upwards [] with t
    simp only [Pi.neg_apply, principalChebyshevStep_sub_primitive_eq_logFloorSum,
      neg_mul, neg_neg, <- Complex.ofReal_mul]
    rfl
  have hWeight := Robin1984.integrableOn_robinRealWeight
    (by norm_num : 1 <= (1 : Nat)) hxOne
  have hConstInt := hWeight.const_mul C
  have hLowerAE : Filter.Eventually (fun t : Real =>
      C * Robin1984.robinRealWeight 1 t <= S t * Robin1984.robinRealWeight 1 t)
        (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hCoefficients : C <= S t := by
      calc
        _ = Finset.sum N.primeFactors (fun p => Real.log p * (k : Real)) := by
          dsimp only [C]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ <= _ := by
          apply Finset.sum_le_sum
          intro p hp
          have hPrime := Nat.prime_of_mem_primeFactors hp
          have hExponent : k <= Nat.log p (Nat.floor t) :=
            Nat.le_log_of_pow_le hPrime.one_lt (Nat.le_floor ((hPowers p hp).trans ht.le))
          have hLogP : 0 <= Real.log p := Real.log_nonneg (by exact_mod_cast hPrime.one_lt.le)
          exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hExponent) hLogP
    exact mul_le_mul_of_nonneg_right hCoefficients
      (Robin1984.robinRealWeight_nonneg (n := 1) (hxOne.trans ht))
  have hMono := integral_mono_ae hConstInt hSInt hLowerAE
  have hConstIntegral : integral (volume.restrict (Ioi x))
      (fun t : Real => C * Robin1984.robinRealWeight 1 t) = C / (x * Real.log x) := by
    rw [integral_const_mul, Robin1984.integral_robinRealWeight
      (by norm_num : 1 <= (1 : Nat)) hxOne]
    norm_num [Real.rpow_neg_one]
    ring
  rw [hConstIntegral] at hMono
  rw [principalCenteredWeightedIntegral_sub_zeta_eq_logFloorIntegral hx,
    Complex.neg_re, Complex.ofReal_re, neg_neg]
  exact hMono

/-- The actual complete correction at the inclusive primorial level.
The modulus varies with P; the centered integral is retained exactly. -/
def movingPrimorialCorrection (P : Nat) (x : Real) : Complex :=
  letI : NeZero (primorial P) := NeZero.mk (primorial_ne_zero P)
  principalCenteredWeightedIntegral (primorial P) x - (Robin1984.nicolasJ x : Complex)

/-- The complete moving principal correction is real, not just bounded in
its real part. -/
theorem movingPrimorialCorrection_im (P : Nat) {x : Real} (hx : 3 <= x) :
    (movingPrimorialCorrection P x).im = 0 := by
  let : NeZero (primorial P) := NeZero.mk (primorial_ne_zero P)
  dsimp only [movingPrimorialCorrection]
  rw [principalCenteredWeightedIntegral_sub_zeta_eq_logFloorIntegral hx,
    Complex.neg_im, Complex.ofReal_im, neg_zero]

/-- Full finite sandwich in both varying parameters. No PNT or RH is used.
The first k layers supply the lower bound, while the upper bound includes
every power of every prime at or below the primorial cutoff. -/
theorem movingPrimorialCorrection_sandwich
    (P k : Nat) {x : Real} (hx : 3 <= x) (hPk : ((P ^ k : Nat) : Real) <= x) :
    And
      ((k : Real) * Chebyshev.theta (P : Real) / (x * Real.log x) <=
        -(movingPrimorialCorrection P x).re)
      (-(movingPrimorialCorrection P x).re <=
        (Nat.primeCounting P : Real) * (1 + 1 / Real.log x) / x) := by
  let : NeZero (primorial P) := NeZero.mk (primorial_ne_zero P)
  have hLower := principalCenteredCorrection_lower_bound (N := primorial P) (k := k) hx
    (fun p hp => by
      rw [primeFactors_primorial] at hp
      have hLe : p <= P := (Nat.mem_primesLE.mp hp).1
      have hPower : ((p ^ k : Nat) : Real) <= ((P ^ k : Nat) : Real) := by
        exact_mod_cast Nat.pow_le_pow_left hLe k
      exact hPower.trans hPk)
  rw [primeFactors_primorial, <- Chebyshev.theta_eq_sum_primesLE_log] at hLower
  have hUpper := norm_principalCenteredWeightedIntegral_sub_zeta_le (N := primorial P) hx
  rw [primeFactors_primorial, Nat.primesLE_card_eq_primeCounting] at hUpper
  constructor
  next =>
    exact hLower
  next =>
    calc
      _ <= abs (movingPrimorialCorrection P x).re := neg_le_abs _
      _ <= norm (movingPrimorialCorrection P x) := Complex.abs_re_le_norm _
      _ <= _ := hUpper

/-- Exact normalization of the full sandwich on every prime-power diagonal.
The lower normalized quantity is theta(P)/P and the upper one is the
normalized prime count times an explicit vanishing logarithmic correction. -/
theorem movingPrimorialCorrection_normalized_sandwich
    (P k : Nat) (hP : 3 <= P) :
    And
      (Chebyshev.theta (P : Real) / (P : Real) <=
        ((P : Real) ^ k * Real.log P) *
          -(movingPrimorialCorrection P ((P : Real) ^ (k + 1))).re)
      (((P : Real) ^ k * Real.log P) *
          -(movingPrimorialCorrection P ((P : Real) ^ (k + 1))).re <=
        ((Nat.primeCounting P : Real) * Real.log P / (P : Real)) *
          (1 + 1 / (((k + 1 : Nat) : Real) * Real.log P))) := by
  let x : Real := (P : Real) ^ (k + 1)
  let F : Real := (P : Real) ^ k * Real.log P
  have hPPos : (0 : Real) < P := by exact_mod_cast (show 0 < P by omega)
  have hPNe : Not ((P : Real) = 0) := hPPos.ne'
  have hLogPos : 0 < Real.log (P : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hK : Not (((k + 1 : Nat) : Real) = 0) := by exact_mod_cast Nat.succ_ne_zero k
  have hx : 3 <= x := by
    have hPow : 0 < P ^ k := Nat.pow_pos (show 0 < P by omega)
    have hNat : 3 <= P ^ (k + 1) := by rw [pow_succ]; nlinarith
    dsimp only [x]
    exact_mod_cast hNat
  have hF : 0 <= F := by dsimp only [F]; positivity
  have hBase := movingPrimorialCorrection_sandwich P (k + 1) hx
    (by simp only [x, Nat.cast_pow]; exact le_rfl)
  have hLower := mul_le_mul_of_nonneg_left hBase.1 hF
  have hUpper := mul_le_mul_of_nonneg_left hBase.2 hF
  have hLowerEq : F * (((k + 1 : Nat) : Real) * Chebyshev.theta (P : Real) /
      (x * Real.log x)) = Chebyshev.theta (P : Real) / (P : Real) := by
    dsimp only [F, x]
    rw [Real.log_pow, pow_succ]
    field_simp [hPNe, hLogPos.ne', hK]
  have hUpperEq : F * ((Nat.primeCounting P : Real) * (1 + 1 / Real.log x) / x) =
      ((Nat.primeCounting P : Real) * Real.log P / (P : Real)) *
        (1 + 1 / (((k + 1 : Nat) : Real) * Real.log P)) := by
    dsimp only [F, x]
    rw [Real.log_pow, pow_succ]
    field_simp [hPNe, hLogPos.ne', hK]
  exact And.intro (hLowerEq.symm.trans_le hLower) (hUpper.trans_eq hUpperEq)

end

end RobinBV.NumberField
