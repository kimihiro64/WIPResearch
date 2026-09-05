import RobinBV.NumberField.Proof.MovingPrimorialEndpoint

/-!
# Complete moving character deletion integrals

Every admitted positive power of every prime up to P is retained. Absolute
integrability follows from the full positive principal correction; it does
not require ERH, nonprincipality or cancellation of the remaining powers.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

/-- The full character-weighted finite-Euler deletion integral. The actual
centered change-of-level interpretation is a separate arithmetic identity. -/
def movingCharacterCorrection {N : Nat} (chi : DirichletCharacter Complex N)
    (P : Nat) (x : Real) : Complex :=
  -integral (volume.restrict (Ioi x)) (fun t : Real =>
    Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t) *
      (Robin1984.robinRealWeight 1 t : Complex))

/-- The entire character deletion integrand is absolutely integrable, and
the norm of its full integral is dominated by the complete principal
correction. The infinite integration tail is not truncated. -/
theorem movingCharacterCorrection_integral_data
    {N : Nat} (chi : DirichletCharacter Complex N) (P : Nat) {x : Real} (hx : 3 <= x) :
    And
      (IntegrableOn (fun t : Real =>
        Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t) *
          (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x))
      (norm (movingCharacterCorrection chi P x) <= -(movingPrimorialCorrection P x).re) := by
  let : NeZero (primorial P) := NeZero.mk (primorial_ne_zero P)
  let S : Real -> Real := fun t => Finset.sum (Nat.primesLE P) (fun p =>
    Real.log p * (Nat.log p (Nat.floor t) : Real))
  have hxOne : 1 < x := by linarith
  have hDifference := integrableOn_imprimitiveChebyshevStep_mul_weight
    (1 : DirichletCharacter Complex (primorial P)) hx
  have hSInt : IntegrableOn (fun t : Real => S t * Robin1984.robinRealWeight 1 t) (Ioi x) := by
    apply hDifference.neg.re.congr
    filter_upwards [] with t
    simp only [Pi.neg_apply, principalChebyshevStep_sub_primitive_eq_logFloorSum,
      neg_mul, neg_neg, <- Complex.ofReal_mul, primeFactors_primorial]
    rfl
  have hStepMeas : Measurable (fun t : Real =>
      Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t)) := by
    let f : Nat -> Complex := fun n => Finset.sum (Nat.primesLE P) (fun p =>
      (Real.log p : Complex) * Finset.sum (Finset.Icc 1 (Nat.log p n))
        (fun j => chi (p : ZMod N) ^ j))
    change Measurable (fun t : Real => f (Nat.floor t))
    exact (measurable_of_countable f).comp Nat.measurable_floor
  have hWeightMeas : Measurable (fun t : Real => (Robin1984.robinRealWeight 1 t : Complex)) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  have hBoundAE : Filter.Eventually (fun t : Real =>
      norm (Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t) *
        (Robin1984.robinRealWeight 1 t : Complex)) <= S t * Robin1984.robinRealWeight 1 t)
      (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hWeightNonneg := Robin1984.robinRealWeight_nonneg (n := 1) (hxOne.trans ht)
    have hSum : norm (Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t)) <= S t := by
      calc
        _ <= Finset.sum (Nat.primesLE P) (fun p => norm (chi.primePowerChebyshevStep p t)) :=
          norm_sum_le _ _
        _ <= _ := by
          apply Finset.sum_le_sum
          intro p hp
          exact chi.norm_primePowerChebyshevStep_le_logFloor (Nat.mem_primesLE.mp hp).2 t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeightNonneg]
    exact mul_le_mul_of_nonneg_right hSum hWeightNonneg
  have hInt : IntegrableOn (fun t : Real =>
      Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t) *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) :=
    hSInt.mono' (hStepMeas.mul hWeightMeas).aestronglyMeasurable hBoundAE
  have hNorm := norm_integral_le_of_norm_le hSInt hBoundAE
  have hIntegral : integral (volume.restrict (Ioi x))
      (fun t : Real => S t * Robin1984.robinRealWeight 1 t) = -(movingPrimorialCorrection P x).re := by
    dsimp only [movingPrimorialCorrection]
    rw [principalCenteredWeightedIntegral_sub_zeta_eq_logFloorIntegral hx,
      Complex.neg_re, Complex.ofReal_re, neg_neg, primeFactors_primorial]
  refine And.intro hInt ?_
  rw [movingCharacterCorrection, norm_neg]
  exact hNorm.trans_eq hIntegral

end

end RobinBV.NumberField
