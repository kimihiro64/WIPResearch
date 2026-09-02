import Mathlib.NumberTheory.LSeries.SumCoeff
import RobinBV.NumberField.Proof.QuadraticDedekindLogDerivativePole
import RobinBV.NumberField.Proof.QuadraticDedekindPrimeSide

/-!
# Mellin continuation of the quadratic Dedekind Chebyshev error

The quadratic Dedekind von Mangoldt sequence is nonnegative and bounded by
twice the ordinary von Mangoldt sequence. Abel summation therefore identifies
its L-series with the Mellin transform of its complete Chebyshev step. After
subtracting the linear main term, the transform agrees on `re(s) > 1` with a
meromorphic expression built from the logarithmic derivative of the canonical
quadratic Dedekind-zeta continuation.
-/

namespace RobinBV.NumberField

open Asymptotics Filter MeasureTheory Set

noncomputable section

def quadraticDedekindMellinStep
    (D : NumberField.OddFundamentalDiscriminant) (t : Real) : Real :=
  (quadraticDedekindChebyshevSum D (Nat.floor t)).re

def quadraticDedekindPsiError
    (D : NumberField.OddFundamentalDiscriminant) (t : Real) : Real :=
  quadraticDedekindMellinStep D t - t

theorem norm_quadraticDedekindMangoldtSequence_le
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) :
    norm (quadraticDedekindMangoldtSequence D n) <=
      2 * ArithmeticFunction.vonMangoldt n := by
  have hReal : quadraticDedekindMangoldtSequence D n =
      ((quadraticDedekindMangoldtSequence D n).re : Complex) := by
    apply Complex.ext
    next => simp
    next => simpa using quadraticDedekindMangoldtSequence_im D n
  rw [hReal, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (quadraticDedekindMangoldtSequence_re_nonneg D n)]
  unfold quadraticDedekindMangoldtSequence twistedMangoldtSequence
  rcases D.character_isQuadratic n with hZero | hOne | hNeg
  next => rw [hZero]; simp [ArithmeticFunction.vonMangoldt_nonneg]
  next => rw [hOne]; simp [ArithmeticFunction.vonMangoldt_nonneg]
  next => rw [hNeg]; simp [ArithmeticFunction.vonMangoldt_nonneg]

theorem quadraticDedekindMangoldtNormPartialSums_isBigO
    (D : NumberField.OddFundamentalDiscriminant) :
    (fun n : Nat =>
      Finset.sum (Finset.Icc 1 n)
        (fun k => norm (quadraticDedekindMangoldtSequence D k)))
      =O[atTop] (fun n : Nat => (n : Real) ^ (1 : Real)) := by
  let c : Real := 2 * (Real.log 4 + 4)
  apply (IsBigOWith.of_bound c
    (Eventually.of_forall fun n => ?_)).isBigO
  have hSumNonneg : 0 <= Finset.sum (Finset.Icc 1 n)
      (fun k => norm (quadraticDedekindMangoldtSequence D k)) :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hLambdaSum :
      Finset.sum (Finset.Icc 1 n)
          (fun k => ArithmeticFunction.vonMangoldt k) =
        Chebyshev.psi (n : Real) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    symm
    rw [<- Finset.insert_Icc_add_one_left_eq_Icc n.zero_le,
      Finset.sum_insert (by aesop)]
    simp
  rw [Real.norm_eq_abs, abs_of_nonneg hSumNonneg,
    Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) 1),
    Real.rpow_one]
  calc
    Finset.sum (Finset.Icc 1 n)
        (fun k => norm (quadraticDedekindMangoldtSequence D k)) <=
        Finset.sum (Finset.Icc 1 n)
          (fun k => 2 * ArithmeticFunction.vonMangoldt k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_quadraticDedekindMangoldtSequence_le D k
    _ = 2 * Finset.sum (Finset.Icc 1 n)
        (fun k => ArithmeticFunction.vonMangoldt k) := by
      rw [Finset.mul_sum]
    _ = 2 * Chebyshev.psi (n : Real) := by rw [hLambdaSum]
    _ <= 2 * ((Real.log 4 + 4) * n) := by
      exact mul_le_mul_of_nonneg_left
        (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)) (by norm_num)
    _ = c * n := by dsimp [c]; ring

theorem quadraticDedekindMellinStep_nonneg
    (D : NumberField.OddFundamentalDiscriminant) (t : Real) :
    0 <= quadraticDedekindMellinStep D t := by
  unfold quadraticDedekindMellinStep
  exact quadraticDedekindChebyshevSum_re_nonneg D (Nat.floor t)

theorem quadraticDedekindChebyshevSum_re_le_two_psi
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) :
    (quadraticDedekindChebyshevSum D n).re <=
      2 * Chebyshev.psi (n : Real) := by
  have hReSum : (quadraticDedekindChebyshevSum D n).re =
      Finset.sum (Finset.Icc 1 n)
        (fun k => (quadraticDedekindMangoldtSequence D k).re) := by
    unfold quadraticDedekindChebyshevSum
    rw [map_sum]
  have hLambdaSum :
      Finset.sum (Finset.Icc 1 n)
          (fun k => ArithmeticFunction.vonMangoldt k) =
        Chebyshev.psi (n : Real) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    symm
    rw [<- Finset.insert_Icc_add_one_left_eq_Icc n.zero_le,
      Finset.sum_insert (by aesop)]
    simp
  rw [hReSum, <- hLambdaSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  calc
    (quadraticDedekindMangoldtSequence D k).re <=
        norm (quadraticDedekindMangoldtSequence D k) :=
      Complex.re_le_norm _
    _ <= 2 * ArithmeticFunction.vonMangoldt k :=
      norm_quadraticDedekindMangoldtSequence_le D k

theorem quadraticDedekindMellinStep_le_two_psi
    (D : NumberField.OddFundamentalDiscriminant) (t : Real) :
    quadraticDedekindMellinStep D t <= 2 * Chebyshev.psi t := by
  unfold quadraticDedekindMellinStep
  rw [<- Chebyshev.psi_eq_psi_coe_floor t]
  exact quadraticDedekindChebyshevSum_re_le_two_psi D (Nat.floor t)

theorem quadraticDedekindLogDeriv_eq_psiMellin
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 < s.re) :
    -logDeriv (quadraticDedekindZetaContinuation D) s =
      s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (quadraticDedekindMellinStep D t : Complex) *
          (t : Complex) ^ (-(s + 1))) := by
  have hAbel := LSeries_eq_mul_integral'
    (quadraticDedekindMangoldtSequence D)
    (r := (1 : Real)) (by norm_num) hs
    (quadraticDedekindMangoldtNormPartialSums_isBigO D)
  calc
    -logDeriv (quadraticDedekindZetaContinuation D) s =
        LSeries (quadraticDedekindMangoldtSequence D) s :=
      neg_logDeriv_quadraticDedekindZetaContinuation_eq_LSeries D hs
    _ = s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (Finset.sum (Finset.Icc 1 (Nat.floor t))
          (quadraticDedekindMangoldtSequence D)) *
            (t : Complex) ^ (-(s + 1))) := hAbel
    _ = s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (quadraticDedekindMellinStep D t : Complex) *
          (t : Complex) ^ (-(s + 1))) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      congr 1
      apply Complex.ext
      next => rfl
      next =>
        simp only [map_sum, Complex.ofReal_im]
        rw [Finset.sum_eq_zero]
        intro k hk
        exact quadraticDedekindMangoldtSequence_im D k

theorem quadraticDedekindPsiMellin_integrable
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (quadraticDedekindMellinStep D t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  let c : Real := 2 * (Real.log 4 + 4)
  have hcPos : 0 < c := by
    dsimp [c]
    positivity
  have hPower : IntegrableOn
      (fun t : Real => (c : Complex) * (t : Complex) ^ (-s)) (Ioi 1) := by
    exact (integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.neg_re]; linarith) (by norm_num)).const_mul
        (c : Complex)
  apply Integrable.mono
    (g := fun t : Real => (c : Complex) * (t : Complex) ^ (-s)) hPower
  next =>
    have hStepMeasurable : Measurable (quadraticDedekindMellinStep D) := by
      unfold quadraticDedekindMellinStep
      exact (measurable_of_countable (fun n : Nat =>
        (quadraticDedekindChebyshevSum D n).re)).comp Nat.measurable_floor
    have hCpow : ContinuousOn
        (fun t : Real => (t : Complex) ^ (-(s + 1))) (Ioi 1) :=
      continuousOn_of_forall_continuousAt fun t ht =>
        Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
          (Or.inr (ne_of_gt (lt_trans (by norm_num) ht)))
    exact ((Complex.measurable_ofReal.comp hStepMeasurable).aestronglyMeasurable.mul
      (hCpow.aestronglyMeasurable measurableSet_Ioi))
  next =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htPos : 0 < t := lt_trans (by norm_num) ht
    have hPsi := Chebyshev.psi_le_const_mul_self htPos.le
    have hStepBound : quadraticDedekindMellinStep D t <= c * t := by
      calc
        quadraticDedekindMellinStep D t <= 2 * Chebyshev.psi t :=
          quadraticDedekindMellinStep_le_two_psi D t
        _ <= 2 * ((Real.log 4 + 4) * t) :=
          mul_le_mul_of_nonneg_left hPsi (by norm_num)
        _ = c * t := by dsimp [c]; ring
    have hPowNonneg : 0 <= t ^ (-(s + 1)).re :=
      Real.rpow_nonneg htPos.le _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (quadraticDedekindMellinStep_nonneg D t),
      abs_of_pos hcPos, Complex.norm_cpow_eq_rpow_re_of_pos htPos]
    calc
      quadraticDedekindMellinStep D t * t ^ (-(s + 1)).re <=
          (c * t) * t ^ (-(s + 1)).re :=
        mul_le_mul_of_nonneg_right hStepBound hPowNonneg
      _ = c * t ^ (-s).re := by
        calc
          (c * t) * t ^ (-(s + 1)).re =
              c * (t ^ (1 : Real) * t ^ (-(s + 1)).re) := by
            rw [Real.rpow_one]
            ring
          _ = c * t ^ ((1 : Real) + (-(s + 1)).re) := by
            rw [Real.rpow_add htPos]
          _ = c * t ^ (-s).re := by
            congr 2
            simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
            ring

theorem quadraticDedekindLinearMellin_integrable
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  have hPower : IntegrableOn
      (fun t : Real => (t : Complex) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.neg_re]; linarith) (by norm_num)
  apply hPower.congr_fun
  next =>
    intro t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_trans (by norm_num) ht))
    change (t : Complex) ^ (-s) =
      (t : Complex) * (t : Complex) ^ (-(s + 1))
    symm
    calc
      (t : Complex) * (t : Complex) ^ (-(s + 1)) =
          (t : Complex) ^ (1 : Complex) *
            (t : Complex) ^ (-(s + 1)) := by
        rw [Complex.cpow_one]
      _ = (t : Complex) ^ ((1 : Complex) + -(s + 1)) := by
        rw [Complex.cpow_add _ _ htZero]
      _ = (t : Complex) ^ (-s) := by
        congr 1
        ring
  next => exact measurableSet_Ioi

theorem quadraticDedekindPsiErrorMellin_eq_logDeriv
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 < s.re) :
    integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-(s + 1))) =
      (-logDeriv (quadraticDedekindZetaContinuation D) s) / s -
        1 / (s - 1) := by
  have hsZero : Not (s = 0) := by
    intro hZero
    subst s
    norm_num at hs
  have hLinear :
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t => (t : Complex) * (t : Complex) ^ (-(s + 1))) =
        1 / (s - 1) := by
    calc
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t => (t : Complex) * (t : Complex) ^ (-(s + 1))) =
          integral (volume.restrict (Ioi (1 : Real)))
            (fun t => (t : Complex) ^ (-s)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have htZero : Not ((t : Complex) = 0) :=
          Complex.ofReal_ne_zero.mpr
            (ne_of_gt (lt_trans (by norm_num) ht))
        calc
          (t : Complex) * (t : Complex) ^ (-(s + 1)) =
              (t : Complex) ^ (1 : Complex) *
                (t : Complex) ^ (-(s + 1)) := by
            rw [Complex.cpow_one]
          _ = (t : Complex) ^ ((1 : Complex) + -(s + 1)) := by
            rw [Complex.cpow_add _ _ htZero]
          _ = (t : Complex) ^ (-s) := by
            congr 1
            ring
      _ = 1 / (s - 1) := by
        rw [integral_Ioi_cpow_of_lt
          (by simp only [Complex.neg_re]; linarith) (by norm_num)]
        rw [Complex.ofReal_one, Complex.one_cpow]
        rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
  rw [show (fun t : Real => (quadraticDedekindPsiError D t : Complex) *
      (t : Complex) ^ (-(s + 1))) =
      (fun t : Real =>
        (quadraticDedekindMellinStep D t : Complex) *
            (t : Complex) ^ (-(s + 1)) -
          (t : Complex) * (t : Complex) ^ (-(s + 1))) by
      funext t
      unfold quadraticDedekindPsiError
      push_cast
      ring]
  rw [integral_sub (quadraticDedekindPsiMellin_integrable D hs)
    (quadraticDedekindLinearMellin_integrable hs), hLinear]
  have hLog := quadraticDedekindLogDeriv_eq_psiMellin D hs
  congr 1
  symm
  apply (div_eq_iff hsZero).2
  rw [hLog]
  ring

theorem quadraticDedekindPsiErrorMellin_integrable
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (quadraticDedekindPsiError D t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  have hSub := (quadraticDedekindPsiMellin_integrable D hs).sub
    (quadraticDedekindLinearMellin_integrable hs)
  apply hSub.congr_fun
  next =>
    intro t ht
    change
      (quadraticDedekindMellinStep D t : Complex) *
          (t : Complex) ^ (-(s + 1)) -
        (t : Complex) * (t : Complex) ^ (-(s + 1)) =
      (quadraticDedekindPsiError D t : Complex) *
        (t : Complex) ^ (-(s + 1))
    unfold quadraticDedekindPsiError
    push_cast
    ring
  next => exact measurableSet_Ioi

def quadraticDedekindPsiMellinContinuation
    (D : NumberField.OddFundamentalDiscriminant) (s : Complex) : Complex :=
  (-logDeriv (quadraticDedekindZetaContinuation D) s) / s -
    1 / (s - 1)

theorem quadraticDedekindPsiMellinContinuation_simplePoleLimit_Ioi
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hRhoZero : Not (rho = 0))
    (hOne : Not (rho = 1)) :
    Exists fun c : Complex => And (Not (c = 0))
      (Tendsto
        (fun u : Real => (u : Complex) *
          quadraticDedekindPsiMellinContinuation D
            (rho + (u : Complex)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds c)) := by
  choose a ha hLog using
    quadraticDedekindZetaLogDeriv_simplePoleLimit_Ioi D hZero hOne
  let l : Filter Real := nhdsWithin 0 (Set.Ioi (0 : Real))
  have hU : Tendsto (fun u : Real => (u : Complex)) l (nhds 0) := by
    have hContinuous : ContinuousAt (fun u : Real => (u : Complex)) 0 := by
      fun_prop
    simpa [l] using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hShift : Tendsto (fun u : Real => rho + (u : Complex)) l
      (nhds rho) := by
    simpa using tendsto_const_nhds.add hU
  have hInvAt : ContinuousAt (fun z : Complex => 1 / z) rho :=
    continuousAt_const.div continuousAt_id hRhoZero
  have hInvShift : Tendsto
      (fun u : Real => Inv.inv (rho + (u : Complex))) l
      (nhds (Inv.inv rho)) := by
    simpa [one_div] using hInvAt.tendsto.comp hShift
  have hInvDenAt : ContinuousAt (fun z : Complex => 1 / (z - 1)) rho :=
    continuousAt_const.div (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.mpr hOne)
  have hInvDen : Tendsto
      (fun u : Real => Inv.inv (rho + (u : Complex) - 1)) l
      (nhds (Inv.inv (rho - 1))) := by
    simpa [one_div] using hInvDenAt.tendsto.comp hShift
  have hMain : Tendsto (fun u : Real =>
      (-(u : Complex) *
        logDeriv (quadraticDedekindZetaContinuation D)
          (rho + (u : Complex))) *
        Inv.inv (rho + (u : Complex))) l
      (nhds ((-a) * Inv.inv rho)) := by
    have hLogNeg := hLog.neg
    simpa [l, neg_mul] using hLogNeg.mul hInvShift
  have hCorrection : Tendsto (fun u : Real =>
      (u : Complex) * Inv.inv (rho + (u : Complex) - 1)) l
      (nhds 0) := by
    simpa using hU.mul hInvDen
  have hTotal : Tendsto (fun u : Real =>
      ((-(u : Complex) *
        logDeriv (quadraticDedekindZetaContinuation D)
          (rho + (u : Complex))) *
          Inv.inv (rho + (u : Complex))) -
        (u : Complex) * Inv.inv (rho + (u : Complex) - 1)) l
      (nhds ((-a) * Inv.inv rho)) := by
    simpa using hMain.sub hCorrection
  have hc : Not (((-a) * Inv.inv rho) = 0) :=
    mul_ne_zero (neg_ne_zero.mpr ha) (inv_ne_zero hRhoZero)
  refine Exists.intro ((-a) * Inv.inv rho) (And.intro hc ?_)
  apply hTotal.congr'
  filter_upwards with u
  unfold quadraticDedekindPsiMellinContinuation
  ring

theorem exists_rightmost_quadraticDedekindPsiMellin_pole_of_not_ERH
    (D : NumberField.OddFundamentalDiscriminant)
    (hNotERH : Not (QuadraticDedekindZetaERH D)) :
    Exists fun rhoMax : Complex =>
      And (quadraticDedekindZetaContinuation D rhoMax = 0)
        (And ((1 / 2 : Real) < rhoMax.re)
          (And (rhoMax.re < 1)
            (And
              (forall v : Real, 0 < v ->
                Not (quadraticDedekindZetaContinuation D
                  (rhoMax + (v : Complex)) = 0))
              (Exists fun c : Complex => And (Not (c = 0))
                (Tendsto
                  (fun u : Real => (u : Complex) *
                    quadraticDedekindPsiMellinContinuation D
                      (rhoMax + (u : Complex)))
                  (nhdsWithin 0 (Set.Ioi 0)) (nhds c)))))) := by
  choose rhoMax hZero hHalf hOne hRay hLog using
    exists_rightmost_quadraticDedekindZeta_logDeriv_pole_of_not_ERH
      D hNotERH
  have hRhoZero : Not (rhoMax = 0) := by
    intro hEq
    subst rhoMax
    norm_num at hHalf
  have hRhoOne : Not (rhoMax = 1) := by
    intro hEq
    subst rhoMax
    norm_num at hOne
  choose c hc hLimit using
    quadraticDedekindPsiMellinContinuation_simplePoleLimit_Ioi
      D hZero hRhoZero hRhoOne
  exact Exists.intro rhoMax
    (And.intro hZero
      (And.intro hHalf
        (And.intro hOne
          (And.intro hRay
            (Exists.intro c (And.intro hc hLimit))))))

def quadraticDedekindPsiMellinStartup
    (D : NumberField.OddFundamentalDiscriminant)
    (x : Real) (s : Complex) : Complex :=
  integral (volume.restrict (Ioc (1 : Real) x))
    (fun t : Real => (quadraticDedekindPsiError D t : Complex) *
      (t : Complex) ^ (-(s + 1)))

def quadraticDedekindPsiMellinTailContinuation
    (D : NumberField.OddFundamentalDiscriminant)
    (x : Real) (s : Complex) : Complex :=
  quadraticDedekindPsiMellinContinuation D s -
    quadraticDedekindPsiMellinStartup D x s

theorem quadraticDedekindPsiErrorTailMellin_eq_continuation
    (D : NumberField.OddFundamentalDiscriminant)
    {x : Real} (hx : 1 <= x) {s : Complex} (hs : 1 < s.re) :
    integral (volume.restrict (Ioi x))
        (fun t : Real => (quadraticDedekindPsiError D t : Complex) *
          (t : Complex) ^ (-(s + 1))) =
      quadraticDedekindPsiMellinTailContinuation D x s := by
  have hFull := quadraticDedekindPsiErrorMellin_integrable D hs
  have hStartup : IntegrableOn
      (fun t : Real => (quadraticDedekindPsiError D t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioc 1 x) :=
    hFull.mono_set Ioc_subset_Ioi_self
  have hTail : IntegrableOn
      (fun t : Real => (quadraticDedekindPsiError D t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi x) :=
    hFull.mono_set (Ioi_subset_Ioi hx)
  have hSplit :
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t : Real => (quadraticDedekindPsiError D t : Complex) *
            (t : Complex) ^ (-(s + 1))) =
        integral (volume.restrict (Ioc (1 : Real) x))
            (fun t : Real => (quadraticDedekindPsiError D t : Complex) *
              (t : Complex) ^ (-(s + 1))) +
          integral (volume.restrict (Ioi x))
            (fun t : Real => (quadraticDedekindPsiError D t : Complex) *
              (t : Complex) ^ (-(s + 1))) := by
    rw [<- Ioc_union_Ioi_eq_Ioi hx,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
    next => exact hStartup
    next => exact hTail
  unfold quadraticDedekindPsiMellinTailContinuation
    quadraticDedekindPsiMellinContinuation
    quadraticDedekindPsiMellinStartup
  rw [<- quadraticDedekindPsiErrorMellin_eq_logDeriv D hs]
  rw [hSplit]
  ring

end

end RobinBV.NumberField
