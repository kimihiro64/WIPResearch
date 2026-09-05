import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Coefficient
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Expansion
import Robin1984.NicolasLandau.WeightedPsiIntegral
import RobinBV.NumberField.Proof.QuadraticDedekindWeightedError

/-!
# Weighted arithmetic formula for a quadratic character

The twisted von Mangoldt series is exchanged with Robin's Mellin cutoff on
the safe line. A signed prime-power indicator then identifies the resulting
arithmetic series with the quadratic-character weighted Chebyshev integral.
-/

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set

noncomputable section

theorem summable_quadraticCharacter_twistedMangoldt_cpow
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 < s.re) :
    Summable (fun m : Nat =>
      twistedMangoldtSequence D.character m / (m : Complex) ^ s) := by
  have hSeries : LSeriesSummable
      (twistedMangoldtSequence D.character) s := by
    have hSequence : twistedMangoldtSequence D.character =
        (fun n : Nat => D.character n) *
          (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) := by
      funext n
      rfl
    rw [hSequence]
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt
      D.character hs
  refine hSeries.congr ?_
  intro m
  by_cases hm : m = 0
  next => simp [hm, twistedMangoldtSequence]
  next => rw [LSeries.term_of_ne_zero hm]

theorem tsum_quadraticCharacter_twistedMangoldt_eq_neg_logDeriv
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 < s.re) :
    tsum (fun m : Nat =>
      twistedMangoldtSequence D.character m / (m : Complex) ^ s) =
      -logDeriv D.character.LFunction s := by
  rw [neg_logDeriv_LFunction_eq_LSeries D.character hs, LSeries]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  next => simp [hm, twistedMangoldtSequence]
  next => rw [LSeries.term_of_ne_zero hm]

theorem norm_quadraticCharacter_twistedMangoldt_vertical_eq
    (D : NumberField.OddFundamentalDiscriminant)
    (c t : Real) (m : Nat) :
    norm (twistedMangoldtSequence D.character m /
        (m : Complex) ^ ((c : Complex) + (t : Complex) * Complex.I)) =
      norm (twistedMangoldtSequence D.character m /
        (m : Complex) ^ (c : Complex)) := by
  cases m with
  | zero => simp [twistedMangoldtSequence]
  | succ m =>
      rw [norm_div, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m),
        Complex.norm_natCast_cpow_of_pos (Nat.succ_pos m)]
      simp

theorem integral_quadraticCharacter_twistedMangoldt_series_mul
    (D : NumberField.OddFundamentalDiscriminant)
    {c : Real} (hc : 1 < c)
    {H : Real -> Complex} (hH : Integrable H) :
    tsum (fun m : Nat => integral volume (fun t : Real =>
        (twistedMangoldtSequence D.character m /
          (m : Complex) ^ ((c : Complex) +
            (t : Complex) * Complex.I)) * H t)) =
      integral volume (fun t : Real =>
        (-logDeriv D.character.LFunction
          ((c : Complex) + (t : Complex) * Complex.I)) * H t) := by
  let F : Nat -> Real -> Complex := fun m t =>
    (twistedMangoldtSequence D.character m /
      (m : Complex) ^ ((c : Complex) +
        (t : Complex) * Complex.I)) * H t
  let A : Nat -> Real := fun m =>
    norm (twistedMangoldtSequence D.character m /
      (m : Complex) ^ (c : Complex))
  have hNorm : forall m : Nat, forall t : Real,
      norm (F m t) = A m * norm (H t) := by
    intro m t
    dsimp [F, A]
    rw [norm_mul,
      norm_quadraticCharacter_twistedMangoldt_vertical_eq D]
  have hFInt : forall m : Nat, Integrable (F m) := by
    intro m
    have hCoeffMeas : Measurable (fun t : Real =>
        twistedMangoldtSequence D.character m /
          (m : Complex) ^ ((c : Complex) +
            (t : Complex) * Complex.I)) := by
      fun_prop
    have hFMeas : AEStronglyMeasurable (F m) volume :=
      hCoeffMeas.aestronglyMeasurable.mul hH.aestronglyMeasurable
    apply (hH.norm.const_mul (A m)).mono' hFMeas
    filter_upwards with t
    rw [hNorm]
  have hNormIntegral : forall m : Nat,
      integral volume (fun t : Real => norm (F m t)) =
        A m * integral volume (fun t : Real => norm (H t)) := by
    intro m
    have hFunction : (fun t : Real => norm (F m t)) =
        (fun t : Real => A m * norm (H t)) := by
      funext t
      exact hNorm m t
    rw [hFunction, integral_const_mul]
  have hASum : Summable A := by
    exact (summable_quadraticCharacter_twistedMangoldt_cpow D
      (s := (c : Complex)) (by simpa using hc)).norm
  have hNormSum : Summable (fun m : Nat =>
      integral volume (fun t : Real => norm (F m t))) := by
    have hProduct := hASum.mul_right
      (integral volume (fun t : Real => norm (H t)))
    exact hProduct.congr (fun m => (hNormIntegral m).symm)
  calc
    tsum (fun m : Nat => integral volume (F m)) =
        integral volume (fun t : Real => tsum (fun m : Nat => F m t)) :=
      integral_tsum_of_summable_integral_norm hFInt hNormSum
    _ = integral volume (fun t : Real =>
        (-logDeriv D.character.LFunction
          ((c : Complex) + (t : Complex) * Complex.I)) * H t) := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp [F]
      rw [tsum_mul_right,
        tsum_quadraticCharacter_twistedMangoldt_eq_neg_logDeriv
          D (by simpa using hc)]

theorem quadraticCharacter_twistedMangoldt_mul_cutoff_eq_integral
    (D : NumberField.OddFundamentalDiscriminant)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    {c : Real} (hcPos : 0 < c) (hcLt : c < n) (m : Nat) :
    twistedMangoldtSequence D.character m *
        Robin1984.robinCutoffMellinTest n x (m : Real) =
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          (twistedMangoldtSequence D.character m /
            (m : Complex) ^ ((c : Complex) +
              (t : Complex) * Complex.I)) *
            mellin (Robin1984.robinCutoffMellinTest n x)
              ((c : Complex) + (t : Complex) * Complex.I)) := by
  by_cases hm : m = 0
  next => simp [hm, twistedMangoldtSequence]
  next =>
    have hmPos : 0 < (m : Real) := by
      exact_mod_cast (Nat.pos_of_ne_zero hm)
    have hInv := Robin1984.mellinInv_mellin_robinCutoffMellinTest
      hn hx hcPos hcLt hmPos
    simp only [mellinInv, RCLike.real_smul_eq_coe_mul, smul_eq_mul,
      Complex.ofReal_natCast] at hInv
    rw [<- hInv]
    calc
      twistedMangoldtSequence D.character m *
          ((((1 / (2 * Real.pi) : Real) : Complex)) *
            integral volume (fun t : Real =>
              (m : Complex) ^ (-((c : Complex) +
                (t : Complex) * Complex.I)) *
                mellin (Robin1984.robinCutoffMellinTest n x)
                  ((c : Complex) + (t : Complex) * Complex.I))) =
        (((1 / (2 * Real.pi) : Real) : Complex)) *
          (twistedMangoldtSequence D.character m *
            integral volume (fun t : Real =>
              (m : Complex) ^ (-((c : Complex) +
                (t : Complex) * Complex.I)) *
                mellin (Robin1984.robinCutoffMellinTest n x)
                  ((c : Complex) + (t : Complex) * Complex.I))) := by
        ring
      _ = (((1 / (2 * Real.pi) : Real) : Complex)) *
          integral volume (fun t : Real =>
            twistedMangoldtSequence D.character m *
              ((m : Complex) ^ (-((c : Complex) +
                (t : Complex) * Complex.I)) *
                mellin (Robin1984.robinCutoffMellinTest n x)
                  ((c : Complex) + (t : Complex) * Complex.I))) := by
        rw [integral_const_mul]
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards with t
        rw [Complex.cpow_neg, div_eq_mul_inv]
        ring

theorem quadraticCharacterPrimePowerSum_eq_safeLineIntegral
    (D : NumberField.OddFundamentalDiscriminant)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    {c : Real} (hc : 1 < c) (hcLt : c < n) :
    tsum (fun m : Nat => twistedMangoldtSequence D.character m *
        Robin1984.robinCutoffMellinTest n x (m : Real)) =
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          (-logDeriv D.character.LFunction
            ((c : Complex) + (t : Complex) * Complex.I)) *
            mellin (Robin1984.robinCutoffMellinTest n x)
              ((c : Complex) + (t : Complex) * Complex.I)) := by
  have hcPos : 0 < c := lt_trans Real.zero_lt_one hc
  have hVertical : Integrable (fun t : Real =>
      mellin (Robin1984.robinCutoffMellinTest n x)
        ((c : Complex) + (t : Complex) * Complex.I)) :=
    Robin1984.verticalIntegrable_mellin_robinCutoffMellinTest
      hn hx hcPos hcLt
  have hSwap :=
    integral_quadraticCharacter_twistedMangoldt_series_mul
      D hc hVertical
  calc
    tsum (fun m : Nat => twistedMangoldtSequence D.character m *
        Robin1984.robinCutoffMellinTest n x (m : Real)) =
      tsum (fun m : Nat =>
        (((1 / (2 * Real.pi) : Real) : Complex)) *
          integral volume (fun t : Real =>
            (twistedMangoldtSequence D.character m /
              (m : Complex) ^ ((c : Complex) +
                (t : Complex) * Complex.I)) *
              mellin (Robin1984.robinCutoffMellinTest n x)
                ((c : Complex) + (t : Complex) * Complex.I))) := by
        apply tsum_congr
        intro m
        exact quadraticCharacter_twistedMangoldt_mul_cutoff_eq_integral
          D hn hx hcPos hcLt m
    _ = (((1 / (2 * Real.pi) : Real) : Complex)) *
        tsum (fun m : Nat => integral volume (fun t : Real =>
          (twistedMangoldtSequence D.character m /
            (m : Complex) ^ ((c : Complex) +
              (t : Complex) * Complex.I)) *
            mellin (Robin1984.robinCutoffMellinTest n x)
              ((c : Complex) + (t : Complex) * Complex.I))) := by
      rw [tsum_mul_left]
    _ = _ := by rw [hSwap]

def quadraticCharacterPrimePowerIndicator
    (D : NumberField.OddFundamentalDiscriminant)
    (n m : Nat) (t : Real) : Complex :=
  (Ici (m : Real)).indicator
    (fun u : Real => twistedMangoldtSequence D.character m *
      (Robin1984.robinRealWeight n u : Complex)) t

theorem integrableOn_quadraticCharacterPrimePowerIndicator
    (D : NumberField.OddFundamentalDiscriminant)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    (m : Nat) :
    IntegrableOn (quadraticCharacterPrimePowerIndicator D n m)
      (Ioi x) := by
  have hWeight : IntegrableOn (fun t : Real =>
      (Robin1984.robinRealWeight n t : Complex)) (Ioi x) :=
    (Robin1984.integrableOn_robinRealWeight hn hx).ofReal
  exact (hWeight.const_mul
    (twistedMangoldtSequence D.character m)).indicator measurableSet_Ici

theorem integral_quadraticCharacterPrimePowerIndicator
    (D : NumberField.OddFundamentalDiscriminant)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    (m : Nat) :
    integral (volume.restrict (Ioi x))
        (quadraticCharacterPrimePowerIndicator D n m) =
      twistedMangoldtSequence D.character m *
        Robin1984.robinCutoffMellinTest n x (m : Real) := by
  have hWeightIntegral (a : Real) (ha : 1 < a) :
      integral (volume.restrict (Ioi a)) (fun t : Real =>
        (Robin1984.robinRealWeight n t : Complex)) =
      (a : Complex) ^ (-(n : Complex)) *
        (((Inv.inv (Real.log a) : Real) : Complex)) := by
    rw [integral_complex_ofReal]
    exact Robin1984.complex_integral_robinRealWeight hn ha
  by_cases hm : (m : Real) <= x
  next =>
    have hIntegral : integral (volume.restrict (Ioi x))
        (quadraticCharacterPrimePowerIndicator D n m) =
      twistedMangoldtSequence D.character m *
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Robin1984.robinRealWeight n t : Complex)) := by
      unfold quadraticCharacterPrimePowerIndicator
      calc
        integral (volume.restrict (Ioi x))
            ((Ici (m : Real)).indicator (fun u : Real =>
              twistedMangoldtSequence D.character m *
                (Robin1984.robinRealWeight n u : Complex))) =
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            twistedMangoldtSequence D.character m *
              (Robin1984.robinRealWeight n t : Complex)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            exact Set.indicator_of_mem (s := Ici (m : Real))
              (le_trans hm ht.le) _
        _ = _ := integral_const_mul _ _
    rw [hIntegral, hWeightIntegral x hx]
    simp only [Robin1984.robinCutoffMellinTest, if_pos hm]
  next =>
    have hmGt : x < (m : Real) := lt_of_not_ge hm
    have hmOne : 1 < (m : Real) := lt_trans hx hmGt
    have hSet : Set.inter (Ioi x) (Ici (m : Real)) =
        Ici (m : Real) := by
      apply inter_eq_right.mpr
      intro t ht
      exact lt_of_lt_of_le hmGt ht
    have hIntegral : integral (volume.restrict (Ioi x))
        (quadraticCharacterPrimePowerIndicator D n m) =
      twistedMangoldtSequence D.character m *
        integral (volume.restrict (Ioi (m : Real))) (fun t : Real =>
          (Robin1984.robinRealWeight n t : Complex)) := by
      unfold quadraticCharacterPrimePowerIndicator
      rw [setIntegral_indicator measurableSet_Ici]
      change integral (volume.restrict
          (Set.inter (Ioi x) (Ici (m : Real)))) (fun t : Real =>
            twistedMangoldtSequence D.character m *
              (Robin1984.robinRealWeight n t : Complex)) = _
      rw [hSet, integral_Ici_eq_integral_Ioi, integral_const_mul]
    rw [hIntegral, hWeightIntegral (m : Real) hmOne]
    simp only [Robin1984.robinCutoffMellinTest, if_neg hm]

theorem norm_quadraticCharacterPrimePowerIndicator_le
    (D : NumberField.OddFundamentalDiscriminant)
    {n m : Nat} {t : Real} (ht : 1 < t) :
    norm (quadraticCharacterPrimePowerIndicator D n m t) <=
      norm (Robin1984.robinPrimePowerIndicator n m t : Complex) := by
  unfold quadraticCharacterPrimePowerIndicator
  unfold Robin1984.robinPrimePowerIndicator
  by_cases hm : (m : Real) <= t
  next =>
    rw [Set.indicator_of_mem (s := Ici (m : Real)) hm,
      Set.indicator_of_mem (s := Ici (m : Real)) hm]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Robin1984.robinRealWeight_nonneg ht)]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Robin1984.robinRealWeight_nonneg ht))]
    exact mul_le_mul_of_nonneg_right
      (norm_twistedMangoldtSequence_le_vonMangoldt D.character m)
      (Robin1984.robinRealWeight_nonneg ht)
  next =>
    rw [Set.indicator_of_notMem (s := Ici (m : Real)) hm,
      Set.indicator_of_notMem (s := Ici (m : Real)) hm]
    simp

theorem summable_integral_norm_quadraticCharacterPrimePowerIndicators
    (D : NumberField.OddFundamentalDiscriminant)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    Summable (fun m : Nat => integral (volume.restrict (Ioi x))
      (fun t : Real =>
        norm (quadraticCharacterPrimePowerIndicator D n m t))) := by
  have hnOne : 1 <= n := by omega
  have hMajor : Summable (fun m : Nat =>
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm (Robin1984.robinPrimePowerIndicator n m t : Complex))) :=
    Robin1984.summable_integral_norm_robinPrimePowerIndicators hn hx
  apply Summable.of_nonneg_of_le
  next => exact fun m => integral_nonneg (fun t => norm_nonneg _)
  next =>
    intro m
    have hLeft : IntegrableOn
        (quadraticCharacterPrimePowerIndicator D n m) (Ioi x) :=
      integrableOn_quadraticCharacterPrimePowerIndicator
        D hnOne hx m
    have hRight : IntegrableOn (fun t : Real =>
        (Robin1984.robinPrimePowerIndicator n m t : Complex)) (Ioi x) :=
      (Robin1984.integrableOn_robinPrimePowerIndicator
        hnOne hx m).ofReal
    apply integral_mono_ae hLeft.norm hRight.norm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_quadraticCharacterPrimePowerIndicator_le
      D (lt_trans hx ht)
  next => exact hMajor

theorem tsum_quadraticCharacterPrimePowerIndicators
    (D : NumberField.OddFundamentalDiscriminant)
    (n : Nat) {t : Real} (ht : 0 <= t) :
    tsum (fun m : Nat => quadraticCharacterPrimePowerIndicator D n m t) =
      characterChebyshevSum (Nat.floor t) D.character *
        (Robin1984.robinRealWeight n t : Complex) := by
  have hSupport : forall m : Nat,
      Not (Membership.mem (Finset.Icc 1 (Nat.floor t)) m) ->
        quadraticCharacterPrimePowerIndicator D n m t = 0 := by
    intro m hm
    by_cases hmT : (m : Real) <= t
    next =>
      have hmFloor : m <= Nat.floor t := (Nat.le_floor_iff ht).mpr hmT
      have hmZero : m = 0 := by
        by_contra hmNe
        exact hm (Finset.mem_Icc.mpr
          (And.intro (Nat.one_le_iff_ne_zero.mpr hmNe) hmFloor))
      subst m
      simp [quadraticCharacterPrimePowerIndicator, twistedMangoldtSequence]
    next =>
      unfold quadraticCharacterPrimePowerIndicator
      rw [Set.indicator_of_notMem (s := Ici (m : Real)) hmT]
  rw [tsum_eq_sum hSupport]
  unfold characterChebyshevSum
  unfold BombieriVinogradov.VaughanMeanValue.psiCharacterSum
  calc
    Finset.sum (Finset.Icc 1 (Nat.floor t))
        (fun m : Nat => quadraticCharacterPrimePowerIndicator D n m t) =
      Finset.sum (Finset.Icc 1 (Nat.floor t)) (fun m : Nat =>
        twistedMangoldtSequence D.character m *
          (Robin1984.robinRealWeight n t : Complex)) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmT : (m : Real) <= t :=
          (Nat.le_floor_iff ht).mp (Finset.mem_Icc.mp hm).2
        unfold quadraticCharacterPrimePowerIndicator
        rw [Set.indicator_of_mem (s := Ici (m : Real)) hmT]
    _ = (Finset.sum (Finset.Icc 1 (Nat.floor t))
          (fun m : Nat => twistedMangoldtSequence D.character m)) *
        (Robin1984.robinRealWeight n t : Complex) := by
      rw [Finset.sum_mul]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      unfold twistedMangoldtSequence
      rw [mul_comm]

theorem quadraticCharacterPrimePowerSum_eq_weightedIntegral
    (D : NumberField.OddFundamentalDiscriminant)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    tsum (fun m : Nat => twistedMangoldtSequence D.character m *
        Robin1984.robinCutoffMellinTest n x (m : Real)) =
      (quadraticCharacterWeightedIntegral D n x : Complex) := by
  have hnOne : 1 <= n := by omega
  have hF : forall m : Nat, IntegrableOn
      (quadraticCharacterPrimePowerIndicator D n m) (Ioi x) := by
    intro m
    exact integrableOn_quadraticCharacterPrimePowerIndicator
      D hnOne hx m
  calc
    tsum (fun m : Nat => twistedMangoldtSequence D.character m *
        Robin1984.robinCutoffMellinTest n x (m : Real)) =
      tsum (fun m : Nat => integral (volume.restrict (Ioi x))
        (quadraticCharacterPrimePowerIndicator D n m)) := by
          apply tsum_congr
          intro m
          exact (integral_quadraticCharacterPrimePowerIndicator
            D hnOne hx m).symm
    _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
        tsum (fun m : Nat =>
          quadraticCharacterPrimePowerIndicator D n m t)) :=
      integral_tsum_of_summable_integral_norm hF
        (summable_integral_norm_quadraticCharacterPrimePowerIndicators
          D hn hx)
    _ = (quadraticCharacterWeightedIntegral D n x : Complex) := by
      rw [quadraticCharacterWeightedIntegral, <- integral_complex_ofReal]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [tsum_quadraticCharacterPrimePowerIndicators D n
        (le_of_lt (lt_trans (lt_trans Real.zero_lt_one hx) ht))]
      unfold quadraticCharacterChebyshevStep
      apply Complex.ext
      next => simp
      next =>
        simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
          mul_zero]
        rw [quadraticCharacterChebyshevSum_im]
        simp

end

end RobinBV.NumberField
