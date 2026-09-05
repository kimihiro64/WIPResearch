import RobinBV.NumberField.Proof.DirichletCharacterReweight
import RobinBV.NumberField.Proof.PairedDirichletWeightedFormula

/-!
# General character arithmetic reconstruction of Robin's weighted integral

The full complex twisted Mangoldt sum is exchanged with the Nicolas cutoff.
Every prime-power indicator is retained, including its exact boundary. The
norm majorant is the untwisted series, so no self-duality or ERH is needed.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set

noncomputable section

def dirichletCharacterPrimePowerIndicator
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (n m : Nat) (t : Real) : Complex :=
  (Ici (m : Real)).indicator
    (fun u : Real => twistedMangoldtSequence chi m *
      (Robin1984.robinRealWeight n u : Complex)) t

theorem integrableOn_dirichletCharacterPrimePowerIndicator
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    (m : Nat) :
    IntegrableOn (dirichletCharacterPrimePowerIndicator chi n m)
      (Ioi x) := by
  have hWeight : IntegrableOn (fun t : Real =>
      (Robin1984.robinRealWeight n t : Complex)) (Ioi x) :=
    (Robin1984.integrableOn_robinRealWeight hn hx).ofReal
  exact (hWeight.const_mul
    (twistedMangoldtSequence chi m)).indicator measurableSet_Ici

theorem integral_dirichletCharacterPrimePowerIndicator
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    (m : Nat) :
    integral (volume.restrict (Ioi x))
        (dirichletCharacterPrimePowerIndicator chi n m) =
      twistedMangoldtSequence chi m *
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
        (dirichletCharacterPrimePowerIndicator chi n m) =
      twistedMangoldtSequence chi m *
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Robin1984.robinRealWeight n t : Complex)) := by
      unfold dirichletCharacterPrimePowerIndicator
      calc
        integral (volume.restrict (Ioi x))
            ((Ici (m : Real)).indicator (fun u : Real =>
              twistedMangoldtSequence chi m *
                (Robin1984.robinRealWeight n u : Complex))) =
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            twistedMangoldtSequence chi m *
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
        (dirichletCharacterPrimePowerIndicator chi n m) =
      twistedMangoldtSequence chi m *
        integral (volume.restrict (Ioi (m : Real))) (fun t : Real =>
          (Robin1984.robinRealWeight n t : Complex)) := by
      unfold dirichletCharacterPrimePowerIndicator
      rw [setIntegral_indicator measurableSet_Ici]
      change integral (volume.restrict
          (Set.inter (Ioi x) (Ici (m : Real)))) (fun t : Real =>
            twistedMangoldtSequence chi m *
              (Robin1984.robinRealWeight n t : Complex)) = _
      rw [hSet, integral_Ici_eq_integral_Ioi, integral_const_mul]
    rw [hIntegral, hWeightIntegral (m : Real) hmOne]
    simp only [Robin1984.robinCutoffMellinTest, if_neg hm]

theorem norm_dirichletCharacterPrimePowerIndicator_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {n m : Nat} {t : Real} (ht : 1 < t) :
    norm (dirichletCharacterPrimePowerIndicator chi n m t) <=
      norm (Robin1984.robinPrimePowerIndicator n m t : Complex) := by
  unfold dirichletCharacterPrimePowerIndicator
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
      (norm_twistedMangoldtSequence_le_vonMangoldt chi m)
      (Robin1984.robinRealWeight_nonneg ht)
  next =>
    rw [Set.indicator_of_notMem (s := Ici (m : Real)) hm,
      Set.indicator_of_notMem (s := Ici (m : Real)) hm]
    simp

theorem summable_integral_norm_dirichletCharacterPrimePowerIndicators
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    Summable (fun m : Nat => integral (volume.restrict (Ioi x))
      (fun t : Real =>
        norm (dirichletCharacterPrimePowerIndicator chi n m t))) := by
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
        (dirichletCharacterPrimePowerIndicator chi n m) (Ioi x) :=
      integrableOn_dirichletCharacterPrimePowerIndicator
        chi hnOne hx m
    have hRight : IntegrableOn (fun t : Real =>
        (Robin1984.robinPrimePowerIndicator n m t : Complex)) (Ioi x) :=
      (Robin1984.integrableOn_robinPrimePowerIndicator
        hnOne hx m).ofReal
    apply integral_mono_ae hLeft.norm hRight.norm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_dirichletCharacterPrimePowerIndicator_le
      chi (lt_trans hx ht)
  next => exact hMajor

theorem tsum_dirichletCharacterPrimePowerIndicators
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (n : Nat) {t : Real} (ht : 0 <= t) :
    tsum (fun m : Nat => dirichletCharacterPrimePowerIndicator chi n m t) =
      characterChebyshevSum (Nat.floor t) chi *
        (Robin1984.robinRealWeight n t : Complex) := by
  have hSupport : forall m : Nat,
      Not (Membership.mem (Finset.Icc 1 (Nat.floor t)) m) ->
        dirichletCharacterPrimePowerIndicator chi n m t = 0 := by
    intro m hm
    by_cases hmT : (m : Real) <= t
    next =>
      have hmFloor : m <= Nat.floor t := (Nat.le_floor_iff ht).mpr hmT
      have hmZero : m = 0 := by
        by_contra hmNe
        exact hm (Finset.mem_Icc.mpr
          (And.intro (Nat.one_le_iff_ne_zero.mpr hmNe) hmFloor))
      subst m
      simp [dirichletCharacterPrimePowerIndicator, twistedMangoldtSequence]
    next =>
      unfold dirichletCharacterPrimePowerIndicator
      rw [Set.indicator_of_notMem (s := Ici (m : Real)) hmT]
  rw [tsum_eq_sum hSupport]
  unfold characterChebyshevSum
  unfold BombieriVinogradov.VaughanMeanValue.psiCharacterSum
  calc
    Finset.sum (Finset.Icc 1 (Nat.floor t))
        (fun m : Nat => dirichletCharacterPrimePowerIndicator chi n m t) =
      Finset.sum (Finset.Icc 1 (Nat.floor t)) (fun m : Nat =>
        twistedMangoldtSequence chi m *
          (Robin1984.robinRealWeight n t : Complex)) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmT : (m : Real) <= t :=
          (Nat.le_floor_iff ht).mp (Finset.mem_Icc.mp hm).2
        unfold dirichletCharacterPrimePowerIndicator
        rw [Set.indicator_of_mem (s := Ici (m : Real)) hmT]
    _ = (Finset.sum (Finset.Icc 1 (Nat.floor t))
          (fun m : Nat => twistedMangoldtSequence chi m)) *
        (Robin1984.robinRealWeight n t : Complex) := by
      rw [Finset.sum_mul]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      unfold twistedMangoldtSequence
      rw [mul_comm]

theorem dirichletCharacterPrimePowerSum_eq_weightedIntegral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    tsum (fun m : Nat => twistedMangoldtSequence chi m *
        Robin1984.robinCutoffMellinTest n x (m : Real)) =
      dirichletCharacterWeightedIntegral chi n x := by
  have hnOne : 1 <= n := by omega
  have hF : forall m : Nat, IntegrableOn
      (dirichletCharacterPrimePowerIndicator chi n m) (Ioi x) := by
    intro m
    exact integrableOn_dirichletCharacterPrimePowerIndicator
      chi hnOne hx m
  calc
    tsum (fun m : Nat => twistedMangoldtSequence chi m *
        Robin1984.robinCutoffMellinTest n x (m : Real)) =
      tsum (fun m : Nat => integral (volume.restrict (Ioi x))
        (dirichletCharacterPrimePowerIndicator chi n m)) := by
          apply tsum_congr
          intro m
          exact (integral_dirichletCharacterPrimePowerIndicator
            chi hnOne hx m).symm
    _ = integral (volume.restrict (Ioi x)) (fun t : Real =>
        tsum (fun m : Nat =>
          dirichletCharacterPrimePowerIndicator chi n m t)) :=
      integral_tsum_of_summable_integral_norm hF
        (summable_integral_norm_dirichletCharacterPrimePowerIndicators
          chi hn hx)
    _ = dirichletCharacterWeightedIntegral chi n x := by
      unfold dirichletCharacterWeightedIntegral
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact tsum_dirichletCharacterPrimePowerIndicators chi n
        (le_of_lt (lt_trans (lt_trans Real.zero_lt_one hx) ht))

/-- The arithmetic series used in the primitive explicit formula is exactly
the weighted character integral; the identity itself does not need primitivity. -/
theorem primitiveCharacterPrimePowerSum_eq_weightedIntegral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    primitiveCharacterPrimePowerSum chi n x =
      dirichletCharacterWeightedIntegral chi n x :=
  dirichletCharacterPrimePowerSum_eq_weightedIntegral chi hn hx

end

end RobinBV.NumberField
