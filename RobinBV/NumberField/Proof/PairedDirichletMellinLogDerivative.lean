import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Expansion
import Mathlib.NumberTheory.LSeries.SumCoeff
import RobinBV.NumberField.Proof.PairedDirichletMellinContinuation

/-!
# Exact logarithmic derivatives and the paired Chebyshev Mellin transform

The ordinary L-series and Chebyshev step are identified on Re(s)>1.
All finite cutoffs and compact corrections are kept explicit.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set Filter Asymptotics

noncomputable section

theorem sum_twistedMangoldtSequence_eq_characterChebyshevSum
    {N : Nat} (chi : DirichletCharacter Complex N) (n : Nat) :
    (Finset.Icc 1 n).sum (twistedMangoldtSequence chi) = characterChebyshevSum n chi := by
  unfold characterChebyshevSum BombieriVinogradov.VaughanMeanValue.psiCharacterSum
  apply Finset.sum_congr rfl
  intro m hm
  exact mul_comm _ _

theorem twistedMangoldtPartialSums_isBigO
    {N : Nat} (chi : DirichletCharacter Complex N) :
    IsBigO atTop (fun n : Nat => (Finset.Icc 1 n).sum (twistedMangoldtSequence chi))
      (fun n : Nat => (n : Real) ^ (1 : Real)) := by
  apply IsBigO.of_bound (Real.log 4 + 4)
  apply Filter.Eventually.of_forall
  intro n
  rw [sum_twistedMangoldtSequence_eq_characterChebyshevSum,
    Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  exact (norm_characterChebyshevSum_le_psi chi n).trans
    (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n))

/-- The complete complex character Mellin identity; real-valuedness is not
required and no cancellation estimate beyond Chebyshev's bound is used. -/
theorem neg_logDeriv_LFunction_eq_characterChebyshevMellin
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {s : Complex} (hs : 1 < s.re) :
    -logDeriv chi.LFunction s =
      s * integral (volume.restrict (Ioi (1 : Real))) (fun t : Real =>
        characterChebyshevSum (Nat.floor t) chi * (t : Complex) ^ (-s - 1)) := by
  have hS : LSeriesSummable (twistedMangoldtSequence chi) s := by
    have hSequence : twistedMangoldtSequence chi =
        (fun n : Nat => chi n) * (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) := by
      funext n
      rfl
    rw [hSequence]
    exact chi.LSeriesSummable_twist_vonMangoldt hs
  have hAbel := LSeries_eq_mul_integral (twistedMangoldtSequence chi)
    (r := (1 : Real)) (by norm_num) hs hS (twistedMangoldtPartialSums_isBigO chi)
  rw [neg_logDeriv_LFunction_eq_LSeries chi hs, hAbel]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [sum_twistedMangoldtSequence_eq_characterChebyshevSum]
  congr 2
  ring

theorem integrableOn_characterChebyshevMellin
    {N : Nat} (chi : DirichletCharacter Complex N)
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn (fun t : Real =>
      characterChebyshevSum (Nat.floor t) chi * (t : Complex) ^ (-s - 1)) (Ioi 1) := by
  have hBase := (integrableOn_Ioi_rpow_of_lt
    (by linarith : -s.re < -1) (by norm_num : (0 : Real) < 1)).const_mul (Real.log 4 + 4)
  have hStep : Measurable (fun t : Real => characterChebyshevSum (Nat.floor t) chi) :=
    (measurable_of_countable (fun n : Nat => characterChebyshevSum n chi)).comp Nat.measurable_floor
  have hPower : Measurable (fun t : Real => (t : Complex) ^ (-s - 1)) := by fun_prop
  apply hBase.mono' (hStep.mul hPower).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htPos : 0 < t := lt_trans zero_lt_one ht
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htPos]
  have hStepBound : norm (characterChebyshevSum (Nat.floor t) chi) <=
      (Real.log 4 + 4) * t := by
    calc
      _ <= Chebyshev.psi (Nat.floor t) := norm_characterChebyshevSum_le_psi chi _
      _ = Chebyshev.psi t := (Chebyshev.psi_eq_psi_coe_floor t).symm
      _ <= _ := Chebyshev.psi_le_const_mul_self htPos.le
  calc
    _ <= ((Real.log 4 + 4) * t) * t ^ (-s - 1).re :=
      mul_le_mul_of_nonneg_right hStepBound (Real.rpow_nonneg htPos.le _)
    _ = (Real.log 4 + 4) * t ^ (-s.re) := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      rw [show -s.re = 1 + (-s.re - 1) by ring, Real.rpow_add htPos, Real.rpow_one]
      ring

end

end RobinBV.NumberField
