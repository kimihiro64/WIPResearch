import RobinBV.NumberField.Proof.PairedDirichletMellinLogDerivative

/-!
# The exact finite correction at the cutoff three

Only the prime two contributes to the Chebyshev step between one and three.
The corresponding logarithmic-derivative correction is a finite entire
combination of complex powers, with no hidden singular division by s.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set

noncomputable section

theorem characterChebyshevSum_one_eq_zero
    {N : Nat} (chi : DirichletCharacter Complex N) :
    characterChebyshevSum 1 chi = 0 := by
  simp [characterChebyshevSum, BombieriVinogradov.VaughanMeanValue.psiCharacterSum]

theorem characterChebyshevSum_two_eq_twistedMangoldt
    {N : Nat} (chi : DirichletCharacter Complex N) :
    characterChebyshevSum 2 chi = twistedMangoldtSequence chi 2 := by
  norm_num [characterChebyshevSum, BombieriVinogradov.VaughanMeanValue.psiCharacterSum,
    Finset.sum_Icc_succ_top, twistedMangoldtSequence]
  ring

theorem characterChebyshevMellin_integral_one_two
    {N : Nat} (chi : DirichletCharacter Complex N) (s : Complex) :
    intervalIntegral (fun t : Real =>
      characterChebyshevSum (Nat.floor t) chi * (t : Complex) ^ (-s - 1)) 1 2 volume = 0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : Real) <= 2),
    integral_Ioc_eq_integral_Ioo]
  calc
    _ = integral (volume.restrict (Ioo (1 : Real) 2)) (fun _ : Real => (0 : Complex)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      have hFloor : Nat.floor t = 1 := (Nat.floor_eq_iff (by linarith [ht.1] : 0 <= t)).2
        (And.intro (by norm_num; exact ht.1.le) (by norm_num; exact ht.2))
      dsimp only
      rw [hFloor, characterChebyshevSum_one_eq_zero, zero_mul]
    _ = 0 := by simp

theorem characterChebyshevMellin_integral_two_three
    {N : Nat} (chi : DirichletCharacter Complex N) (s : Complex) :
    intervalIntegral (fun t : Real =>
      characterChebyshevSum (Nat.floor t) chi * (t : Complex) ^ (-s - 1)) 2 3 volume =
      twistedMangoldtSequence chi 2 *
        intervalIntegral (fun t : Real => (t : Complex) ^ (-s - 1)) 2 3 volume := by
  rw [intervalIntegral.integral_of_le (by norm_num : (2 : Real) <= 3),
    intervalIntegral.integral_of_le (by norm_num : (2 : Real) <= 3),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, <- integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hFloor : Nat.floor t = 2 := (Nat.floor_eq_iff (by linarith [ht.1] : 0 <= t)).2
    (And.intro (by norm_num; exact ht.1.le) (by norm_num; exact ht.2))
  dsimp only
  rw [hFloor, characterChebyshevSum_two_eq_twistedMangoldt]

theorem mul_integral_characterChebyshevMellin_one_three
    {N : Nat} (chi : DirichletCharacter Complex N)
    {s : Complex} (hs : 1 < s.re) :
    s * intervalIntegral (fun t : Real =>
      characterChebyshevSum (Nat.floor t) chi * (t : Complex) ^ (-s - 1)) 1 3 volume =
      twistedMangoldtSequence chi 2 * ((2 : Complex) ^ (-s) - (3 : Complex) ^ (-s)) := by
  have hFull := integrableOn_characterChebyshevMellin chi hs
  have hInt12 : IntervalIntegrable (fun t : Real =>
      characterChebyshevSum (Nat.floor t) chi * (t : Complex) ^ (-s - 1)) volume 1 2 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : Real) <= 2)).2
      (hFull.mono_set (fun t ht => ht.1))
  have hInt23 : IntervalIntegrable (fun t : Real =>
      characterChebyshevSum (Nat.floor t) chi * (t : Complex) ^ (-s - 1)) volume 2 3 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (2 : Real) <= 3)).2
      (hFull.mono_set (fun t ht => lt_trans (by norm_num : (1 : Real) < 2) ht.1))
  rw [<- intervalIntegral.integral_add_adjacent_intervals hInt12 hInt23,
    characterChebyshevMellin_integral_one_two,
    characterChebyshevMellin_integral_two_three, zero_add]
  have hsNe : Not (s = 0) := by
    intro hZero
    rw [hZero] at hs
    norm_num at hs
  have hExponent : Not (-s - 1 = (-1 : Complex)) := by
    intro hEq
    apply hsNe
    linear_combination -hEq
  rw [integral_cpow (Or.inr (And.intro hExponent (by norm_num [uIcc_of_le])))]
  simp only [sub_add_cancel]
  field_simp [hsNe]
  norm_num
  ring

theorem logDeriv_LFunction_eq_mellinTail_primeTwo
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {s : Complex} (hs : 1 < s.re) :
    logDeriv chi.LFunction s =
      -s * integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        characterChebyshevSum (Nat.floor t) chi * (t : Complex) ^ (-s - 1)) -
      twistedMangoldtSequence chi 2 * ((2 : Complex) ^ (-s) - (3 : Complex) ^ (-s)) := by
  have hMain := neg_logDeriv_LFunction_eq_characterChebyshevMellin chi hs
  have hSplit := intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_characterChebyshevMellin chi hs) (by norm_num : (1 : Real) <= 3)
  have hCompact := mul_integral_characterChebyshevMellin_one_three chi hs
  rw [<- hSplit] at hCompact
  linear_combination -hMain - hCompact

/-- The ordinary L-product, distinct from the completed zero carrier. -/
def pairedDirichletOrdinaryLProduct
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (s : Complex) : Complex :=
  chi.LFunction s * (Inv.inv chi).LFunction s

def pairedDirichletPrimeTwoCoefficient
    {N : Nat} (chi : DirichletCharacter Complex N) : Complex :=
  twistedMangoldtSequence chi 2 + twistedMangoldtSequence (Inv.inv chi) 2

theorem pairedDirichletPrimeTwoCoefficient_eq
    {N : Nat} (chi : DirichletCharacter Complex N) :
    pairedDirichletPrimeTwoCoefficient chi =
      (Real.log 2 : Complex) * (chi 2 + (Inv.inv chi) 2) := by
  unfold pairedDirichletPrimeTwoCoefficient twistedMangoldtSequence
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num
  ring

/-- Entire finite correction applied to the proved half-plane continuation. -/
def pairedDirichletLogDerivContinuation
    {N : Nat} (chi : DirichletCharacter Complex N) (s : Complex) : Complex :=
  -s * pairedDirichletMellinContinuation chi s -
    pairedDirichletPrimeTwoCoefficient chi * ((2 : Complex) ^ (-s) - (3 : Complex) ^ (-s))

theorem logDeriv_pairedDirichletOrdinaryLProduct_eq_mellinTail
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) {s : Complex} (hs : 1 < s.re) :
    logDeriv (pairedDirichletOrdinaryLProduct chi) s =
      -s * integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        pairedDirichletChebyshevStep chi t * (t : Complex) ^ (-s - 1)) -
        pairedDirichletPrimeTwoCoefficient chi * ((2 : Complex) ^ (-s) - (3 : Complex) ^ (-s)) := by
  have hInv : Not (Inv.inv chi = 1) := by simpa only [inv_eq_one] using hchi
  have hFirst := (integrableOn_characterChebyshevMellin chi hs).mono_set
    (Ioi_subset_Ioi (by norm_num : (1 : Real) <= 3))
  have hSecond := (integrableOn_characterChebyshevMellin (Inv.inv chi) hs).mono_set
    (Ioi_subset_Ioi (by norm_num : (1 : Real) <= 3))
  have hIntegral : integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
      pairedDirichletChebyshevStep chi t * (t : Complex) ^ (-s - 1)) =
      integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        characterChebyshevSum (Nat.floor t) chi * (t : Complex) ^ (-s - 1)) +
      integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        characterChebyshevSum (Nat.floor t) (Inv.inv chi) * (t : Complex) ^ (-s - 1)) := by
    simpa only [pairedDirichletChebyshevStep, add_mul] using integral_add hFirst hSecond
  change logDeriv (fun z : Complex => chi.LFunction z * (Inv.inv chi).LFunction z) s = _
  rw [logDeriv_mul s
      (chi.LFunction_ne_zero_of_one_le_re (Or.inl hchi) hs.le)
      ((Inv.inv chi).LFunction_ne_zero_of_one_le_re (Or.inl hInv) hs.le)
      (chi.differentiable_LFunction hchi s)
      ((Inv.inv chi).differentiable_LFunction hInv s),
    logDeriv_LFunction_eq_mellinTail_primeTwo chi hs,
    logDeriv_LFunction_eq_mellinTail_primeTwo (Inv.inv chi) hs, hIntegral]
  unfold pairedDirichletPrimeTwoCoefficient
  ring

theorem pairedDirichletLogDerivContinuation_eq_logDeriv
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hBound : PairedDirichletCriticalBound chi)
    {s : Complex} (hs : 1 < s.re) :
    pairedDirichletLogDerivContinuation chi s =
      logDeriv (pairedDirichletOrdinaryLProduct chi) s := by
  rw [pairedDirichletLogDerivContinuation,
    pairedDirichletMellinContinuation_eq_mellinTail hchi hBound hs]
  exact (logDeriv_pairedDirichletOrdinaryLProduct_eq_mellinTail hchi hs).symm

theorem differentiableAt_pairedDirichletLogDerivContinuation
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hBound : PairedDirichletCriticalBound chi)
    {s : Complex} (hs : (1 / 2 : Real) < s.re) :
    DifferentiableAt Complex (pairedDirichletLogDerivContinuation chi) s := by
  have hTwo := (hasDerivAt_neg s).const_cpow
    (Or.inl (by norm_num : Not ((2 : Complex) = 0)))
  have hThree := (hasDerivAt_neg s).const_cpow
    (Or.inl (by norm_num : Not ((3 : Complex) = 0)))
  exact ((hasDerivAt_neg s).differentiableAt.mul
    (differentiableAt_pairedDirichletMellinContinuation hchi hBound hs)).sub
      ((hTwo.sub hThree).differentiableAt.const_mul (pairedDirichletPrimeTwoCoefficient chi))

end

end RobinBV.NumberField
