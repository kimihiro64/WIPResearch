import RobinBV.NumberField.Proof.PairedDirichletWeightedFormula

/-!
# Complete higher-exponent character remainders

The origin and trivial-zero terms are retained at every integer exponent
n>=2. These estimates supply the higher-weight ERH bounds required to
separate successive root-prime layers without an assumed Chebyshev error.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

/-- Exact complete origin correction at every higher exponent. -/
theorem primitiveCharacterEvenOriginCorrection_eq
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    quadraticCharacterEvenOriginCorrection n x =
      ((x ^ (-(n : Real)) : Real) : Complex) +
        Robin1984.robinCpowLogTail
          ((-(n : Real) : Real) : Complex) 1 x := by
  have hPair :=
    Robin1984.robinCutoffMellin_resolvent_pairing
      (n := n) (by omega : 1 <= n) hx
      (c := (3 / 2 : Real))
      (by norm_num : (0 : Real) < 3 / 2)
      (by
        have hnR : (2 : Real) <= n := by exact_mod_cast hn
        linarith)
      (rho := 0) (by norm_num)
  have hOrigin :
      quadraticCharacterEvenOriginCorrection n x =
        integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
          (u : Complex) ^ (-(1 : Complex)) *
            Robin1984.robinCutoffMellinTest n x u) := by
    unfold quadraticCharacterEvenOriginCorrection
    simpa [sub_zero] using! hPair
  have hInt :=
    Robin1984.integrableOn_robinCutoffMellinTest_power_tail
      (n := n) hx (rho := 0) (by
        have hnR : (2 : Real) <= n := by exact_mod_cast hn
        simpa only [Complex.zero_re] using (show (0 : Real) < n by linarith))
  have hLow :=
    hInt.mono_set (Ioc_subset_Ioi_self :
      Ioc (1 : Real) x <= Ioi 1)
  have hHigh :=
    hInt.mono_set (Ioi_subset_Ioi hx.le)
  have hLowValue :
      integral (volume.restrict (Ioc (1 : Real) x)) (fun u : Real =>
        (u : Complex) ^ (-(1 : Complex)) *
          Robin1984.robinCutoffMellinTest n x u) =
        ((x ^ (-(n : Real)) : Real) : Complex) := by
    calc
      integral (volume.restrict (Ioc (1 : Real) x)) (fun u : Real =>
          (u : Complex) ^ (-(1 : Complex)) *
            Robin1984.robinCutoffMellinTest n x u) =
        integral (volume.restrict (Ioc (1 : Real) x)) (fun u : Real =>
          ((u ^ (-(1 : Real)) *
            (x ^ (-(n : Real)) *
              Inv.inv (Real.log x)) : Real) : Complex)) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro u hu
          have huPos : 0 < u := lt_trans Real.zero_lt_one hu.1
          have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
          simp only [Robin1984.robinCutoffMellinTest,
            if_pos hu.2]
          have huPow :
              (u : Complex) ^ (-(1 : Complex)) =
                ((u ^ (-(1 : Real)) : Real) : Complex) := by
            rw [show (-(1 : Complex)) =
              ((-(1 : Real) : Real) : Complex) by norm_num]
            exact (Complex.ofReal_cpow huPos.le (-(1 : Real))).symm
          have hxPow :
              (x : Complex) ^ (-(n : Complex)) =
                ((x ^ (-(n : Real)) : Real) : Complex) := by
            rw [show (-(n : Complex)) =
              ((-(n : Real) : Real) : Complex) by push_cast; rfl]
            exact (Complex.ofReal_cpow hxPos.le (-(n : Real))).symm
          rw [huPow, hxPow]
          push_cast
          rfl
      _ = ((integral (volume.restrict (Ioc (1 : Real) x))
          (fun u : Real =>
          u ^ (-(1 : Real)) *
            (x ^ (-(n : Real)) *
              Inv.inv (Real.log x))) : Real) : Complex) := by
          rw [integral_complex_ofReal]
      _ = ((integral (volume.restrict (Ioc (1 : Real) x)) (fun u : Real =>
          Inv.inv u *
            (x ^ (-(n : Real)) *
              Inv.inv (Real.log x))) : Real) : Complex) := by
          congr 1
          apply setIntegral_congr_fun measurableSet_Ioc
          intro u hu
          change u ^ (-(1 : Real)) *
            (x ^ (-(n : Real)) * Inv.inv (Real.log x)) =
            Inv.inv u *
              (x ^ (-(n : Real)) * Inv.inv (Real.log x))
          rw [Real.rpow_neg_one]
      _ = (((integral (volume.restrict (Ioc (1 : Real) x))
            (fun u : Real => Inv.inv u)) *
          (x ^ (-(n : Real)) *
            Inv.inv (Real.log x)) : Real) : Complex) := by
            congr 1
            rw [integral_mul_const]
      _ = ((Real.log x *
          (x ^ (-(n : Real)) *
            Inv.inv (Real.log x)) : Real) : Complex) := by
            congr 1
            rw [<- intervalIntegral.integral_of_le hx.le,
              integral_inv_of_pos
                Real.zero_lt_one (lt_trans Real.zero_lt_one hx)]
            simp
      _ = ((x ^ (-(n : Real)) : Real) : Complex) := by
            congr 1
            have hLog : Not (Real.log x = 0) :=
              ne_of_gt (Real.log_pos hx)
            field_simp [hLog]
  have hHighValue :
      integral (volume.restrict (Ioi x)) (fun u : Real =>
        (u : Complex) ^ (-(1 : Complex)) *
          Robin1984.robinCutoffMellinTest n x u) =
        Robin1984.robinCpowLogTail
          ((-(n : Real) : Real) : Complex) 1 x := by
    unfold Robin1984.robinCpowLogTail
    simp only [pow_one]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simpa using!
      Robin1984.robinCutoffMellinIntegrand_eq_upper
        n (0 : Complex) hx hu
  rw [hOrigin, <- Ioc_union_Ioi_eq_Ioi hx.le]
  have hUnion :=
    setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi hLow hHigh
  simp only [zero_sub] at hUnion
  rw [hUnion, hLowValue, hHighValue]

/-- Complete norm bound for the higher-exponent origin term, including
the explicit inverse-exponent logarithmic correction. -/
theorem norm_primitiveCharacterEvenOriginCorrection_le
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    norm (quadraticCharacterEvenOriginCorrection n x) <=
      x ^ (-(n : Real)) + (x ^ (-(n : Real)) / (n : Real)) * Inv.inv (Real.log x) := by
  have hnPos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hTail := Robin1984.norm_robinCpowLogTail_le
    (a := ((-(n : Real) : Real) : Complex)) hx
    (by simpa only [Complex.ofReal_re] using neg_neg_of_pos hnPos) 1
  rw [primitiveCharacterEvenOriginCorrection_eq hn hx]
  calc
    _ <= norm (((x ^ (-(n : Real)) : Real) : Complex)) +
        norm (Robin1984.robinCpowLogTail ((-(n : Real) : Real) : Complex) 1 x) := norm_add_le _ _
    _ <= _ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 <= x) _)]
      exact add_le_add le_rfl (by simpa only [Complex.ofReal_re, pow_one, neg_div_neg_eq] using hTail)

/-- Exact norm of the frozen cutoff test at one, for arbitrary exponent. -/
theorem norm_primitiveCharacterCutoff_one_eq
    (n : Nat) {x : Real} (hx : 1 < x) :
    norm (Robin1984.robinCutoffMellinTest n x 1) =
      x ^ (-(n : Real)) * Inv.inv (Real.log x) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  simp only [Robin1984.robinCutoffMellinTest, if_pos hx.le, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hLogPos)]
  rw [show -(n : Complex) = ((-(n : Real) : Real) : Complex) by norm_num,
    <- Complex.ofReal_cpow hxPos.le, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hxPos.le _)]

/-- The complete negative-even zero family remains explicitly controlled
at every positive integer weight exponent. -/
theorem norm_primitiveCharacterNegativeEvenKernels_le
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    norm (tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n (-(2 * ((k : Complex) + 1))) x /
        (2 * ((k : Complex) + 1)))) <=
      2 * Real.log (2 * Real.pi) * x ^ (-(n : Real)) * Inv.inv (Real.log x) := by
  have hEq := Robin1984.robin_explicit_correction_eq hn hx
  have hCorr := Robin1984.robinTrivialZeroCorrection_bounds hn hx
  have hLogPos : 0 < Real.log (2 * Real.pi) := by
    apply Real.log_pos
    nlinarith [Real.pi_gt_three]
  have hSolve : tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n (-(2 * ((k : Complex) + 1))) x /
        (2 * ((k : Complex) + 1))) =
      (Real.log (2 * Real.pi) : Complex) * Robin1984.robinCutoffMellinTest n x 1 -
        (Robin1984.robinTrivialZeroCorrection n x : Complex) := by linear_combination hEq
  rw [hSolve]
  calc
    _ <= norm ((Real.log (2 * Real.pi) : Complex) * Robin1984.robinCutoffMellinTest n x 1) +
        norm (Robin1984.robinTrivialZeroCorrection n x : Complex) := norm_sub_le _ _
    _ = Real.log (2 * Real.pi) * (x ^ (-(n : Real)) * Inv.inv (Real.log x)) +
        Robin1984.robinTrivialZeroCorrection n x := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLogPos,
        norm_primitiveCharacterCutoff_one_eq n (by linarith), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hCorr.1]
    _ <= Real.log (2 * Real.pi) * (x ^ (-(n : Real)) * Inv.inv (Real.log x)) +
        Real.log (2 * Real.pi) * x ^ (-(n : Real)) * Inv.inv (Real.log x) := add_le_add le_rfl hCorr.2
    _ = _ := by ring

/-- The complete negative-odd zero family has its full higher-exponent
weight bound, without truncation. -/
theorem norm_primitiveCharacterNegativeOddKernels_le
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    norm (tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1))) <= x ^ (-(n : Real)) * Inv.inv (Real.log x) := by
  exact (norm_tsum_quadraticNegativeOddKernels_le hn hx).trans_eq
    (Robin1984.integral_robinRealWeight hn (by linarith))

/-- Complete even-parity remainder at arbitrary higher exponent, keeping
the origin term and its exact inverse-exponent logarithmic coefficient. -/
theorem norm_primitiveCharacterEvenWeightedRemainder_le
    (N : Nat) (B : Complex) {n : Nat} (hn : 2 <= n) {x : Real} (hx : 2 <= x) :
    norm (primitiveCharacterEvenWeightedRemainder N B n x) <=
      x ^ (-(n : Real)) +
        (norm ((Real.log N : Complex) / 2 - B - (Real.log Real.pi : Complex) / 2 -
            (Real.eulerMascheroniConstant : Complex) / 2) +
          2 * Real.log (2 * Real.pi) + Inv.inv (n : Real)) *
          (x ^ (-(n : Real)) * Inv.inv (Real.log x)) := by
  let C : Complex := (Real.log N : Complex) / 2 - B - (Real.log Real.pi : Complex) / 2 -
    (Real.eulerMascheroniConstant : Complex) / 2
  let T : Complex := Robin1984.robinCutoffMellinTest n x 1
  let S : Complex := tsum (fun k : Nat =>
    Robin1984.robinZeroKernel n (-(2 * ((k : Complex) + 1))) x / (2 * ((k : Complex) + 1)))
  let O : Complex := quadraticCharacterEvenOriginCorrection n x
  change norm (C * T + S - O) <= _
  have hT := norm_primitiveCharacterCutoff_one_eq n (by linarith : 1 < x)
  have hS := norm_primitiveCharacterNegativeEvenKernels_le (by omega : 1 <= n) hx
  have hO := norm_primitiveCharacterEvenOriginCorrection_le hn (by linarith : 1 < x)
  calc
    _ <= (norm (C * T) + norm S) + norm O :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (norm C * (x ^ (-(n : Real)) * Inv.inv (Real.log x)) + norm S) + norm O := by
      rw [norm_mul, hT]
    _ <= (norm C * (x ^ (-(n : Real)) * Inv.inv (Real.log x)) +
        2 * Real.log (2 * Real.pi) * x ^ (-(n : Real)) * Inv.inv (Real.log x)) +
        (x ^ (-(n : Real)) + (x ^ (-(n : Real)) / (n : Real)) * Inv.inv (Real.log x)) :=
      add_le_add (add_le_add le_rfl hS) hO
    _ = _ := by dsimp only [C]; ring

/-- Complete odd-parity higher-exponent remainder; unlike the even case
there is no origin term of order x^(-n) without a logarithmic saving. -/
theorem norm_primitiveCharacterOddWeightedRemainder_le
    (N : Nat) (B : Complex) {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    norm (primitiveCharacterOddWeightedRemainder N B n x) <=
      (norm ((Real.log N : Complex) / 2 - B - (Real.log Real.pi : Complex) / 2 -
          (Real.eulerMascheroniConstant : Complex) / 2 + quadraticOddGammaConstant) + 1) *
        (x ^ (-(n : Real)) * Inv.inv (Real.log x)) := by
  let C : Complex := (Real.log N : Complex) / 2 - B - (Real.log Real.pi : Complex) / 2 -
    (Real.eulerMascheroniConstant : Complex) / 2 + quadraticOddGammaConstant
  let T : Complex := Robin1984.robinCutoffMellinTest n x 1
  let S : Complex := tsum (fun k : Nat =>
    Robin1984.robinZeroKernel n (-(2 * (k : Complex) + 1)) x / (2 * (k : Complex) + 1))
  change norm (C * T + S) <= _
  have hT := norm_primitiveCharacterCutoff_one_eq n (by linarith : 1 < x)
  have hS := norm_primitiveCharacterNegativeOddKernels_le hn hx
  calc
    _ <= norm (C * T) + norm S := norm_add_le _ _
    _ = norm C * (x ^ (-(n : Real)) * Inv.inv (Real.log x)) + norm S := by rw [norm_mul, hT]
    _ <= norm C * (x ^ (-(n : Real)) * Inv.inv (Real.log x)) +
        x ^ (-(n : Real)) * Inv.inv (Real.log x) := add_le_add le_rfl hS
    _ = _ := by dsimp only [C]; ring

end

end RobinBV.NumberField
