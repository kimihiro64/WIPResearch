import RobinBV.NumberField.Definitions.IdealNicolasTransfer
import RobinBV.NumberField.Proof.QuadraticIdealTowerReserveBounds

/-!
# Quadratic ideal Chebyshev gap and height loss

The ideal Chebyshev difference is the sum of the repeated prime-power layers.
In a quadratic field, norm-fiber multiplicity bounds this difference by
`2 * (floor(sqrt B) + 1) * log B`. A general two-stage logarithm inequality
then bounds the ideal-lcm height loss by the Chebyshev gap divided by
`theta * log theta`.
-/

namespace RobinBV.NumberField

noncomputable section

/-- The repeated prime-power height contributed by one selected prime ideal. -/
def idealPrimePowerHeightGapTerm
    {K : Type*} [Field K] [NumberField K]
    (B : Nat) (P : Ideal (NumberField.RingOfIntegers K)) : Real :=
  ((Nat.log (Ideal.absNorm P) B : Real) - 1) *
    Real.log (Ideal.absNorm P : Real)

/-- Exact decomposition of `psi_K - theta_K` into local repeated-power
contributions. -/
theorem idealChebyshevPsi_sub_theta_eq_sum_gapTerm
    (K : Type*) [Field K] [NumberField K] (B : Nat) :
    idealChebyshevPsi K B - idealChebyshevTheta K B =
      (primeIdealsUpToNorm K B).sum
        (fun P => idealPrimePowerHeightGapTerm B P) := by
  unfold idealChebyshevPsi idealChebyshevTheta
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro P _hP
  unfold idealPrimePowerHeightGapTerm
  ring

/-- Every local repeated-power height is nonnegative. -/
theorem idealPrimePowerHeightGapTerm_nonneg
    {K : Type*} [Field K] [NumberField K]
    {B : Nat} {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (primeIdealsUpToNorm K B) P) :
    0 <= idealPrimePowerHeightGapTerm B P := by
  have hq := one_lt_absNorm_of_mem_primeIdealsUpToNorm K hP
  have hqB := absNorm_le_of_mem_primeIdealsUpToNorm K hP
  have hLogNat : 1 <= Nat.log (Ideal.absNorm P) B :=
    Nat.log_pos hq hqB
  have hLogReal : (1 : Real) <= Nat.log (Ideal.absNorm P) B := by
    exact_mod_cast hLogNat
  have hLogNorm : 0 <= Real.log (Ideal.absNorm P : Real) := by
    apply Real.log_nonneg
    exact_mod_cast hq.le
  unfold idealPrimePowerHeightGapTerm
  positivity

/-- A local repeated-power height is at most the logarithm of the packet
frontier. -/
theorem idealPrimePowerHeightGapTerm_le_log_frontier
    {K : Type*} [Field K] [NumberField K]
    {B : Nat} {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (primeIdealsUpToNorm K B) P) :
    idealPrimePowerHeightGapTerm B P <= Real.log (B : Real) := by
  let q := Ideal.absNorm P
  let e := Nat.log q B
  have hq := one_lt_absNorm_of_mem_primeIdealsUpToNorm K hP
  have hqB := absNorm_le_of_mem_primeIdealsUpToNorm K hP
  have hBPos : Not (B = 0) := Nat.ne_of_gt
    (lt_of_lt_of_le (Nat.zero_lt_one.trans hq) hqB)
  have hPowNat : q ^ e <= B := Nat.pow_log_le_self q hBPos
  have hPowReal : (q : Real) ^ e <= (B : Real) := by
    exact_mod_cast hPowNat
  have hqRealPos : (0 : Real) < q := by exact_mod_cast (Nat.zero_lt_one.trans hq)
  have hLogPow := Real.log_le_log (pow_pos hqRealPos e) hPowReal
  rw [Real.log_pow] at hLogPow
  have hLogNorm : 0 <= Real.log (q : Real) :=
    Real.log_nonneg (by exact_mod_cast hq.le)
  unfold idealPrimePowerHeightGapTerm
  change ((e : Real) - 1) * Real.log (q : Real) <= Real.log (B : Real)
  nlinarith

/-- A selected prime ideal of norm above the square-root frontier contributes
no repeated prime-power height. -/
theorem idealPrimePowerHeightGapTerm_eq_zero_of_sqrt_lt
    {K : Type*} [Field K] [NumberField K]
    {B : Nat} {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (primeIdealsUpToNorm K B) P)
    (hSqrt : Nat.sqrt B < Ideal.absNorm P) :
    idealPrimePowerHeightGapTerm B P = 0 := by
  have hq := one_lt_absNorm_of_mem_primeIdealsUpToNorm K hP
  have hqB := absNorm_le_of_mem_primeIdealsUpToNorm K hP
  have hBqq : B < Ideal.absNorm P * Ideal.absNorm P :=
    (Nat.sqrt_lt).mp hSqrt
  have hLogOne : Nat.log (Ideal.absNorm P) B = 1 :=
    Nat.log_eq_one_iff'.2 (And.intro hqB hBqq)
  unfold idealPrimePowerHeightGapTerm
  rw [hLogOne]
  norm_num

/-- The prime-ideal theta height never exceeds the full prime-power psi
height. -/
theorem idealChebyshevTheta_le_psi
    (K : Type*) [Field K] [NumberField K] (B : Nat) :
    idealChebyshevTheta K B <= idealChebyshevPsi K B := by
  have hSum : 0 <= (primeIdealsUpToNorm K B).sum
      (fun P => idealPrimePowerHeightGapTerm B P) := by
    apply Finset.sum_nonneg
    intro P hP
    exact idealPrimePowerHeightGapTerm_nonneg hP
  rw [<- idealChebyshevPsi_sub_theta_eq_sum_gapTerm] at hSum
  linarith

/-- Removing two nested logarithms costs at most `(x-y)/(y*log y)` when
`1 < y <= x`. -/
theorem log_log_sub_le_sub_div_mul_log
    {x y : Real} (hy : 1 < y) (hyx : y <= x) :
    Real.log (Real.log x) - Real.log (Real.log y) <=
      (x - y) / (y * Real.log y) := by
  have hyPos : 0 < y := zero_lt_one.trans hy
  have hxPos : 0 < x := hyPos.trans_le hyx
  have hLogYPos : 0 < Real.log y := Real.log_pos hy
  have hLogXPos : 0 < Real.log x := Real.log_pos (hy.trans_le hyx)
  have hOuterRaw := Real.log_le_sub_one_of_pos
    (div_pos hLogXPos hLogYPos)
  have hOuter :
      Real.log (Real.log x) - Real.log (Real.log y) <=
        (Real.log x - Real.log y) / Real.log y := by
    calc
      Real.log (Real.log x) - Real.log (Real.log y) =
          Real.log (Real.log x / Real.log y) := by
        rw [Real.log_div hLogXPos.ne' hLogYPos.ne']
      _ <= Real.log x / Real.log y - 1 := hOuterRaw
      _ = (Real.log x - Real.log y) / Real.log y := by
        field_simp
  have hInnerRaw := Real.log_le_sub_one_of_pos (div_pos hxPos hyPos)
  have hInner :
      Real.log x - Real.log y <= (x - y) / y := by
    calc
      Real.log x - Real.log y = Real.log (x / y) := by
        rw [Real.log_div hxPos.ne' hyPos.ne']
      _ <= x / y - 1 := hInnerRaw
      _ = (x - y) / y := by
        field_simp
  have hDivide :
      (Real.log x - Real.log y) / Real.log y <=
        ((x - y) / y) / Real.log y := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hInner (inv_nonneg.mpr hLogYPos.le)
  calc
    Real.log (Real.log x) - Real.log (Real.log y) <=
        (Real.log x - Real.log y) / Real.log y := hOuter
    _ <= ((x - y) / y) / Real.log y := hDivide
    _ = (x - y) / (y * Real.log y) := by
      field_simp

/-- The nonlinear ideal-lcm height loss is bounded by the normalized
prime-power gap. -/
theorem idealLcmHeightLoss_le_gap_div_theta_mul_log
    (K : Type*) [Field K] [NumberField K] {B : Nat}
    (hTheta : 1 < idealChebyshevTheta K B) :
    idealLcmHeightLoss K B <=
      (idealChebyshevPsi K B - idealChebyshevTheta K B) /
        (idealChebyshevTheta K B *
          Real.log (idealChebyshevTheta K B)) := by
  unfold idealLcmHeightLoss
  exact log_log_sub_le_sub_div_mul_log hTheta
    (idealChebyshevTheta_le_psi K B)

/-- In a quadratic field the complete ideal Chebyshev gap is at most
`2 * (floor(sqrt B) + 1) * log B`. -/
theorem quadraticIdealChebyshevPsi_sub_theta_le
    (D : NumberField.OddFundamentalDiscriminant) {B : Nat}
    (hB : 0 < B) :
    idealChebyshevPsi D.QuadraticField B -
        idealChebyshevTheta D.QuadraticField B <=
      ((2 * (Nat.sqrt B + 1) : Nat) : Real) * Real.log (B : Real) := by
  classical
  let S := primeIdealsUpToNorm D.QuadraticField B
  let low := S.filter (fun P => Ideal.absNorm P <= Nat.sqrt B)
  let high := S.filter (fun P => Not (Ideal.absNorm P <= Nat.sqrt B))
  let f := fun P : Ideal
      (NumberField.RingOfIntegers D.QuadraticField) =>
    idealPrimePowerHeightGapTerm B P
  have hPartition : S.sum f = low.sum f + high.sum f := by
    unfold low high
    rw [Finset.sum_filter_add_sum_filter_not]
  have hLow : low.sum f <= (low.card : Real) * Real.log (B : Real) := by
    calc
      low.sum f <= low.sum (fun _P => Real.log (B : Real)) := by
        apply Finset.sum_le_sum
        intro P hP
        exact idealPrimePowerHeightGapTerm_le_log_frontier
          (Finset.mem_filter.mp hP).1
      _ = (low.card : Real) * Real.log (B : Real) := by simp
  have hHigh : high.sum f = 0 := by
    apply Finset.sum_eq_zero
    intro P hP
    have hParts := Finset.mem_filter.mp hP
    apply idealPrimePowerHeightGapTerm_eq_zero_of_sqrt_lt hParts.1
    omega
  have hCardNat := quadraticPrimeIdealsLowNorm_card_le D B (Nat.sqrt B)
  have hCardReal : (low.card : Real) <=
      ((2 * (Nat.sqrt B + 1) : Nat) : Real) := by
    exact_mod_cast hCardNat
  have hLogB : 0 <= Real.log (B : Real) := by
    apply Real.log_nonneg
    exact_mod_cast hB
  rw [idealChebyshevPsi_sub_theta_eq_sum_gapTerm]
  change S.sum f <=
    ((2 * (Nat.sqrt B + 1) : Nat) : Real) * Real.log (B : Real)
  rw [hPartition, hHigh, add_zero]
  exact hLow.trans (mul_le_mul_of_nonneg_right hCardReal hLogB)

/-- The quadratic ideal-lcm height loss is reduced to an explicit
square-root numerator and the prime-ideal theta denominator. -/
theorem quadraticIdealLcmHeightLoss_le_sqrt_envelope
    (D : NumberField.OddFundamentalDiscriminant) {B : Nat}
    (hB : 0 < B)
    (hTheta : 1 < idealChebyshevTheta D.QuadraticField B) :
    idealLcmHeightLoss D.QuadraticField B <=
      (((2 * (Nat.sqrt B + 1) : Nat) : Real) * Real.log (B : Real)) /
        (idealChebyshevTheta D.QuadraticField B *
          Real.log (idealChebyshevTheta D.QuadraticField B)) := by
  have hGap := quadraticIdealChebyshevPsi_sub_theta_le D hB
  have hDenPos : 0 < idealChebyshevTheta D.QuadraticField B *
      Real.log (idealChebyshevTheta D.QuadraticField B) :=
    mul_pos (zero_lt_one.trans hTheta) (Real.log_pos hTheta)
  exact (idealLcmHeightLoss_le_gap_div_theta_mul_log
      D.QuadraticField hTheta).trans
    (by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hGap (inv_nonneg.mpr hDenPos.le))

end

end RobinBV.NumberField
