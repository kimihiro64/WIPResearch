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

open Asymptotics
open Filter

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

/-- Once ideal theta exceeds one, the ideal-lcm height loss is nonnegative. -/
theorem idealLcmHeightLoss_nonneg_of_one_lt_theta
    (K : Type*) [Field K] [NumberField K] {B : Nat}
    (hTheta : 1 < idealChebyshevTheta K B) :
    0 <= idealLcmHeightLoss K B := by
  unfold idealLcmHeightLoss
  apply sub_nonneg.mpr
  apply Real.log_le_log (Real.log_pos hTheta)
  apply Real.log_le_log (zero_lt_one.trans hTheta)
  exact idealChebyshevTheta_le_psi K B

/-- A half-strength linear lower bound for quadratic ideal theta converts the
height envelope into an explicit critical-scale bound. -/
theorem quadraticIdealLcmHeightLoss_le_sixteen_inv_realSqrt_of_theta
    (D : NumberField.OddFundamentalDiscriminant) {B : Nat}
    (hB : 4 <= B)
    (hThetaLower : (B : Real) / 2 <=
      idealChebyshevTheta D.QuadraticField B) :
    idealLcmHeightLoss D.QuadraticField B <=
      16 * Inv.inv (Real.sqrt (B : Real)) := by
  let m := Nat.sqrt B
  let s := Real.sqrt (B : Real)
  let theta := idealChebyshevTheta D.QuadraticField B
  let L := Real.log (B : Real)
  have hBPosNat : 0 < B := by omega
  have hBPos : (0 : Real) < B := by exact_mod_cast hBPosNat
  have hBFour : (4 : Real) <= B := by exact_mod_cast hB
  have hSPos : 0 < s := by
    unfold s
    exact Real.sqrt_pos.2 hBPos
  have hSSq : s * s = (B : Real) := by
    unfold s
    exact Real.mul_self_sqrt hBPos.le
  have hTwoLeS : (2 : Real) <= s := by
    have hSNonneg := hSPos.le
    nlinarith
  have hMSqNat : m ^ (2 : Nat) <= B := by
    unfold m
    simpa [pow_two] using Nat.sqrt_le B
  have hMSq : (m : Real) ^ (2 : Nat) <= (B : Real) := by
    exact_mod_cast hMSqNat
  have hMLeS : (m : Real) <= s := by
    rw [Real.le_sqrt (by positivity) hBPos.le]
    simpa [m, s] using hMSq
  have hCoeff :
      (((2 * (Nat.sqrt B + 1) : Nat) : Real)) =
        2 * ((m : Real) + 1) := by
    unfold m
    push_cast
    ring
  have hLogBPos : 0 < L := by
    unfold L
    exact Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hNumerator :
      (((2 * (Nat.sqrt B + 1) : Nat) : Real) * L) <=
        4 * s * L := by
    rw [hCoeff]
    apply mul_le_mul_of_nonneg_right
    next => nlinarith
    next => exact hLogBPos.le
  have hSLeHalfB : s <= (B : Real) / 2 := by
    nlinarith
  have hSLeTheta : s <= theta :=
    hSLeHalfB.trans hThetaLower
  have hThetaOne : 1 < theta := by
    have hTwoLeTheta : (2 : Real) <= theta := by
      nlinarith
    linarith
  have hLogThetaLower : L / 2 <= Real.log theta := by
    have hLogSLe := Real.log_le_log hSPos hSLeTheta
    have hLogS : Real.log s = L / 2 := by
      unfold s L
      exact Real.log_sqrt hBPos.le
    rw [hLogS] at hLogSLe
    exact hLogSLe
  have hDenLower :
      ((B : Real) / 2) * (L / 2) <=
        theta * Real.log theta := by
    exact mul_le_mul hThetaLower hLogThetaLower
      (by positivity) (zero_lt_one.trans hThetaOne).le
  have hScaleNonneg : 0 <= 16 * Inv.inv s := by positivity
  have hDenPos : 0 < theta * Real.log theta :=
    mul_pos (zero_lt_one.trans hThetaOne) (Real.log_pos hThetaOne)
  have hLogThetaNe : Ne (Real.log theta) 0 :=
    (Real.log_pos hThetaOne).ne'
  have hIdentity :
      4 * s * L =
        (16 * Inv.inv s) * (((B : Real) / 2) * (L / 2)) := by
    rw [<- hSSq]
    field_simp
    norm_num
  have hFraction :
      (((2 * (Nat.sqrt B + 1) : Nat) : Real) * L) /
          (theta * Real.log theta) <=
        16 * Inv.inv s := by
    have hMul :
        (((2 * (Nat.sqrt B + 1) : Nat) : Real) * L) <=
          (16 * Inv.inv s) * (theta * Real.log theta) := by
      calc
        (((2 * (Nat.sqrt B + 1) : Nat) : Real) * L) <=
            4 * s * L := hNumerator
        _ = (16 * Inv.inv s) * (((B : Real) / 2) * (L / 2)) :=
          hIdentity
        _ <= (16 * Inv.inv s) * (theta * Real.log theta) :=
          mul_le_mul_of_nonneg_left hDenLower hScaleNonneg
    rw [div_eq_mul_inv]
    calc
      (((2 * (Nat.sqrt B + 1) : Nat) : Real) * L) *
          Inv.inv (theta * Real.log theta) <=
        ((16 * Inv.inv s) * (theta * Real.log theta)) *
          Inv.inv (theta * Real.log theta) :=
        mul_le_mul_of_nonneg_right hMul (by positivity)
      _ = 16 * Inv.inv s := by
        field_simp [hSPos.ne', hLogThetaNe]
  have hEnvelope := quadraticIdealLcmHeightLoss_le_sqrt_envelope
    D hBPosNat hThetaOne
  change idealLcmHeightLoss D.QuadraticField B <=
    16 * Inv.inv (Real.sqrt (B : Real))
  change idealLcmHeightLoss D.QuadraticField B <= 16 * Inv.inv s
  exact hEnvelope.trans hFraction

private theorem height_rpow_isLittleO_rpow_atTop_of_lt
    {a b : Real} (hab : a < b) :
    (fun x : Real => x ^ a) =o[(atTop : Filter Real)]
      (fun x : Real => x ^ b) := by
  apply isLittleO_of_tendsto'
  next =>
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    intro hZero
    exact False.elim ((Real.rpow_pos_of_pos hx b).ne' hZero)
  next =>
    have hLimit := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
    exact hLimit.congr' ((eventually_gt_atTop (0 : Real)).mono
      (fun x hx => by
        calc
          x ^ (-(b - a)) = x ^ (a - b) := by
            congr 1
            ring
          _ = x ^ a / x ^ b := Real.rpow_sub hx a b))

/-- Any eventual half-strength prime-ideal theorem makes the quadratic
ideal-lcm height loss little-o below the critical half exponent. -/
theorem quadraticIdealLcmHeightLoss_isLittleO_rpow_of_theta_linear
    (D : NumberField.OddFundamentalDiscriminant) {b : Real}
    (hb : b < (1 : Real) / 2)
    (hThetaLinear : Filter.Eventually
      (fun B : Nat =>
        (B : Real) / 2 <= idealChebyshevTheta D.QuadraticField B)
      atTop) :
    (fun B : Nat => idealLcmHeightLoss D.QuadraticField B) =o[
      (atTop : Filter Nat)]
      (fun B : Nat => (B : Real) ^ (-b)) := by
  have hBigO :
      (fun B : Nat => idealLcmHeightLoss D.QuadraticField B) =O[
        (atTop : Filter Nat)]
        (fun B : Nat => (B : Real) ^ (-((1 : Real) / 2))) := by
    apply IsBigO.of_bound 16
    filter_upwards [hThetaLinear, eventually_ge_atTop 4] with B hTheta hB
    have hThetaOne :
        1 < idealChebyshevTheta D.QuadraticField B := by
      have hCast : (4 : Real) <= B := by exact_mod_cast hB
      linarith
    have hLossNonneg :=
      idealLcmHeightLoss_nonneg_of_one_lt_theta
        D.QuadraticField hThetaOne
    have hLossBound :=
      quadraticIdealLcmHeightLoss_le_sixteen_inv_realSqrt_of_theta
        D hB hTheta
    have hEq :
        Inv.inv (Real.sqrt (B : Real)) =
          (B : Real) ^ (-((1 : Real) / 2)) := by
      have hNonneg : (0 : Real) <= B := by positivity
      simpa [Real.sqrt_eq_rpow] using
        (Real.rpow_neg hNonneg ((1 : Real) / 2)).symm
    rw [Real.norm_of_nonneg hLossNonneg]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    rw [<- hEq]
    exact hLossBound
  have hPowersReal :
      (fun x : Real => x ^ (-((1 : Real) / 2))) =o[
        (atTop : Filter Real)]
        (fun x : Real => x ^ (-b)) :=
    height_rpow_isLittleO_rpow_atTop_of_lt (by linarith)
  have hPowersNat :
      (fun B : Nat => (B : Real) ^ (-((1 : Real) / 2))) =o[
        (atTop : Filter Nat)]
        (fun B : Nat => (B : Real) ^ (-b)) :=
    hPowersReal.comp_tendsto tendsto_natCast_atTop_atTop
  exact hBigO.trans_isLittleO hPowersNat

end

end RobinBV.NumberField
