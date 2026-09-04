import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.CriticalStripZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.ASCIIExpansion
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.RetainedZeroRightGap
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroNormInvSqSummable

/-!
# Zero-free damping of a primitive character's truncated zero sum

The retained-zero gap supplies an exponent strictly below one. The finite
sum of reciprocal norms is bounded using the summable inverse-square mass;
all zero multiplicities are preserved. This is the first estimate needed
for fixed-character Chebyshev decay at the Nicolas endpoint.

The BV interfaces are reviewed at commit
310dcff4efc8109814e6cbeab093465262d5d1c5 (Apache-2.0).
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz

theorem retained_zero_re_le_uniform_gap
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hN : 3 <= N) (hchi : Ne chi 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {c : Real} (hc : 0 < c) (hData : ExplicitFormulaZeroFreeData c chi)
    {e : Option Complex} (hChoice : IsExceptionalZeroChoice c chi e)
    {T : Real} {p : SymmetricCompletedZeroIndex chi}
    (hp : Membership.mem (retainedCriticalZeroIndices chi T e) p) :
    (symmetricCompletedZeroValue p).re <=
      1 - c / (Real.log N + Real.log (T + 2)) := by
  have hMem := mem_retainedCriticalZeroIndices_iff.mp hp
  have hStrip := mem_criticalStripZeroTruncation_iff.mp hMem.1
  change And (0 < (symmetricCompletedZeroValue p).re)
    (And ((symmetricCompletedZeroValue p).re < 1)
      (abs (symmetricCompletedZeroValue p).im < T)) at hStrip
  have hZero : chi.LFunction (symmetricCompletedZeroValue p) = 0 :=
    LFunction_eq_zero_of_mem_criticalStripZeroTruncation hchi hPrimitive hMem.1
  have hGap := retainedLFunctionZero_gap_from_one hc hN
    hData.regularGap hData.realUnique hChoice hZero hStrip.1 hStrip.2.1 hMem.2
  have hLogN : 0 < Real.log (N : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hHeight : 0 <= Real.log (abs (symmetricCompletedZeroValue p).im + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg (symmetricCompletedZeroValue p).im]
  have hLogMono : Real.log (abs (symmetricCompletedZeroValue p).im + 2) <=
      Real.log (T + 2) :=
    Real.log_le_log (by positivity) (by linarith [hStrip.2.2])
  have hDelta := div_le_div_of_nonneg_left hc.le
    (show 0 < Real.log (N : Real) +
      Real.log (abs (symmetricCompletedZeroValue p).im + 2) by linarith)
    (show Real.log (N : Real) + Real.log (abs (symmetricCompletedZeroValue p).im + 2) <=
      Real.log (N : Real) + Real.log (T + 2) by linarith)
  linarith

theorem retained_zero_reciprocal_le_mass_term
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {e : Option Complex} {p : SymmetricCompletedZeroIndex chi}
    (hp : Membership.mem (retainedCriticalZeroIndices chi T e) p) :
    1 / norm (symmetricCompletedZeroValue p) <=
      (T + 1) * (1 / norm (symmetricCompletedZeroValue p)) ^ 2 := by
  have hMem := mem_retainedCriticalZeroIndices_iff.mp hp
  have hStrip := mem_criticalStripZeroTruncation_iff.mp hMem.1
  let rho := symmetricCompletedZeroValue p
  change And (0 < rho.re) (And (rho.re < 1) (abs rho.im < T)) at hStrip
  have hNormPos : 0 < norm rho := by
    apply norm_pos_iff.mpr
    intro hZero
    have hRe := hStrip.1
    rw [hZero] at hRe
    norm_num at hRe
  have hNormBound : norm rho <= T + 1 := by
    calc
      norm rho <= abs rho.re + abs rho.im := Complex.norm_le_abs_re_add_abs_im rho
      _ <= T + 1 := by rw [abs_of_pos hStrip.1]; linarith [hStrip.2.1, hStrip.2.2]
  change 1 / norm rho <= (T + 1) * (1 / norm rho) ^ 2
  calc
    1 / norm rho = norm rho * (1 / norm rho) ^ 2 := by
      field_simp [hNormPos.ne']
    _ <= (T + 1) * (1 / norm rho) ^ 2 :=
      mul_le_mul_of_nonneg_right hNormBound (sq_nonneg _)

theorem norm_truncatedCriticalZeroSum_le_zeroFree_mass
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hN : 3 <= N) (hchi : Ne chi 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {c : Real} (hc : 0 < c) (hData : ExplicitFormulaZeroFreeData c chi)
    {e : Option Complex} (hChoice : IsExceptionalZeroChoice c chi e)
    (hx : 1 <= x) {T : Real} (hT : 0 <= T) :
    norm (truncatedCriticalZeroSum chi x T e) <=
      (x : Real) ^ (1 - c / (Real.log N + Real.log (T + 2))) *
        ((T + 1) * tsum (fun p : SymmetricCompletedZeroIndex chi =>
          (1 / norm (symmetricCompletedZeroValue p)) ^ 2)) := by
  let A : Real := (x : Real) ^ (1 - c / (Real.log N + Real.log (T + 2)))
  let w : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    (1 / norm (symmetricCompletedZeroValue p)) ^ 2
  let S := retainedCriticalZeroIndices chi T e
  have hxReal : (1 : Real) <= (x : Real) := by exact_mod_cast hx
  have hxPos : 0 < (x : Real) := lt_of_lt_of_le zero_lt_one hxReal
  have hAPos : 0 <= A := Real.rpow_nonneg hxPos.le _
  have hTerm : forall p, Membership.mem S p ->
      norm ((x : Complex) ^ symmetricCompletedZeroValue p / symmetricCompletedZeroValue p) <=
        A * ((T + 1) * w p) := by
    intro p hp
    have hRe := retained_zero_re_le_uniform_gap hN hchi hPrimitive hc hData hChoice hp
    have hPow : norm ((x : Complex) ^ symmetricCompletedZeroValue p) <= A := by
      rw [<- Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
      exact Real.rpow_le_rpow_of_exponent_le hxReal hRe
    calc
      norm ((x : Complex) ^ symmetricCompletedZeroValue p / symmetricCompletedZeroValue p) =
          norm ((x : Complex) ^ symmetricCompletedZeroValue p) *
            (1 / norm (symmetricCompletedZeroValue p)) := by rw [norm_div]; ring
      _ <= A * (1 / norm (symmetricCompletedZeroValue p)) :=
        mul_le_mul_of_nonneg_right hPow (by positivity)
      _ <= A * ((T + 1) * w p) :=
        mul_le_mul_of_nonneg_left (retained_zero_reciprocal_le_mass_term hp) hAPos
  have hSummable : Summable w := summable_completedZero_norm_inv_sq hchi hPrimitive
  have hFinite : S.sum w <= tsum w :=
    hSummable.sum_le_tsum S (fun p _ => sq_nonneg _)
  rw [truncatedCriticalZeroSum_eq_sum_symmetricCompletedZeroValue]
  calc
    norm (S.sum (fun p => (x : Complex) ^ symmetricCompletedZeroValue p /
      symmetricCompletedZeroValue p)) <=
        S.sum (fun p => norm ((x : Complex) ^ symmetricCompletedZeroValue p /
          symmetricCompletedZeroValue p)) := norm_sum_le _ _
    _ <= S.sum (fun p => A * ((T + 1) * w p)) := Finset.sum_le_sum hTerm
    _ = A * ((T + 1) * S.sum w) := by rw [Finset.mul_sum, Finset.mul_sum]
    _ <= A * ((T + 1) * tsum w) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hFinite (by linarith)) hAPos

end RobinBV.NumberField
