import Mathlib.Analysis.Complex.Convex
import RobinBV.Mathlib.Analysis.Complex.LogDerivContinuation
import RobinBV.NumberField.Proof.PairedDirichletMellinCompact

/-!
# The paired critical integral criterion is equivalent to Dirichlet ERH

The actual critical bound constructs a holomorphic continuation of the
ordinary paired L-product logarithmic derivative. Its exact prime-two
correction is retained. Analytic identity and finite-order poles exclude
zeros to the right of the critical line. Primitive dual reflection excludes
zeros on the left, completing the converse without a new analytic hypothesis.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set Filter

noncomputable section

/-- The paired critical bound excludes all ordinary L-product zeros in the
open half-plane to the right of the critical line. -/
theorem pairedDirichletOrdinaryLProduct_ne_zero_of_criticalBound
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hBound : PairedDirichletCriticalBound chi)
    {s : Complex} (hs : (1 / 2 : Real) < s.re) :
    Not (pairedDirichletOrdinaryLProduct chi s = 0) := by
  let U : Set Complex := {z : Complex | (1 / 2 : Real) < z.re}
  have hInv : Not (Inv.inv chi = 1) := by simpa only [inv_eq_one] using hchi
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hConnected : IsPreconnected U :=
    (convex_halfSpace_re_gt (1 / 2 : Real)).isPreconnected
  have hF : AnalyticOnNhd Complex (pairedDirichletOrdinaryLProduct chi) U := by
    intro z hz
    exact ((chi.differentiable_LFunction hchi).analyticAt z).mul
      (((Inv.inv chi).differentiable_LFunction hInv).analyticAt z)
  have hGDiff : DifferentiableOn Complex (pairedDirichletLogDerivContinuation chi) U := by
    intro z hz
    exact (differentiableAt_pairedDirichletLogDerivContinuation hchi hBound hz).differentiableWithinAt
  have hG := hGDiff.analyticOnNhd hOpen
  have hStart : Not (pairedDirichletOrdinaryLProduct chi 2 = 0) :=
    mul_ne_zero
      (chi.LFunction_ne_zero_of_one_le_re (Or.inl hchi) (by norm_num))
      ((Inv.inv chi).LFunction_ne_zero_of_one_le_re (Or.inl hInv) (by norm_num))
  have hSafe : Filter.Eventually (fun z : Complex => (1 : Real) < z.re) (nhds (2 : Complex)) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hEq : EventuallyEq (nhds (2 : Complex))
      (logDeriv (pairedDirichletOrdinaryLProduct chi)) (pairedDirichletLogDerivContinuation chi) := by
    filter_upwards [hSafe] with z hz
    exact (pairedDirichletLogDerivContinuation_eq_logDeriv hchi hBound hz).symm
  exact Complex.apply_ne_zero_of_logDeriv_continuation hF hG hOpen hConnected
    (by norm_num [U] : Membership.mem U (2 : Complex)) hStart hEq hs

/-- The converse uses both factors of the dual pair; it does not assume
that a complex character is real or self-dual. -/
theorem dirichletERH_of_pairedDirichletCriticalBound
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hBound : PairedDirichletCriticalBound chi) :
    DirichletERH chi := by
  intro rho hZero
  have hRhoNe : Not (rho = 0) := by
    intro hEq
    have hPos := hZero.2.1
    rw [hEq] at hPos
    norm_num at hPos
  have hLZero : chi.LFunction rho = 0 := by
    rw [chi.LFunction_eq_completed_div_gammaFactor rho (Or.inl hRhoNe), hZero.1, zero_div]
  have hUpper : rho.re <= (1 / 2 : Real) := by
    apply le_of_not_gt
    intro hRight
    apply pairedDirichletOrdinaryLProduct_ne_zero_of_criticalBound hchi hBound hRight
    unfold pairedDirichletOrdinaryLProduct
    rw [hLZero, zero_mul]
  have hInvPrimitive := BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive
  have hMirrorZero : (Inv.inv chi).completedLFunction (1 - rho) = 0 := by
    rw [hInvPrimitive.completedLFunction_one_sub, inv_inv, hZero.1, mul_zero]
  have hMirrorPos : 0 < (1 - rho).re := by
    change 0 < 1 - rho.re
    linarith [hZero.2.2]
  have hMirrorNe : Not (1 - rho = 0) := by
    intro hEq
    rw [hEq] at hMirrorPos
    norm_num at hMirrorPos
  have hMirrorLZero : (Inv.inv chi).LFunction (1 - rho) = 0 := by
    rw [(Inv.inv chi).LFunction_eq_completed_div_gammaFactor (1 - rho) (Or.inl hMirrorNe),
      hMirrorZero, zero_div]
  have hLower : (1 / 2 : Real) <= rho.re := by
    apply le_of_not_gt
    intro hLeft
    have hRight : (1 / 2 : Real) < (1 - rho).re := by
      change 1 / 2 < 1 - rho.re
      linarith
    apply pairedDirichletOrdinaryLProduct_ne_zero_of_criticalBound hchi hBound hRight
    unfold pairedDirichletOrdinaryLProduct
    rw [hMirrorLZero, mul_zero]
  exact le_antisymm hUpper hLower

/-- For every nonprincipal primitive complex Dirichlet character, the actual
paired critical integral bound with the canonical zero-mass coefficient is
equivalent to the critical-line assertion for its completed L-function. -/
theorem dirichletERH_iff_pairedDirichletCriticalBound
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    DirichletERH chi <-> PairedDirichletCriticalBound chi :=
  Iff.intro (pairedDirichletCriticalBound_of_dirichletERH hchi hPrimitive)
    (dirichletERH_of_pairedDirichletCriticalBound hchi hPrimitive)

end

end RobinBV.NumberField
