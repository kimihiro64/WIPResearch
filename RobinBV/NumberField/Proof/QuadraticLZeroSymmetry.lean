import RobinBV.NumberField.Definitions.QuadraticLZeros

/-!
# Zero symmetry for primitive quadratic Dirichlet L-functions

Primitive Gauss sums and root numbers are proved nonzero directly from Fourier
inversion.  The completed functional equation therefore reflects zeros across
the critical line.  In particular, failure of the associated ERH predicate
produces a critical-strip zero strictly to the right of one half.
-/

namespace RobinBV.NumberField

open DirichletCharacter

noncomputable section

variable {N : Nat} [NeZero N]

theorem gaussSum_stdAddChar_ne_zero_of_isPrimitive
    {chi : DirichletCharacter Complex N} (hchi : IsPrimitive chi) :
    Not (gaussSum chi ZMod.stdAddChar = 0) := by
  intro hGauss
  have hDft :
      ZMod.dft (N := N) (E := Complex) (chi : ZMod N -> Complex) = 0 := by
    funext k
    rw [hchi.fourierTransform_eq_inv_mul_gaussSum, hGauss, mul_zero]
    rfl
  have hChi : (chi : ZMod N -> Complex) = 0 :=
    (ZMod.dft (N := N) (E := Complex)).injective (by
      simpa only [map_zero] using hDft)
  have hAtOne := congrFun hChi 1
  change chi 1 = 0 at hAtOne
  rw [map_one] at hAtOne
  exact one_ne_zero hAtOne

theorem rootNumber_ne_zero_of_isPrimitive
    {chi : DirichletCharacter Complex N} (hchi : IsPrimitive chi) :
    Not (rootNumber chi = 0) := by
  unfold rootNumber
  apply div_ne_zero
  next =>
    apply div_ne_zero
    next => exact gaussSum_stdAddChar_ne_zero_of_isPrimitive hchi
    next => exact pow_ne_zero _ Complex.I_ne_zero
  next =>
    exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))

theorem completedLFunction_one_sub_eq_zero_iff
    {chi : DirichletCharacter Complex N} (hchi : IsPrimitive chi)
    (s : Complex) :
    completedLFunction chi (1 - s) = 0 <->
      completedLFunction (Inv.inv chi) s = 0 := by
  rw [hchi.completedLFunction_one_sub]
  have hNpow : Not ((N : Complex) ^ (s - 1 / 2) = 0) :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  have hRoot := rootNumber_ne_zero_of_isPrimitive hchi
  have hCoeff : Not (((N : Complex) ^ (s - 1 / 2) * rootNumber chi) = 0) :=
    mul_ne_zero hNpow hRoot
  constructor
  next =>
    intro hProduct
    rcases mul_eq_zero.mp hProduct with hCoeffZero | hL
    next => exact False.elim (hCoeff hCoeffZero)
    next => exact hL
  next =>
    intro hL
    rw [hL, mul_zero]

theorem completedLFunction_one_sub_eq_zero_iff_of_isQuadratic
    {chi : DirichletCharacter Complex N} (hchi : IsPrimitive chi)
    (hquad : MulChar.IsQuadratic chi) (s : Complex) :
    completedLFunction chi (1 - s) = 0 <->
      completedLFunction chi s = 0 := by
  simpa [hquad.inv] using completedLFunction_one_sub_eq_zero_iff hchi s

theorem isNontrivialCompletedLZero_one_sub_iff_of_isQuadratic
    {chi : DirichletCharacter Complex N} (hchi : IsPrimitive chi)
    (hquad : MulChar.IsQuadratic chi) (rho : Complex) :
    IsNontrivialCompletedLZero chi (1 - rho) <->
      IsNontrivialCompletedLZero chi rho := by
  unfold IsNontrivialCompletedLZero
  rw [completedLFunction_one_sub_eq_zero_iff_of_isQuadratic hchi hquad]
  constructor
  next =>
    intro h
    apply And.intro h.1
    apply And.intro
    next =>
      have hLt := h.2.2
      simp only [Complex.sub_re, Complex.one_re] at hLt
      linarith
    next =>
      have hPos := h.2.1
      simp only [Complex.sub_re, Complex.one_re] at hPos
      linarith
  next =>
    intro h
    apply And.intro h.1
    apply And.intro
    next =>
      simp only [Complex.sub_re, Complex.one_re]
      linarith [h.2.2]
    next =>
      simp only [Complex.sub_re, Complex.one_re]
      linarith [h.2.1]

/-- Failure of ERH for a primitive quadratic character supplies a nontrivial
zero strictly to the right of the critical line. -/
theorem exists_nontrivialCompletedLZero_re_gt_half_of_not_dirichletERH
    {chi : DirichletCharacter Complex N} (hchi : IsPrimitive chi)
    (hquad : MulChar.IsQuadratic chi) (hNotERH : Not (DirichletERH chi)) :
    Exists fun rho : Complex =>
      And (IsNontrivialCompletedLZero chi rho) (1 / 2 < rho.re) := by
  unfold DirichletERH at hNotERH
  push Not at hNotERH
  choose rho hZero hOffLine using hNotERH
  by_cases hRight : 1 / 2 < rho.re
  next => exact Exists.intro rho (And.intro hZero hRight)
  next =>
    have hLeft : rho.re < 1 / 2 := by
      exact lt_of_le_of_ne (le_of_not_gt hRight) hOffLine
    have hReflected :=
      (isNontrivialCompletedLZero_one_sub_iff_of_isQuadratic
        hchi hquad rho).2 hZero
    apply Exists.intro (1 - rho)
    apply And.intro hReflected
    simp only [Complex.sub_re, Complex.one_re]
    linarith

end

end RobinBV.NumberField
