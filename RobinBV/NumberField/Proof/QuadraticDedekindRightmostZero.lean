import Robin1984.NicolasLandau.XiZeroConstant
import RobinBV.NumberField.Proof.QuadraticDedekindZetaZeros

/-!
# Rightmost quadratic Dedekind zeros

The entire quadratic Dedekind zero carrier has exactly the critical-strip
zeros of the continued quadratic Dedekind zeta. Compactness therefore selects
a rightmost zero on the horizontal line through any zero strictly to the right
of the critical line. The proof includes a possible real exceptional zero.
-/

namespace RobinBV.NumberField

open Complex
open Set

noncomputable section

theorem quadraticDedekindZeroCarrier_ne_zero_of_one_le_re
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 <= s.re) :
    Not (quadraticDedekindZeroCarrier D s = 0) := by
  intro hCarrier
  rcases (quadraticDedekindZeroCarrier_eq_zero_iff D s).1 hCarrier with
    hXi | hCompleted
  next =>
    by_cases hOne : s = 1
    next =>
      subst s
      rw [Robin1984.riemannXi_one_eq_half] at hXi
      norm_num at hXi
    next =>
      have hZero : Not (s = 0) := by
        intro hEq
        subst s
        norm_num at hs
      have hZeta : riemannZeta s = 0 :=
        Robin1984.riemannZeta_eq_zero_of_riemannXi_eq_zero
          hZero hOne hXi
      exact (riemannZeta_ne_zero_of_one_le_re hs) hZeta
  next =>
    have hsPos : 0 < s.re := lt_of_lt_of_le zero_lt_one hs
    have hL : D.character.LFunction s = 0 :=
      (symmetricCompletedLFunction_eq_zero_iff_LFunction_eq_zero_of_re_pos
        D hsPos).1 hCompleted
    exact (D.character.LFunction_ne_zero_of_one_le_re
      (Or.inl (quadraticCharacter_ne_one D)) hs) hL

theorem exists_rightmost_horizontal_quadraticDedekindZeta_zero
    (D : NumberField.OddFundamentalDiscriminant)
    {rho : Complex}
    (hZero : quadraticDedekindZetaContinuation D rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re)
    (hOne : rho.re < 1) :
    Exists fun rhoMax : Complex =>
      And (quadraticDedekindZetaContinuation D rhoMax = 0)
        (And ((1 / 2 : Real) < rhoMax.re)
          (And (rhoMax.re < 1)
            (And (rhoMax.im = rho.im)
              (forall v : Real, 0 < v ->
                Not (quadraticDedekindZetaContinuation D
                  (rhoMax + (v : Complex)) = 0))))) := by
  let linePoint : Real -> Complex := fun r : Real =>
    (r : Complex) + (rho.im : Complex) * Complex.I
  let S : Set Real := Set.inter (Icc rho.re 1)
    {r : Real | quadraticDedekindZeroCarrier D (linePoint r) = 0}
  have hLineContinuous : Continuous linePoint := by
    dsimp [linePoint]
    fun_prop
  have hCarrierContinuous : Continuous
      (fun r : Real => quadraticDedekindZeroCarrier D (linePoint r)) :=
    (differentiable_quadraticDedekindZeroCarrier D).continuous.comp
      hLineContinuous
  have hZeroClosed : IsClosed
      {r : Real | quadraticDedekindZeroCarrier D (linePoint r) = 0} :=
    isClosed_eq hCarrierContinuous continuous_const
  have hCompact : IsCompact S := by
    dsimp [S]
    exact isCompact_Icc.inter_right hZeroClosed
  have hRhoLine : linePoint rho.re = rho := by
    dsimp [linePoint]
    apply Complex.ext
    next => simp
    next => simp
  have hRhoPos : 0 < rho.re := by linarith
  have hCarrierRho : quadraticDedekindZeroCarrier D rho = 0 :=
    (quadraticDedekindZeroCarrier_eq_zero_iff_continuation_eq_zero
      D hRhoPos hOne).2 hZero
  have hNonempty : S.Nonempty := by
    refine Exists.intro rho.re ?_
    dsimp [S]
    refine And.intro (And.intro le_rfl hOne.le) ?_
    change quadraticDedekindZeroCarrier D (linePoint rho.re) = 0
    rw [hRhoLine]
    exact hCarrierRho
  choose rMax hrMax using hCompact.exists_isGreatest hNonempty
  let rhoMax : Complex := linePoint rMax
  have hrMem : Membership.mem S rMax := hrMax.1
  have hrBounds : Membership.mem (Icc rho.re 1) rMax := hrMem.1
  have hrCarrier : quadraticDedekindZeroCarrier D rhoMax = 0 := hrMem.2
  have hMaxIm : rhoMax.im = rho.im := by
    dsimp [rhoMax, linePoint]
    simp
  have hMaxRe : rhoMax.re = rMax := by
    dsimp [rhoMax, linePoint]
    simp
  have hMaxLtOne : rhoMax.re < 1 := by
    rw [hMaxRe]
    apply lt_of_le_of_ne hrBounds.2
    intro hrEq
    have hReOne : 1 <= rhoMax.re := by rw [hMaxRe, hrEq]
    exact (quadraticDedekindZeroCarrier_ne_zero_of_one_le_re D hReOne)
      hrCarrier
  have hMaxHalf : (1 / 2 : Real) < rhoMax.re := by
    rw [hMaxRe]
    exact hHalf.trans_le hrBounds.1
  have hMaxPos : 0 < rhoMax.re := by linarith
  have hMaxZero : quadraticDedekindZetaContinuation D rhoMax = 0 :=
    (quadraticDedekindZeroCarrier_eq_zero_iff_continuation_eq_zero
      D hMaxPos hMaxLtOne).1 hrCarrier
  refine Exists.intro rhoMax (And.intro hMaxZero
    (And.intro hMaxHalf (And.intro hMaxLtOne
      (And.intro hMaxIm ?_))))
  intro v hv
  by_cases hRight : 1 <= (rhoMax + (v : Complex)).re
  next =>
    intro hShiftZero
    unfold quadraticDedekindZetaContinuation at hShiftZero
    have hZeta : Not (riemannZeta (rhoMax + (v : Complex)) = 0) :=
      riemannZeta_ne_zero_of_one_le_re hRight
    have hL : Not (D.character.LFunction
        (rhoMax + (v : Complex)) = 0) :=
      D.character.LFunction_ne_zero_of_one_le_re
        (Or.inl (quadraticCharacter_ne_one D)) hRight
    exact (mul_ne_zero hZeta hL) hShiftZero
  next =>
    intro hShiftZero
    have hShiftLtOne : (rhoMax + (v : Complex)).re < 1 :=
      lt_of_not_ge hRight
    have hShiftPos : 0 < (rhoMax + (v : Complex)).re := by
      rw [Complex.add_re, Complex.ofReal_re]
      linarith
    have hShiftCarrier : quadraticDedekindZeroCarrier D
        (rhoMax + (v : Complex)) = 0 :=
      (quadraticDedekindZeroCarrier_eq_zero_iff_continuation_eq_zero
        D hShiftPos hShiftLtOne).2 hShiftZero
    have hShiftLine : linePoint (rMax + v) =
        rhoMax + (v : Complex) := by
      dsimp [linePoint, rhoMax]
      push_cast
      ring
    have hShiftRe : (rhoMax + (v : Complex)).re = rMax + v := by
      rw [Complex.add_re, Complex.ofReal_re, hMaxRe]
    have hShiftMem : Membership.mem S (rMax + v) := by
      dsimp [S]
      refine And.intro ?_ ?_
      next =>
        constructor
        next => linarith [hrBounds.1]
        next =>
          rw [hShiftRe] at hShiftLtOne
          exact hShiftLtOne.le
      next =>
        change quadraticDedekindZeroCarrier D (linePoint (rMax + v)) = 0
        rw [hShiftLine]
        exact hShiftCarrier
    have hMaximal : rMax + v <= rMax := hrMax.2 hShiftMem
    linarith

end

end RobinBV.NumberField
