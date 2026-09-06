import RobinBV.NumberField.Proof.MovingCharacterBoundarySecondMoment

/-!
# Quantitative principal-character boundary sharpness

Actual xi mass positivity, complete canonical second moments and the full
sampled-mean excursion theorem force arbitrarily late norm fluctuations.
No numerical zero, simple-zero, or independence assumption is used.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter
open scoped Classical

noncomputable section

/-- The full principal root second moment is strictly positive under RH. -/
theorem principalCharacter_rootZeroSecondMoment_re_pos
    (N : Nat) [NeZero N] (hRH : RiemannHypothesis) {k : Nat} (hk : 2 <= k) :
    0 < (rootCharacterZeroSecondMoment (1 : DirichletCharacter Complex N) k).re := by
  let : Nonempty RiemannXiDivisorZeroIndex :=
    nonempty_riemannXiDivisorZeroIndex_of_riemannHypothesis hRH
  let c : Complex -> Complex := fun z => (k : Complex)/(z*((k : Complex)-z))
  have hkR : (1 : Real) < k := by exact_mod_cast (by omega : 1 < k)
  have hRe := Robin1984.riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH
  have hZ := Robin1984.summable_robinXiZeroWeight
  have hC : Summable (fun p : RiemannXiDivisorZeroIndex => norm (c (riemannXiDivisorZeroValue p))) := by
    simpa only [c, Complex.ofReal_natCast] using
      (Complex.summable_real_div_mul_sub_of_re_eq_half riemannXiDivisorZeroValue hRe hZ hkR.le).norm
  have hDiag : 0 < tsum (fun p : RiemannXiDivisorZeroIndex => norm (c (riemannXiDivisorZeroValue p))^2) := by
    simpa only [c, Complex.ofReal_natCast] using
      Complex.tsum_norm_real_div_mul_sub_sq_pos_of_re_eq_half riemannXiDivisorZeroValue hRe hZ hkR
  have hMass : (rootCharacterZeroSecondMoment (1 : DirichletCharacter Complex N) k).re =
      tsum (fun p : RiemannXiDivisorZeroIndex => norm (c (riemannXiDivisorZeroValue p))^2) +
        Complex.pointRepeatMass riemannXiDivisorZeroValue c := by
    simp only [rootCharacterZeroSecondMoment, ite_true]
    change (tsum (fun p : Prod RiemannXiDivisorZeroIndex RiemannXiDivisorZeroIndex =>
      if riemannXiDivisorZeroValue p.1=riemannXiDivisorZeroValue p.2 then
        c (riemannXiDivisorZeroValue p.1)*star (c (riemannXiDivisorZeroValue p.2)) else 0)).re = _
    rw [Complex.tsum_equalPoint_mul_star_eq_mass riemannXiDivisorZeroValue c,
      Complex.ofReal_re, Complex.pointCollisionMass_eq_diagonal_add_repeat riemannXiDivisorZeroValue c hC]
  rw [hMass]
  exact add_pos_of_pos_of_nonneg hDiag (Complex.pointRepeatMass_nonneg riemannXiDivisorZeroValue c)

/-- The actual principal arithmetic second-moment scale, with all zero
multiplicities retained in its canonical root mass. -/
def principalBoundarySecondMoment (N : Nat) [NeZero N] (m : Nat) : Real :=
  (rootCharacterZeroSecondMoment (1 : DirichletCharacter Complex N) (m+1)).re/(m : Real)^2

private theorem principalBoundarySecondMoment_re_eq (N : Nat) [NeZero N] (m : Nat) :
    (rootCharacterZeroSecondMoment (1 : DirichletCharacter Complex N) (m+1)/(m : Complex)^2).re =
      principalBoundarySecondMoment N m := by
  unfold principalBoundarySecondMoment
  rw [show (m : Complex)^2=(((m : Real)^2 : Real) : Complex) by norm_cast,
    Complex.div_ofReal_re]

/-- Strictly positive actual boundary second moment for every m>=1. -/
theorem principalBoundarySecondMoment_pos (N : Nat) [NeZero N]
    (hRH : RiemannHypothesis) {m : Nat} (hm : 1 <= m) :
    0 < principalBoundarySecondMoment N m := by
  unfold principalBoundarySecondMoment
  apply div_pos (principalCharacter_rootZeroSecondMoment_re_pos N hRH (by omega : 2 <= m+1))
  exact pow_pos (by exact_mod_cast (by omega : 0 < m)) 2

/-- Every amplitude whose square is below the actual second moment is
exceeded in norm at arbitrarily late integer cutoffs. -/
theorem principalCharacter_boundary_frequently_norm_gt
    (N : Nat) [NeZero N] (hRH : RiemannHypothesis) (m : Nat) (hm : 1 <= m)
    (d : Real) (hd : 0 <= d) (hSmall : d^2 < principalBoundarySecondMoment N m) :
    forall P0 : Nat, exists P : Nat, And (P0 <= P)
      (d < norm (centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m P)) := by
  have hERH : DirichletERH (1 : DirichletCharacter Complex N) :=
    (dirichletERH_principal_iff_riemannHypothesis (N := N)).2 hRH
  have hPowers : forall j : Nat, m+1 <= j -> j < 2*(m+1) ->
      DirichletERH ((1 : DirichletCharacter Complex N)^j) := by
    intro j _ _
    simpa only [one_pow] using hERH
  have hMean := centeredCharacter_boundary_secondMoment_tendsto
    (1 : DirichletCharacter Complex N) m hm hPowers
  simp only [one_pow] at hMean
  have hNormSmall : d^2 <
      norm (rootCharacterZeroSecondMoment (1 : DirichletCharacter Complex N) (m+1)/(m : Complex)^2) := by
    have hReSmall : d^2 <
        (rootCharacterZeroSecondMoment (1 : DirichletCharacter Complex N) (m+1)/(m : Complex)^2).re := by
      rw [principalBoundarySecondMoment_re_eq]
      exact hSmall
    exact hReSmall.trans_le (Complex.re_le_norm _)
  exact Filter.frequently_atTop.mp (Complex.frequently_norm_gt_of_secondMoment_limit
    (centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m) d hd hMean hNormSmall)

/-- A proved positive amplitude works at arbitrarily late cutoffs for
every principal character and every positive root-layer index. -/
theorem principalCharacter_boundary_exists_positive_amplitude
    (N : Nat) [NeZero N] (hRH : RiemannHypothesis) (m : Nat) (hm : 1 <= m) :
    exists d : Real, And (0 < d) (forall P0 : Nat, exists P : Nat, And (P0 <= P)
      (d < norm (centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m P))) := by
  have hV := principalBoundarySecondMoment_pos N hRH hm
  let d : Real := Real.sqrt (principalBoundarySecondMoment N m)/2
  have hd : 0 < d := div_pos (Real.sqrt_pos.mpr hV) (by norm_num)
  have hSmall : d^2 < principalBoundarySecondMoment N m := by
    dsimp only [d]
    nlinarith [Real.sq_sqrt hV.le]
  exact Exists.intro d (And.intro hd
    (principalCharacter_boundary_frequently_norm_gt N hRH m hm d hd.le hSmall))

/-- The actual normalized principal boundary residual is not little-o of
one under RH; the previously identified arithmetic error scale is genuine. -/
theorem principalCharacter_boundary_not_tendsto_zero
    (N : Nat) [NeZero N] (hRH : RiemannHypothesis) (m : Nat) (hm : 1 <= m) :
    Not (Tendsto (centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m)
      atTop (nhds (0 : Complex))) := by
  intro hZero
  have hSquare : Tendsto (fun P : Nat =>
      centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m P *
        star (centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m P))
      atTop (nhds (0 : Complex)) := by
    simpa only [star_zero, mul_zero] using hZero.mul hZero.star
  have hMeanZero := Complex.tendsto_intervalMean_nat_floor_exp _ hSquare
  have hERH : DirichletERH (1 : DirichletCharacter Complex N) :=
    (dirichletERH_principal_iff_riemannHypothesis (N := N)).2 hRH
  have hPowers : forall j : Nat, m+1 <= j -> j < 2*(m+1) ->
      DirichletERH ((1 : DirichletCharacter Complex N)^j) := by
    intro j _ _
    simpa only [one_pow] using hERH
  have hMean := centeredCharacter_boundary_secondMoment_tendsto
    (1 : DirichletCharacter Complex N) m hm hPowers
  simp only [one_pow] at hMean
  have hEq := tendsto_nhds_unique hMean hMeanZero
  have hPos := principalBoundarySecondMoment_pos N hRH hm
  rw [<- principalBoundarySecondMoment_re_eq N m, hEq, Complex.zero_re] at hPos
  exact (lt_irrefl (0 : Real)) hPos

end

end RobinBV.NumberField
