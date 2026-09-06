import RobinBV.NumberField.Proof.DirichletGRHCriterion
import RobinBV.NumberField.Proof.PrincipalBoundarySharpness

/-!
# Universal resonant arithmetic boundary profiles

When the first omitted character power is principal, its entire canonical
zero series agrees with the principal series. Subtracting the actual
proved expansions preserves every finite moment and principal model.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter
open scoped Classical

noncomputable section

/-- Exact shared complete zero series at every resonant layer and cutoff. -/
theorem resonantCharacter_boundary_zeroSeries_eq_principal
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m P : Nat)
    (hResonance : chi^(m+1)=1) :
    boundaryCharacterZeroSeries chi m P =
      boundaryCharacterZeroSeries (1 : DirichletCharacter Complex N) m P := by
  simp only [boundaryCharacterZeroSeries, hResonance, one_pow, if_true]

private theorem riemannHypothesis_of_resonant_powers_ERH
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hResonance : chi^(m+1)=1)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    RiemannHypothesis := by
  have h := hPowersERH (m+1) le_rfl (by omega)
  rw [hResonance] at h
  exact (dirichletERH_principal_iff_riemannHypothesis (N := N)).1 h

/-- The complete actual resonant boundary profile differs from the
principal profile by a vanishing quantity, even for nonreal characters. -/
theorem resonantCharacter_boundary_sub_principal_tendsto_zero
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hResonance : chi^(m+1)=1)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    Tendsto (fun P : Nat => centeredCharacterBoundaryResidual chi m P -
      centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m P)
      atTop (nhds (0 : Complex)) := by
  have hRH := riemannHypothesis_of_resonant_powers_ERH chi m hm hResonance hPowersERH
  have hERHOne := (dirichletERH_principal_iff_riemannHypothesis (N := N)).2 hRH
  have hPowersOne : forall j : Nat, m+1 <= j -> j < 2*(m+1) ->
      DirichletERH ((1 : DirichletCharacter Complex N)^j) := by
    intro j _ _
    simpa only [one_pow] using hERHOne
  have hChiError : Tendsto (fun P : Nat => centeredCharacterBoundaryResidual chi m P -
      boundaryCharacterZeroSeries chi m P) atTop (nhds (0 : Complex)) := by
    simpa only [centeredCharacterBoundaryResidual] using
      centeredCharacter_boundary_zero_expansion_of_ERH chi m hm hPowersERH
  have hOneError : Tendsto (fun P : Nat =>
      centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m P -
        boundaryCharacterZeroSeries (1 : DirichletCharacter Complex N) m P)
      atTop (nhds (0 : Complex)) := by
    simpa only [centeredCharacterBoundaryResidual] using
      centeredCharacter_boundary_zero_expansion_of_ERH (1 : DirichletCharacter Complex N) m hm hPowersOne
  have h := hChiError.sub hOneError
  simp only [sub_zero] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro P
  dsimp only
  rw [resonantCharacter_boundary_zeroSeries_eq_principal chi m P hResonance]
  ring

/-- Every resonant actual arithmetic boundary has zero logarithmic mean,
including nonreal characters; principal xi has no central zero. -/
theorem resonantCharacter_boundary_logMean_tendsto_zero
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hResonance : chi^(m+1)=1)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t)))) atTop (nhds (0 : Complex)) := by
  have h := centeredCharacter_boundary_logMean_tendsto chi m hm hPowersERH
  simpa only [hResonance, rootCharacterCentralMultiplicity_principal_eq_zero,
    Nat.cast_zero, mul_zero] using h

/-- The complete second moment at resonance is the universal principal mass. -/
theorem resonantCharacter_boundary_secondMoment_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hResonance : chi^(m+1)=1)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    Tendsto (Complex.intervalMean (fun t : Real =>
      centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t)) *
        star (centeredCharacterBoundaryResidual chi m (Nat.floor (Real.exp t)))))
      atTop (nhds (rootCharacterZeroSecondMoment (1 : DirichletCharacter Complex N) (m+1)/(m : Complex)^2)) := by
  simpa only [hResonance] using centeredCharacter_boundary_secondMoment_tendsto chi m hm hPowersERH

/-- Universal quantitative norm sharpness at every resonant complex-character layer. -/
theorem resonantCharacter_boundary_frequently_norm_gt
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hResonance : chi^(m+1)=1)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j))
    (d : Real) (hd : 0 <= d) (hSmall : d^2 < principalBoundarySecondMoment N m) :
    forall P0 : Nat, exists P : Nat, And (P0 <= P)
      (d < norm (centeredCharacterBoundaryResidual chi m P)) := by
  have hMean := resonantCharacter_boundary_secondMoment_tendsto chi m hm hResonance hPowersERH
  have hRe : (rootCharacterZeroSecondMoment (1 : DirichletCharacter Complex N) (m+1)/(m : Complex)^2).re =
      principalBoundarySecondMoment N m := by
    unfold principalBoundarySecondMoment
    rw [show (m : Complex)^2=(((m : Real)^2 : Real) : Complex) by norm_cast,
      Complex.div_ofReal_re]
  have hSmallNorm : d^2 <
      norm (rootCharacterZeroSecondMoment (1 : DirichletCharacter Complex N) (m+1)/(m : Complex)^2) :=
    (hSmall.trans_eq hRe.symm).trans_le (Complex.re_le_norm _)
  exact Filter.frequently_atTop.mp (Complex.frequently_norm_gt_of_secondMoment_limit
    (centeredCharacterBoundaryResidual chi m) d hd hMean hSmallNorm)

/-- No resonant complex-character normalized boundary residual can tend
to zero under the stated finite family of actual ERH hypotheses. -/
theorem resonantCharacter_boundary_not_tendsto_zero
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hResonance : chi^(m+1)=1)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    Not (Tendsto (centeredCharacterBoundaryResidual chi m) atTop (nhds (0 : Complex))) := by
  intro hZero
  have hProfile := resonantCharacter_boundary_sub_principal_tendsto_zero chi m hm hResonance hPowersERH
  have h := hZero.sub hProfile
  simp only [sub_zero] at h
  have hOne : Tendsto (centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m)
      atTop (nhds (0 : Complex)) := by
    apply h.congr'
    apply Filter.Eventually.of_forall
    intro P
    dsimp only
    ring
  exact principalCharacter_boundary_not_tendsto_zero N
    (riemannHypothesis_of_resonant_powers_ERH chi m hm hResonance hPowersERH) m hm hOne

/-- A strictly positive amplitude recurs at every resonant fixed layer. -/
theorem resonantCharacter_boundary_exists_positive_amplitude
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hResonance : chi^(m+1)=1)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    exists d : Real, And (0 < d) (forall P0 : Nat, exists P : Nat, And (P0 <= P)
      (d < norm (centeredCharacterBoundaryResidual chi m P))) := by
  have hRH := riemannHypothesis_of_resonant_powers_ERH chi m hm hResonance hPowersERH
  have hV := principalBoundarySecondMoment_pos N hRH hm
  let d : Real := Real.sqrt (principalBoundarySecondMoment N m)/2
  have hd : 0 < d := div_pos (Real.sqrt_pos.mpr hV) (by norm_num)
  have hSmall : d^2 < principalBoundarySecondMoment N m := by
    dsimp only [d]
    nlinarith [Real.sq_sqrt hV.le]
  exact Exists.intro d (And.intro hd
    (resonantCharacter_boundary_frequently_norm_gt chi m hm hResonance hPowersERH d hd.le hSmall))

/-- Full Dirichlet GRH gives cofinally many sharp fixed layers for every
complex character. The layer is chosen before the arbitrary cutoff bound. -/
theorem fullDirichletGRH_resonant_sharp_layers_cofinal
    (hGRH : FullDirichletGRH) {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (m0 : Nat) :
    exists m : Nat, And (m0 <= m) (And (1 <= m) (And (chi^(m+1)=1)
      (exists d : Real, And (0 < d) (forall P0 : Nat, exists P : Nat, And (P0 <= P)
        (d < norm (centeredCharacterBoundaryResidual chi m P)))))) := by
  have hOrder : 0 < orderOf chi := MulChar.orderOf_pos chi
  have hOrderOne : 1 <= orderOf chi := hOrder
  have hLarge : m0+2 <= orderOf chi*(m0+2) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (m0+2) hOrderOne
  let m : Nat := orderOf chi*(m0+2)-1
  have hm : 1 <= m := by dsimp only [m]; omega
  have hm0 : m0 <= m := by dsimp only [m]; omega
  have hAdd : m+1=orderOf chi*(m0+2) := by dsimp only [m]; omega
  have hResonance : chi^(m+1)=1 := by
    rw [hAdd, pow_mul, pow_orderOf_eq_one, one_pow]
  have hPowers : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j) := by
    intro j _ _
    exact hGRH N (chi^j)
  exact Exists.intro m (And.intro hm0 (And.intro hm (And.intro hResonance
    (resonantCharacter_boundary_exists_positive_amplitude chi m hm hResonance hPowers))))

/-- Finite resonant combinations retain exactly their total coefficient
times the principal boundary profile, with a vanishing full remainder. -/
theorem resonantCharacter_boundary_weighted_profile_tendsto_zero
    {N : Nat} [NeZero N] {I : Type*} (s : Finset I)
    (chi : I -> DirichletCharacter Complex N) (c : I -> Complex) (m : Nat) (hm : 1 <= m)
    (hResonance : forall i, Membership.mem s i -> (chi i)^(m+1)=1)
    (hPowersERH : forall i, Membership.mem s i -> forall j : Nat,
      m+1 <= j -> j < 2*(m+1) -> DirichletERH ((chi i)^j)) :
    Tendsto (fun P : Nat => (s.sum fun i => c i * centeredCharacterBoundaryResidual (chi i) m P) -
      (s.sum c) * centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m P)
      atTop (nhds (0 : Complex)) := by
  have hEach : forall i, Membership.mem s i -> Tendsto (fun P : Nat => c i *
      (centeredCharacterBoundaryResidual (chi i) m P -
        centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m P))
      atTop (nhds (0 : Complex)) := by
    intro i hi
    simpa only [mul_zero] using
      (resonantCharacter_boundary_sub_principal_tendsto_zero (chi i) m hm
        (hResonance i hi) (hPowersERH i hi)).const_mul (c i)
  have h := tendsto_finsetSum s hEach
  simpa only [Finset.sum_const_zero, mul_sub, Finset.sum_sub_distrib, <- Finset.sum_mul] using h

/-- Balanced resonant character combinations cancel the entire leading
zeta fluctuation, not merely its logarithmic average. -/
theorem resonantCharacter_boundary_balanced_sum_tendsto_zero
    {N : Nat} [NeZero N] {I : Type*} (s : Finset I)
    (chi : I -> DirichletCharacter Complex N) (c : I -> Complex) (m : Nat) (hm : 1 <= m)
    (hResonance : forall i, Membership.mem s i -> (chi i)^(m+1)=1)
    (hPowersERH : forall i, Membership.mem s i -> forall j : Nat,
      m+1 <= j -> j < 2*(m+1) -> DirichletERH ((chi i)^j))
    (hBalanced : s.sum c=0) :
    Tendsto (fun P : Nat => s.sum fun i => c i * centeredCharacterBoundaryResidual (chi i) m P)
      atTop (nhds (0 : Complex)) := by
  simpa only [hBalanced, zero_mul, sub_zero] using
    resonantCharacter_boundary_weighted_profile_tendsto_zero s chi c m hm hResonance hPowersERH

end

end RobinBV.NumberField
