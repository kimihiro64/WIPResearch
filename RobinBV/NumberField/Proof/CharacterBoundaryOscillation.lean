import RobinBV.Mathlib.Analysis.SpecificLimits.IntervalMeanOscillation
import RobinBV.NumberField.Proof.ResonantBoundaryUniversality

/-!
# Signed fluctuations of the actual arithmetic boundary

First establish realness and boundedness directly for the arithmetic
objects, retaining every finite moment and conductor correction.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set
open BombieriVinogradov.SiegelWalfisz
open scoped Classical

noncomputable section

/-- The principal centered integral is real at every cutoff. This uses
the exact complete conductor correction, with no integral splitting. -/
theorem principalCenteredWeightedIntegral_im_eq_zero
    (N : Nat) [NeZero N] (x : Real) :
    (principalCenteredWeightedIntegral N x).im = 0 := by
  let f : Real -> Real := fun t => (Chebyshev.psi t -
    Finset.sum N.primeFactors (fun p =>
      Real.log p * (Nat.log p (Nat.floor t) : Real)) - t) * Robin1984.robinRealWeight 1 t
  have hCheb (t : Real) :
      characterChebyshevSum (Nat.floor t) (1 : DirichletCharacter Complex N) =
        ((Chebyshev.psi t - Finset.sum N.primeFactors (fun p =>
          Real.log p * (Nat.log p (Nat.floor t) : Real)) : Real) : Complex) := by
    have h := principalChebyshevStep_sub_primitive_eq_logFloorSum (N := N) t
    rw [characterChebyshevSum_primitive_principal_eq_psi] at h
    rw [Complex.ofReal_sub]
    linear_combination h
  have hFunction :
      (fun t : Real => (characterChebyshevSum (Nat.floor t)
        (1 : DirichletCharacter Complex N) - (t : Complex)) *
          (Robin1984.robinRealWeight 1 t : Complex)) = (fun t => (f t : Complex)) := by
    funext t
    rw [hCheb]
    simp only [f, Complex.ofReal_mul, Complex.ofReal_sub]
  unfold principalCenteredWeightedIntegral
  rw [hFunction, integral_complex_ofReal]
  rfl

/-- The complete normalized principal boundary residual is real, including
its exact finite prime moments and all earlier principal root models. -/
theorem principalCharacter_boundary_im_eq_zero
    (N : Nat) [NeZero N] (m P : Nat) :
    (centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m P).im = 0 := by
  let : NeZero (Nat.lcm N (primorial P)) :=
    NeZero.mk (Nat.lcm_ne_zero (NeZero.ne N) (primorial_ne_zero P))
  have hChange : (1 : DirichletCharacter Complex N).changeLevel
      (Nat.dvd_lcm_left N (primorial P)) = 1 :=
    (DirichletCharacter.changeLevel_eq_one_iff _).2 rfl
  have hInt (M : Nat) [NeZero M] (x : Real) :
      (starRingEnd Complex) (centeredCharacterWeightedIntegral
        (1 : DirichletCharacter Complex M) x) =
          centeredCharacterWeightedIntegral (1 : DirichletCharacter Complex M) x := by
    apply Complex.conj_eq_iff_im.2
    rw [centeredCharacterWeightedIntegral_principal]
    exact principalCenteredWeightedIntegral_im_eq_zero M x
  have hValue (p : Nat) :
      (starRingEnd Complex) ((1 : DirichletCharacter Complex N) (p : ZMod N)) =
        (1 : DirichletCharacter Complex N) (p : ZMod N) := by
    by_cases hp : IsUnit (p : ZMod N)
    next => rw [MulChar.one_apply hp, map_one]
    next => rw [MulChar.map_nonunit _ hp, map_zero]
  apply Complex.conj_eq_iff_im.1
  unfold centeredCharacterBoundaryResidual
  rw [hChange]
  simp only [one_pow, if_true, one_mul, div_eq_mul_inv, map_mul, map_add, map_sub,
    map_sum, map_pow, Complex.conj_inv, Complex.conj_ofReal, map_natCast, hInt, hValue]

/-- Actual boundary residual boundedness follows from its complete zero
expansion and the proved full zero-series bound, with no new hypothesis. -/
theorem exists_centeredCharacterBoundaryResidual_norm_bound
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    exists B : Real, And (0 <= B) (Filter.Eventually (fun P : Nat =>
      norm (centeredCharacterBoundaryResidual chi m P) <= B) atTop) := by
  choose C hC using exists_boundaryCharacterZeroSeries_norm_bound chi m hm
    (hPowersERH (m+1) le_rfl (by omega))
  have hError : Tendsto (fun P : Nat => centeredCharacterBoundaryResidual chi m P -
      boundaryCharacterZeroSeries chi m P) atTop (nhds (0 : Complex)) := by
    simpa only [centeredCharacterBoundaryResidual] using
      centeredCharacter_boundary_zero_expansion_of_ERH chi m hm hPowersERH
  have hSmall := Metric.tendsto_nhds.mp hError 1 (by norm_num)
  simp only [dist_zero_right] at hSmall
  refine Exists.intro (abs C+1) (And.intro (by positivity) ?_)
  filter_upwards [hC, hSmall] with P hCP hSP
  calc
    norm (centeredCharacterBoundaryResidual chi m P) =
        norm ((centeredCharacterBoundaryResidual chi m P-boundaryCharacterZeroSeries chi m P) +
          boundaryCharacterZeroSeries chi m P) := by rw [sub_add_cancel]
    _ <= norm (centeredCharacterBoundaryResidual chi m P-boundaryCharacterZeroSeries chi m P) +
        norm (boundaryCharacterZeroSeries chi m P) := norm_add_le _ _
    _ <= abs C+1 := by linarith [le_abs_self C]

/-- At resonance even a nonreal character has asymptotically real actual
boundary residual, by the proved complete principal-profile universality. -/
theorem resonantCharacter_boundary_im_tendsto_zero
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hResonance : chi^(m+1)=1)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    Tendsto (fun P : Nat => (centeredCharacterBoundaryResidual chi m P).im)
      atTop (nhds (0 : Real)) := by
  have hProfile := resonantCharacter_boundary_sub_principal_tendsto_zero chi m hm hResonance hPowersERH
  have h := (Complex.continuous_im.tendsto (0 : Complex)).comp hProfile
  simpa only [Function.comp_def, Complex.sub_im, principalCharacter_boundary_im_eq_zero,
    sub_zero, Complex.zero_im] using h

/-- The actual boundary has recurrent positive and negative real excursions
at every resonant layer under the finite family of actual powers ERH. -/
theorem resonantCharacter_boundary_signed_oscillation
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (m : Nat) (hm : 1 <= m)
    (hResonance : chi^(m+1)=1)
    (hPowersERH : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j)) :
    exists d : Real, And (0 < d) (forall P0 : Nat, exists Pplus Pminus : Nat,
      And (P0 <= Pplus) (And (P0 <= Pminus)
        (And (d < (centeredCharacterBoundaryResidual chi m Pplus).re)
          ((centeredCharacterBoundaryResidual chi m Pminus).re < -d)))) := by
  have hFirst := hPowersERH (m+1) le_rfl (by omega)
  rw [hResonance] at hFirst
  have hRH := (dirichletERH_principal_iff_riemannHypothesis (N := N)).1 hFirst
  choose B hB using exists_centeredCharacterBoundaryResidual_norm_bound chi m hm hPowersERH
  have hMean := resonantCharacter_boundary_logMean_tendsto_zero chi m hm hResonance hPowersERH
  have hSecond := resonantCharacter_boundary_secondMoment_tendsto chi m hm hResonance hPowersERH
  have hPos : 0 < (rootCharacterZeroSecondMoment (1 : DirichletCharacter Complex N) (m+1)/
      (m : Complex)^2).re := by
    rw [show (m : Complex)^2=(((m : Real)^2 : Real) : Complex) by norm_cast,
      Complex.div_ofReal_re]
    exact principalBoundarySecondMoment_pos N hRH hm
  choose d hd using Complex.exists_signed_excursions_of_zero_mean_secondMoment
    (centeredCharacterBoundaryResidual chi m) B hB.1
    (resonantCharacter_boundary_im_tendsto_zero chi m hm hResonance hPowersERH)
    hB.2 hMean hSecond hPos
  refine Exists.intro d (And.intro hd.1 ?_)
  intro P0
  choose Pplus hPlus using (Filter.frequently_atTop.mp hd.2.1) P0
  choose Pminus hMinus using (Filter.frequently_atTop.mp hd.2.2) P0
  exact Exists.intro Pplus (Exists.intro Pminus
    (And.intro hPlus.1 (And.intro hMinus.1 (And.intro hPlus.2 hMinus.2))))

/-- RH alone gives two signed excursions at arbitrarily late cutoffs for
every principal modulus and every fixed positive boundary-layer index. -/
theorem principalCharacter_boundary_signed_oscillation
    (N : Nat) [NeZero N] (hRH : RiemannHypothesis) (m : Nat) (hm : 1 <= m) :
    exists d : Real, And (0 < d) (forall P0 : Nat, exists Pplus Pminus : Nat,
      And (P0 <= Pplus) (And (P0 <= Pminus)
        (And (d < (centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m Pplus).re)
          ((centeredCharacterBoundaryResidual (1 : DirichletCharacter Complex N) m Pminus).re < -d)))) := by
  have hERH := (dirichletERH_principal_iff_riemannHypothesis (N := N)).2 hRH
  have hPowers : forall j : Nat, m+1 <= j -> j < 2*(m+1) ->
      DirichletERH ((1 : DirichletCharacter Complex N)^j) := by
    intro j _ _
    simpa only [one_pow] using hERH
  exact resonantCharacter_boundary_signed_oscillation (1 : DirichletCharacter Complex N)
    m hm (one_pow _) hPowers

/-- Every complex character has cofinally many fixed layers with recurrent
excursions of both signs under actual full Dirichlet GRH. -/
theorem fullDirichletGRH_resonant_signed_layers_cofinal
    (hGRH : FullDirichletGRH) {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (m0 : Nat) :
    exists m : Nat, And (m0 <= m) (And (1 <= m) (And (chi^(m+1)=1)
      (exists d : Real, And (0 < d) (forall P0 : Nat, exists Pplus Pminus : Nat,
        And (P0 <= Pplus) (And (P0 <= Pminus)
          (And (d < (centeredCharacterBoundaryResidual chi m Pplus).re)
            ((centeredCharacterBoundaryResidual chi m Pminus).re < -d))))))) := by
  choose m hm using fullDirichletGRH_resonant_sharp_layers_cofinal hGRH chi m0
  have hPowers : forall j : Nat, m+1 <= j -> j < 2*(m+1) -> DirichletERH (chi^j) := by
    intro j _ _
    exact hGRH N (chi^j)
  exact Exists.intro m (And.intro hm.1 (And.intro hm.2.1 (And.intro hm.2.2.1
    (resonantCharacter_boundary_signed_oscillation chi m hm.2.1 hm.2.2.1 hPowers))))

end

end RobinBV.NumberField
