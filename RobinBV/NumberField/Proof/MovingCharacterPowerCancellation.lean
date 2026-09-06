import RobinBV.NumberField.Proof.MovingCharacterBoundary

/-!
# Unconditional higher comparison after exact character-power cancellation

Common earlier root-prime tails are subtracted before any estimate.
The selected root uses SW only; no RH or ERH is imposed.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter
open scoped Classical

noncomputable section

/-- Equal earlier character powers cancel their complete root tails,
so the selected root scale has its exact SW limit without any ERH. -/
theorem movingCharacter_common_power_rootScale_tendsto
    {N : Nat} [NeZero N] (chi eta : DirichletCharacter Complex N)
    (m L : Nat) (hm : 1 <= m) (hML : m+1 <= L)
    (hPowers : forall j : Nat, m+1 <= j -> j < L -> chi^j=eta^j) :
    Tendsto (fun P : Nat =>
      (((((P : Real)^m)^(1-Inv.inv (L : Real))*Real.log ((P : Real)^m) : Real) : Complex) *
        (movingCharacterCorrection chi P ((P : Real)^m) -
          movingCharacterCorrection eta P ((P : Real)^m) +
          ((Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N)^j))) -
           (Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
            Finset.sum (Finset.Icc 1 m) (fun j => eta (p : ZMod N)^j)))) /
              ((((P : Real)^m : Real) : Complex)*(Real.log ((P : Real)^m) : Complex)))))
      atTop (nhds (-((if chi^L=1 then (1 : Complex) else 0) -
        (if eta^L=1 then (1 : Complex) else 0)) / ((1-Inv.inv (L : Real) : Real) : Complex))) := by
  have hL : 2 <= L := by omega
  have hLPos : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
  have hr0 : 0 < Inv.inv (L : Real) := inv_pos.mpr hLPos
  have hr1 : Inv.inv (L : Real) < 1 := by
    simpa only [Nat.cast_one] using Robin1984.inv_nat_lt_nat_of_two_le
      (n := 1) (k := L) (by norm_num) hL
  have hX : Tendsto (fun P : Nat => (P : Real)^m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < m by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  have hSum (P : Nat) :
      Finset.sum (Finset.Icc (m+1) L) (fun j =>
        rootPrimeCharacterTail (chi^j) (Inv.inv (j : Real)) ((P : Real)^m)) -
      Finset.sum (Finset.Icc (m+1) L) (fun j =>
        rootPrimeCharacterTail (eta^j) (Inv.inv (j : Real)) ((P : Real)^m)) =
        rootPrimeCharacterTail (chi^L) (Inv.inv (L : Real)) ((P : Real)^m) -
          rootPrimeCharacterTail (eta^L) (Inv.inv (L : Real)) ((P : Real)^m) := by
    rw [<- Finset.sum_sub_distrib, <- Finset.sum_Ico_add_eq_sum_Icc hML]
    have hZero : Finset.sum (Finset.Ico (m+1) L) (fun j =>
        rootPrimeCharacterTail (chi^j) (Inv.inv (j : Real)) ((P : Real)^m) -
          rootPrimeCharacterTail (eta^j) (Inv.inv (j : Real)) ((P : Real)^m)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hPowers j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2, sub_self]
    rw [hZero, zero_add]
  have hChiError := movingCharacter_uncapped_layers_error_tendsto chi m L hm hML
  have hEtaError := movingCharacter_uncapped_layers_error_tendsto eta m L hm hML
  have hChiRoot := (rootPrimeCharacterTail_normalized_tendsto (chi^L) hr0 hr1).comp hX
  have hEtaRoot := (rootPrimeCharacterTail_normalized_tendsto (eta^L) hr0 hr1).comp hX
  have h := (hChiError.sub hEtaError).sub (hChiRoot.sub hEtaRoot)
  simp only [sub_self, zero_sub] at h
  have hLimit :
      -((if chi^L=1 then (1 : Complex) else 0)/((1-Inv.inv (L : Real) : Real) : Complex) -
        (if eta^L=1 then (1 : Complex) else 0)/((1-Inv.inv (L : Real) : Real) : Complex)) =
      -((if chi^L=1 then (1 : Complex) else 0) -
        (if eta^L=1 then (1 : Complex) else 0))/((1-Inv.inv (L : Real) : Real) : Complex) := by ring
  rw [hLimit] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro P
  dsimp only [Function.comp_def]
  linear_combination
    (((((P : Real)^m)^(1-Inv.inv (L : Real))*Real.log ((P : Real)^m) : Real) : Complex) * hSum P)

/-- Actual difference of two centered level shifts after retaining the
complete finite prime-moment difference. No root-model term is discarded. -/
def centeredCharacterPrefixDifference {N : Nat} [NeZero N]
    (chi eta : DirichletCharacter Complex N) (m P : Nat) : Complex :=
  let x : Real := (P : Real)^m
  (centeredCharacterWeightedIntegral (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) x -
    centeredCharacterWeightedIntegral chi x) -
  (centeredCharacterWeightedIntegral (eta.changeLevel (Nat.dvd_lcm_left N (primorial P))) x -
    centeredCharacterWeightedIntegral eta x) +
  ((Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
      Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N)^j))) -
    (Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
      Finset.sum (Finset.Icc 1 m) (fun j => eta (p : ZMod N)^j)))) /
        ((x : Complex)*(m : Complex)*(Real.log P : Complex))

/-- Exact sharper actual arithmetic comparison after common powers
cancel. No RH, ERH or strict upper bound on the selected layer is needed. -/
theorem centeredCharacter_common_power_resonance
    {N : Nat} [NeZero N] (chi eta : DirichletCharacter Complex N)
    (m L : Nat) (hm : 1 <= m) (hML : m+1 <= L)
    (hPowers : forall j : Nat, m+1 <= j -> j < L -> chi^j=eta^j) :
    Tendsto (fun P : Nat =>
      ((((P : Real)^((m : Real)*((L : Real)-1)/(L : Real))*Real.log P : Real) : Complex) *
        centeredCharacterPrefixDifference chi eta m P))
      atTop (nhds (-(L : Complex)/((m : Complex)*((L : Complex)-1)) *
        ((if chi^L=1 then (1 : Complex) else 0) - (if eta^L=1 then (1 : Complex) else 0)))) := by
  have hM : Not ((m : Complex)=0) := by exact_mod_cast (show Not (m=0) by omega)
  have hL : Not ((L : Complex)=0) := by exact_mod_cast (show Not (L=0) by omega)
  have hLR : Not ((L : Real)=0) := by exact_mod_cast (show Not (L=0) by omega)
  have hL1 : Not ((L : Complex)-1=0) := by
    intro h
    have : (L : Complex)=1 := by linear_combination h
    have : L=1 := by exact_mod_cast this
    omega
  have h := (movingCharacter_common_power_rootScale_tendsto chi eta m L hm hML hPowers).div_const
    (m : Complex)
  have hLimit :
      (-((if chi^L=1 then (1 : Complex) else 0) - (if eta^L=1 then (1 : Complex) else 0)) /
        ((1-Inv.inv (L : Real) : Real) : Complex)) / (m : Complex) =
      -(L : Complex)/((m : Complex)*((L : Complex)-1)) *
        ((if chi^L=1 then (1 : Complex) else 0) - (if eta^L=1 then (1 : Complex) else 0)) := by
    push_cast
    field_simp [hM, hL, hL1]
  rw [hLimit] at h
  have hX : Tendsto (fun P : Nat => (P : Real)^m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < m by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : Nat),
    hX.eventually (Filter.eventually_ge_atTop (3 : Real))] with P hP hx
  have hPPos : 0 < (P : Real) := by exact_mod_cast (show 0 < P by omega)
  have hExponent : (m : Real)*(1-Inv.inv (L : Real)) =
      (m : Real)*((L : Real)-1)/(L : Real) := by field_simp [hLR]
  have hScale : ((P : Real)^m)^(1-Inv.inv (L : Real))*Real.log ((P : Real)^m) =
      (m : Real)*((P : Real)^((m : Real)*((L : Real)-1)/(L : Real))*Real.log P) := by
    rw [Real.log_pow, <- Real.rpow_natCast, <- Real.rpow_mul hPPos.le, hExponent]
    ring
  dsimp only [centeredCharacterPrefixDifference]
  rw [centeredCharacterWeightedIntegral_changeLevel_primorial_sub chi P hx,
    centeredCharacterWeightedIntegral_changeLevel_primorial_sub eta P hx, hScale, Real.log_pow]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp [hM]

/-- Against the principal character, a nonprincipal resonant character
has the explicit positive next-layer comparison constant, unconditionally. -/
theorem centeredCharacter_resonant_principal_comparison_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hChi : Not (chi=1))
    (m : Nat) (hm : 1 <= m) (hResonance : chi^(m+1)=1) :
    Tendsto (fun P : Nat =>
      ((((P : Real)^((m : Real)*((m+1 : Nat) : Real)/((m+2 : Nat) : Real))*Real.log P : Real) : Complex) *
        centeredCharacterPrefixDifference chi (1 : DirichletCharacter Complex N) m P))
      atTop (nhds (((m+2 : Nat) : Complex)/((m : Complex)*((m+1 : Nat) : Complex)))) := by
  have hPowers : forall j : Nat, m+1 <= j -> j < m+2 ->
      chi^j=(1 : DirichletCharacter Complex N)^j := by
    intro j hjLow hjHigh
    have hj : j=m+1 := by omega
    simpa only [hj, one_pow] using hResonance
  have hNext : chi^(m+2)=chi := by
    rw [show m+2=(m+1)+1 by omega, pow_succ, hResonance, one_mul]
  have h := centeredCharacter_common_power_resonance chi (1 : DirichletCharacter Complex N)
    m (m+2) hm (by omega) hPowers
  have hReal : ((m+2 : Nat) : Real)-1=((m+1 : Nat) : Real) := by push_cast; ring
  have hComplex : ((m+2 : Nat) : Complex)-1=((m+1 : Nat) : Complex) := by push_cast; ring
  simpa only [hNext, if_neg hChi, one_pow, ite_true, zero_sub,
    mul_neg_one, neg_div, neg_neg, hReal, hComplex] using h

/-- Every nonprincipal character admits cofinally many fixed resonant
layers with this sharper positive asymptotic comparison, without GRH. -/
theorem centeredCharacter_unconditional_positive_comparison_layers_cofinal
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hChi : Not (chi=1))
    (m0 : Nat) :
    exists m : Nat, And (m0 <= m) (And (1 <= m) (And (chi^(m+1)=1)
      (Tendsto (fun P : Nat =>
        ((((P : Real)^((m : Real)*((m+1 : Nat) : Real)/((m+2 : Nat) : Real))*Real.log P : Real) : Complex) *
          centeredCharacterPrefixDifference chi (1 : DirichletCharacter Complex N) m P))
        atTop (nhds (((m+2 : Nat) : Complex)/((m : Complex)*((m+1 : Nat) : Complex))))))) := by
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
  exact Exists.intro m (And.intro hm0 (And.intro hm (And.intro hResonance
    (centeredCharacter_resonant_principal_comparison_tendsto chi hChi m hm hResonance))))

end

end RobinBV.NumberField
