import RobinBV.NumberField.Proof.MovingCharacterPowerCancellation

/-!
# Unconditional arithmetic asymptotics from finite power-fiber cancellation

The cancellation hypotheses are finite algebraic coefficient identities.
Their complete root-tail consequences are proved, not assumed.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter
open scoped Classical

noncomputable section

/-- Actual single-character level shift with its complete finite prime
moment retained. -/
def centeredCharacterPrefix {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (m P : Nat) : Complex :=
  let x : Real := (P : Real)^m
  centeredCharacterWeightedIntegral (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) x -
    centeredCharacterWeightedIntegral chi x +
  (Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
    Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N)^j))) /
      ((x : Complex)*(m : Complex)*(Real.log P : Complex))

/-- The actual finite weighted packet; all character-specific moments
and both levels of every integral remain present. -/
def centeredCharacterPacketPrefix {N : Nat} [NeZero N] {I : Type*}
    (s : Finset I) (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (m P : Nat) : Complex :=
  s.sum (fun i => c i*centeredCharacterPrefix (chi i) m P)

/-- Finite algebraic zero fibers imply exact cancellation of the complete
root tails, with no analytic estimate or integrability premise. -/
theorem characterPacket_rootTail_eq_zero_of_fiber_cancellation
    {N : Nat} [NeZero N] {I : Type*}
    (s : Finset I) (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (j : Nat) (r x : Real)
    (hFibers : forall psi : DirichletCharacter Complex N,
      (s.filter (fun i => (chi i)^j=psi)).sum c=0) :
    s.sum (fun i => c i*rootPrimeCharacterTail ((chi i)^j) r x)=0 := by
  rw [<- Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image (fun i => (chi i)^j))
    (g := fun i => (chi i)^j)
    (fun i hi => Finset.mem_image_of_mem (fun k => (chi k)^j) hi)
    (fun i => c i*rootPrimeCharacterTail ((chi i)^j) r x)]
  apply Finset.sum_eq_zero
  intro psi hPsi
  calc
    (s.filter (fun i => (chi i)^j=psi)).sum
        (fun i => c i*rootPrimeCharacterTail ((chi i)^j) r x) =
      (s.filter (fun i => (chi i)^j=psi)).sum
        (fun i => c i*rootPrimeCharacterTail psi r x) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = ((s.filter (fun i => (chi i)^j=psi)).sum c)*rootPrimeCharacterTail psi r x :=
      (Finset.sum_mul _ _ _).symm
    _ = 0 := by rw [hFibers psi, zero_mul]

/-- Complete actual single-character uncapped layer expansion at the
selected root scale, without ERH or an upper restriction on L. -/
theorem centeredCharacterPrefix_uncapped_layers_error_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (m L : Nat) (hm : 1 <= m) (hML : m+1 <= L) :
    Tendsto (fun P : Nat =>
      (((((P : Real)^m)^(1-Inv.inv (L : Real))*Real.log ((P : Real)^m) : Real) : Complex) *
        (centeredCharacterPrefix chi m P +
          Finset.sum (Finset.Icc (m+1) L) (fun j =>
            rootPrimeCharacterTail (chi^j) (Inv.inv (j : Real)) ((P : Real)^m)))))
      atTop (nhds (0 : Complex)) := by
  have h := movingCharacter_uncapped_layers_error_tendsto chi m L hm hML
  have hX : Tendsto (fun P : Nat => (P : Real)^m) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_atTop (show (0 : Real) < m by exact_mod_cast (show 0 < m by omega))).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  apply h.congr'
  filter_upwards [hX.eventually (Filter.eventually_ge_atTop (3 : Real))] with P hx
  dsimp only [centeredCharacterPrefix]
  rw [centeredCharacterWeightedIntegral_changeLevel_primorial_sub chi P hx]
  simp only [Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc]

/-- Algebraic vanishing of every earlier power fiber leaves exactly the
selected principal fiber in the full unconditional packet root-scale limit. -/
theorem centeredCharacterPacket_power_cancellation_rootScale_tendsto
    {N : Nat} [NeZero N] {I : Type*}
    (s : Finset I) (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (m L : Nat) (hm : 1 <= m) (hML : m+1 <= L)
    (hFibers : forall j : Nat, m+1 <= j -> j < L ->
      forall psi : DirichletCharacter Complex N,
        (s.filter (fun i => (chi i)^j=psi)).sum c=0) :
    Tendsto (fun P : Nat =>
      (((((P : Real)^m)^(1-Inv.inv (L : Real))*Real.log ((P : Real)^m) : Real) : Complex) *
        centeredCharacterPacketPrefix s chi c m P))
      atTop (nhds (-((s.filter (fun i => (chi i)^L=1)).sum c) /
        ((1-Inv.inv (L : Real) : Real) : Complex))) := by
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
  let A : Nat -> Complex := fun P =>
    (((((P : Real)^m)^(1-Inv.inv (L : Real))*Real.log ((P : Real)^m) : Real) : Complex))
  let R : I -> Nat -> Nat -> Complex := fun i j P =>
    rootPrimeCharacterTail ((chi i)^j) (Inv.inv (j : Real)) ((P : Real)^m)
  have hRootSum (P : Nat) :
      s.sum (fun i => c i*(Finset.Icc (m+1) L).sum (fun j => R i j P)) =
        s.sum (fun i => c i*R i L P) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm, <- Finset.sum_Ico_add_eq_sum_Icc hML]
    have hZero : (Finset.Ico (m+1) L).sum (fun j => s.sum (fun i => c i*R i j P))=0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact characterPacket_rootTail_eq_zero_of_fiber_cancellation s chi c j
        (Inv.inv (j : Real)) ((P : Real)^m)
        (hFibers j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2)
    rw [hZero, zero_add]
  have hExpand (P : Nat) :
      s.sum (fun i => c i*(A P*(centeredCharacterPrefix (chi i) m P +
        (Finset.Icc (m+1) L).sum (fun j => R i j P)))) =
      A P*(centeredCharacterPacketPrefix s chi c m P +
        s.sum (fun i => c i*(Finset.Icc (m+1) L).sum (fun j => R i j P))) := by
    calc
      _ = s.sum (fun i => A P*(c i*centeredCharacterPrefix (chi i) m P +
          c i*(Finset.Icc (m+1) L).sum (fun j => R i j P))) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [<- Finset.mul_sum, Finset.sum_add_distrib]; rfl
  have hSelectedExpand (P : Nat) :
      s.sum (fun i => c i*(A P*R i L P)) = A P*s.sum (fun i => c i*R i L P) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hError := tendsto_finsetSum s (fun i (_ : Membership.mem s i) =>
    (centeredCharacterPrefix_uncapped_layers_error_tendsto (chi i) m L hm hML).const_mul (c i))
  simp only [mul_zero, Finset.sum_const_zero] at hError
  have hSelected := tendsto_finsetSum s (fun i (_ : Membership.mem s i) =>
    ((rootPrimeCharacterTail_normalized_tendsto ((chi i)^L) hr0 hr1).comp hX).const_mul (c i))
  have hFiberLimit :
      s.sum (fun i => c i*((if (chi i)^L=1 then (1 : Complex) else 0) /
        ((1-Inv.inv (L : Real) : Real) : Complex))) =
      ((s.filter (fun i => (chi i)^L=1)).sum c) / ((1-Inv.inv (L : Real) : Real) : Complex) := by
    simp only [div_eq_mul_inv, Finset.sum_filter]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [hFiberLimit] at hSelected
  have h := hError.sub hSelected
  simp only [zero_sub, <- neg_div] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro P
  change s.sum (fun i => c i*(A P*(centeredCharacterPrefix (chi i) m P +
      (Finset.Icc (m+1) L).sum (fun j => R i j P)))) -
      s.sum (fun i => c i*(A P*R i L P)) = A P*centeredCharacterPacketPrefix s chi c m P
  rw [hExpand, hRootSum, hSelectedExpand]
  ring

/-- Explicit prime-clock packet asymptotic. Only algebraic earlier-power
fiber cancellation is required; the surviving coefficient is exact. -/
theorem centeredCharacterPacket_power_cancellation_resonance
    {N : Nat} [NeZero N] {I : Type*}
    (s : Finset I) (chi : I -> DirichletCharacter Complex N) (c : I -> Complex)
    (m L : Nat) (hm : 1 <= m) (hML : m+1 <= L)
    (hFibers : forall j : Nat, m+1 <= j -> j < L ->
      forall psi : DirichletCharacter Complex N,
        (s.filter (fun i => (chi i)^j=psi)).sum c=0) :
    Tendsto (fun P : Nat =>
      ((((P : Real)^((m : Real)*((L : Real)-1)/(L : Real))*Real.log P : Real) : Complex) *
        centeredCharacterPacketPrefix s chi c m P))
      atTop (nhds (-(L : Complex)/((m : Complex)*((L : Complex)-1)) *
        (s.filter (fun i => (chi i)^L=1)).sum c)) := by
  have hM : Not ((m : Complex)=0) := by exact_mod_cast (show Not (m=0) by omega)
  have hL : Not ((L : Complex)=0) := by exact_mod_cast (show Not (L=0) by omega)
  have hLR : Not ((L : Real)=0) := by exact_mod_cast (show Not (L=0) by omega)
  have hL1 : Not ((L : Complex)-1=0) := by
    intro h
    have : (L : Complex)=1 := by linear_combination h
    have : L=1 := by exact_mod_cast this
    omega
  have h := (centeredCharacterPacket_power_cancellation_rootScale_tendsto
    s chi c m L hm hML hFibers).div_const (m : Complex)
  have hLimit : (-(s.filter (fun i => (chi i)^L=1)).sum c /
      ((1-Inv.inv (L : Real) : Real) : Complex))/(m : Complex) =
      -(L : Complex)/((m : Complex)*((L : Complex)-1)) *
        (s.filter (fun i => (chi i)^L=1)).sum c := by
    push_cast
    field_simp [hM, hL, hL1]
  rw [hLimit] at h
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with P hP
  have hPPos : 0 < (P : Real) := by exact_mod_cast (show 0 < P by omega)
  have hExponent : (m : Real)*(1-Inv.inv (L : Real)) =
      (m : Real)*((L : Real)-1)/(L : Real) := by field_simp [hLR]
  have hScale : ((P : Real)^m)^(1-Inv.inv (L : Real))*Real.log ((P : Real)^m) =
      (m : Real)*((P : Real)^((m : Real)*((L : Real)-1)/(L : Real))*Real.log P) := by
    rw [Real.log_pow, <- Real.rpow_natCast, <- Real.rpow_mul hPPos.le, hExponent]
    ring
  rw [hScale]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp [hM]

end

end RobinBV.NumberField
