import RobinBV.NumberField.Proof.MovingCharacterAsymptotic

/-!
# Actual centered integrals at moving induced-character levels

The complete prime-power deletion integral is identified with the difference
of the actual induced and original character integrals. Principal characters
are centered before integration, and changing level preserves principality.
The moving modulus is the least common multiple with the inclusive primorial.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex Filter MeasureTheory Set BombieriVinogradov.SiegelWalfisz
open scoped Classical

noncomputable section

/-- The actual character integral with its pole contribution subtracted
inside the integrand. For nonprincipal characters the centering is zero. -/
def centeredCharacterWeightedIntegral
    {N : Nat} (chi : DirichletCharacter Complex N) (x : Real) : Complex :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    (characterChebyshevSum (Nat.floor t) chi - (if chi = 1 then (t : Complex) else 0)) *
      (Robin1984.robinRealWeight 1 t : Complex))

/-- The centered integral is absolutely integrable for every character,
including principal and imprimitive characters, without ERH. -/
theorem integrableOn_centeredCharacterWeightedError
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) {x : Real} (hx : 3 <= x) :
    IntegrableOn (fun t : Real =>
      (characterChebyshevSum (Nat.floor t) chi - (if chi = 1 then (t : Complex) else 0)) *
        (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
  by_cases hChi : chi = 1
  case pos =>
    subst chi
    simpa using integrableOn_principalCenteredWeightedError (N := N) hx
  case neg =>
    have hSubset : Ioi x <= Ioi (3 : Real) := by
      intro t ht
      exact hx.trans_lt ht
    simpa only [if_neg hChi, sub_zero] using
      (integrableOn_characterChebyshevStep_mul_weight_one chi hChi).mono_set hSubset

/-- Principal centering agrees exactly with the previously proved actual
principal endpoint; this is an identity of integrals, not a new hypothesis. -/
theorem centeredCharacterWeightedIntegral_principal
    {N : Nat} [NeZero N] (x : Real) :
    centeredCharacterWeightedIntegral (1 : DirichletCharacter Complex N) x =
      principalCenteredWeightedIntegral N x := by
  simp [centeredCharacterWeightedIntegral, principalCenteredWeightedIntegral]

/-- In the nonprincipal case the centered definition is exactly the
existing character endpoint used in the ERH critical criterion. -/
theorem centeredCharacterWeightedIntegral_nonprincipal
    {N : Nat} (chi : DirichletCharacter Complex N) (hChi : Not (chi = 1)) (x : Real) :
    centeredCharacterWeightedIntegral chi x = dirichletCharacterWeightedIntegral chi 1 x := by
  simp only [centeredCharacterWeightedIntegral, dirichletCharacterWeightedIntegral,
    if_neg hChi, sub_zero]

/-- The actual induced character at lcm(N,primorial(P)) has precisely the
complete prime-power deletion already analyzed, with principal centering
preserved on both sides. -/
theorem centeredCharacterWeightedIntegral_changeLevel_primorial_sub
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (P : Nat)
    {x : Real} (hx : 3 <= x) :
    centeredCharacterWeightedIntegral (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) x -
      centeredCharacterWeightedIntegral chi x = movingCharacterCorrection chi P x := by
  let : NeZero (primorial P) := NeZero.mk (primorial_ne_zero P)
  let : NeZero (Nat.lcm N (primorial P)) :=
    NeZero.mk (Nat.lcm_ne_zero (NeZero.ne N) (primorial_ne_zero P))
  have hStep (t : Real) :
      characterChebyshevSum (Nat.floor t) (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) -
        characterChebyshevSum (Nat.floor t) chi =
          -Finset.sum (Nat.primesLE P) (fun p => chi.primePowerChebyshevStep p t) := by
    unfold characterChebyshevSum BombieriVinogradov.VaughanMeanValue.psiCharacterSum
    rw [<- Finset.sum_sub_distrib]
    simp_rw [<- mul_sub]
    rw [chi.sum_vonMangoldt_mul_changeLevel_lcm_sub, primeFactors_primorial]
    rfl
  have hCenter (t : Real) :
      (if chi.changeLevel (Nat.dvd_lcm_left N (primorial P)) = 1 then (t : Complex) else 0) =
        (if chi = 1 then (t : Complex) else 0) := by
    rw [DirichletCharacter.changeLevel_eq_one_iff]
  have hFirst := integrableOn_centeredCharacterWeightedError
    (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) hx
  have hSecond := integrableOn_centeredCharacterWeightedError chi hx
  unfold centeredCharacterWeightedIntegral movingCharacterCorrection
  rw [<- integral_sub hFirst hSecond, <- integral_neg]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hCenter]
  calc
    _ = (characterChebyshevSum (Nat.floor t)
        (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) -
          characterChebyshevSum (Nat.floor t) chi) * (Robin1984.robinRealWeight 1 t : Complex) := by ring
    _ = _ := by rw [hStep, neg_mul]

/-- The complete principal-power coefficient belongs to the actual moving
centered character integral difference, not just an abstract deletion model. -/
theorem centeredCharacter_changeLevel_primorial_normalized_tendsto
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (k : Nat) :
    Tendsto (fun P : Nat => (((P : Real) ^ k * Real.log P : Real) : Complex) *
      (centeredCharacterWeightedIntegral
        (chi.changeLevel (Nat.dvd_lcm_left N (primorial P))) ((P : Real) ^ (k + 1)) -
          centeredCharacterWeightedIntegral chi ((P : Real) ^ (k + 1)))) atTop
      (nhds (-Finset.sum (Finset.Icc 1 (k + 1))
        (fun j => if chi ^ j = 1 then (1 : Complex) else 0) / ((k + 1 : Nat) : Complex))) := by
  apply (movingCharacterCorrection_normalized_tendsto chi k).congr'
  filter_upwards [Filter.eventually_ge_atTop (3 : Nat)] with P hP
  have hPow : 0 < P ^ k := Nat.pow_pos (show 0 < P by omega)
  have hNat : 3 <= P ^ (k + 1) := by rw [pow_succ]; nlinarith
  have hx : 3 <= (P : Real) ^ (k + 1) := by exact_mod_cast hNat
  rw [centeredCharacterWeightedIntegral_changeLevel_primorial_sub chi P hx]

end

end RobinBV.NumberField
