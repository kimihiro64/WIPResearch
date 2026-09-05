import RobinBV.NumberField.Proof.MovingCharacterSecondary

/-!
# Complete finite character-layer hierarchy

Any fixed finite interval of root-prime layers is separated exactly.
Every capped root moment and the entire remaining higher-power integral
stay in the identity. The iteration is finite, not a recursive simplifier.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set
open scoped Classical

noncomputable section

/-- Separate exactly one complete root-prime layer from its full remainder. -/
theorem higherCharacterPrimePower_integral_eq_first_add
    {N : Nat} (chi : DirichletCharacter Complex N) (P k : Nat) (hk : 1 <= k)
    {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real =>
      Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p k t) *
        (Robin1984.robinRealWeight 1 t : Complex)) =
      cappedRootPrimeCharacterTail (chi ^ (k + 1)) P (Inv.inv ((k + 1 : Nat) : Real)) x +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p (k + 1) t) *
            (Robin1984.robinRealWeight 1 t : Complex)) := by
  have hCap := (cappedRootPrimeCharacterTail_integral_data (chi ^ (k + 1)) P
    (Inv.inv ((k + 1 : Nat) : Real)) hx).1
  have hHigher := (higherCharacterPrimePower_integral_data chi P (k + 1) (by omega) hx).1
  unfold cappedRootPrimeCharacterTail
  rw [<- integral_add hCap hHigher]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [chi.sum_primePowerHigherStep_eq_primeMoment_add_higher P k (hx.trans ht).le, add_mul]

/-- The complete higher-power integral equals any finite initial interval
of its capped root moments plus the entire remaining higher-power integral. -/
theorem higherCharacterPrimePower_integral_eq_layers_add
    {N : Nat} (chi : DirichletCharacter Complex N) (P m L : Nat) (hm : 1 <= m)
    (hML : m <= L) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t : Real =>
      Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p m t) *
        (Robin1984.robinRealWeight 1 t : Complex)) =
      Finset.sum (Finset.Icc (m + 1) L) (fun j =>
        cappedRootPrimeCharacterTail (chi ^ j) P (Inv.inv (j : Real)) x) +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p L t) *
            (Robin1984.robinRealWeight 1 t : Complex)) := by
  induction L, hML using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self m), Finset.sum_empty, zero_add]
  | succ L hML ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [higherCharacterPrimePower_integral_eq_first_add chi P L (by omega) hx] at ih
    exact ih.trans (by ring)

/-- Exact hierarchy after the admitted finite prime moments are removed.
The selected last layer, all intervening layers and the full higher tail
remain explicit; no prime moment is replaced by an analytic average. -/
theorem movingCharacterCorrection_layer_identity
    {N : Nat} (chi : DirichletCharacter Complex N) (P m L : Nat)
    (hm : 1 <= m) (hML : m + 1 <= L) {x : Real} (hx : 3 <= x)
    (hP : ((P ^ m : Nat) : Real) <= x) :
    movingCharacterCorrection chi P x +
      Finset.sum (Nat.primesLE P) (fun p => (Real.log p : Complex) *
        Finset.sum (Finset.Icc 1 m) (fun j => chi (p : ZMod N) ^ j)) /
          ((x : Complex) * (Real.log x : Complex)) =
      -Finset.sum (Finset.Ico (m + 1) L) (fun j =>
        cappedRootPrimeCharacterTail (chi ^ j) P (Inv.inv (j : Real)) x) -
        cappedRootPrimeCharacterTail (chi ^ L) P (Inv.inv (L : Real)) x -
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            Finset.sum (Nat.primesLE P) (fun p => chi.primePowerHigherStep p L t) *
              (Robin1984.robinRealWeight 1 t : Complex)) := by
  rw [movingCharacterCorrection_prefix_eq_higher_integral chi P m hm hx hP,
    higherCharacterPrimePower_integral_eq_layers_add chi P m L hm (by omega) (by linarith)]
  have hSet : Finset.Icc (m + 1) L = Insert.insert L (Finset.Ico (m + 1) L) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hSet, Finset.sum_insert (by simp only [Finset.mem_Ico, lt_self_iff_false, and_false, not_false_eq_true])]
  ring

end

end RobinBV.NumberField
