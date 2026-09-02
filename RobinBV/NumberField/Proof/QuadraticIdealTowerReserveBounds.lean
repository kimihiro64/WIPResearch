import RobinBV.NumberField.Proof.IdealEulerReserveBounds
import RobinBV.NumberField.Proof.QuadraticPrimeIdealNormMultiplicity
import Mathlib.Analysis.PSeries

/-!
# Quadratic ideal-lcm tower reserve bounds

The degree-two norm-fiber bound controls both sides of the square-root split.
Low norms contribute at most their cardinality times the reciprocal frontier;
high norms are grouped by exact absolute norm and bounded by a telescoping
reciprocal-square tail. The resulting tower reserve is at most
`12 / floor(sqrt B)` for every positive frontier.
-/

namespace RobinBV.NumberField

noncomputable section

/-- There are at most `2 * (M + 1)` selected quadratic prime ideals of norm at
most `M`. -/
theorem quadraticPrimeIdealsLowNorm_card_le
    (D : NumberField.OddFundamentalDiscriminant) (B M : Nat) :
    ((primeIdealsUpToNorm D.QuadraticField B).filter
      (fun P => Ideal.absNorm P <= M)).card <= 2 * (M + 1) := by
  classical
  let S := (primeIdealsUpToNorm D.QuadraticField B).filter
    (fun P => Ideal.absNorm P <= M)
  let toSigma : {P // Membership.mem S P} ->
      Sigma (fun i : Fin (M + 1) => quadraticPrimeIdealNormFiber D i.val) :=
    fun P => by
      let i : Fin (M + 1) :=
        Fin.mk (Ideal.absNorm P.val)
          (Nat.lt_succ_of_le (Finset.mem_filter.mp P.property).2)
      let Q : quadraticPrimeIdealNormFiber D i.val :=
        Subtype.mk P.val (And.intro
          (mem_primeIdealsUpToNorm_prime D.QuadraticField
            (Finset.mem_filter.mp P.property).1)
          (by rfl))
      exact Sigma.mk i Q
  letI (i : Fin (M + 1)) :
      Finite (quadraticPrimeIdealNormFiber D i.val) :=
    (Ideal.finite_setOfPred_absNorm_eq i.val).subset
      (fun _P hP => hP.2)
  letI : Finite
      (Sigma
        (fun i : Fin (M + 1) => quadraticPrimeIdealNormFiber D i.val)) :=
    inferInstance
  have hInjective : Function.Injective toSigma := by
    intro P Q hPQ
    have hVal : P.val = Q.val :=
      congrArg
        (fun Z : Sigma
          (fun i : Fin (M + 1) => quadraticPrimeIdealNormFiber D i.val) =>
            Z.2.val)
        hPQ
    apply Subtype.ext
    exact hVal
  have hCardSigma :
      Nat.card
          (Sigma
            (fun i : Fin (M + 1) => quadraticPrimeIdealNormFiber D i.val)) <=
        2 * (M + 1) := by
    rw [Nat.card_sigma]
    calc
      Finset.univ.sum
          (fun i : Fin (M + 1) =>
            Nat.card (quadraticPrimeIdealNormFiber D i.val)) <=
          Finset.univ.sum (fun _i : Fin (M + 1) => 2) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact quadraticPrimeIdealNormFiber_card_le_two D i.val
      _ = 2 * (M + 1) := by simp [Nat.mul_comm]
  change S.card <= 2 * (M + 1)
  calc
    S.card = Nat.card {P // Membership.mem S P} := by simp
    _ <= Nat.card
        (Sigma
          (fun i : Fin (M + 1) => quadraticPrimeIdealNormFiber D i.val)) :=
      Nat.card_le_card_of_injective toSigma hInjective
    _ <= 2 * (M + 1) := hCardSigma

/-- Grouping by exact norm bounds the high-norm reciprocal-square sum by twice
the corresponding integer sum. -/
theorem quadraticPrimeIdealsHighNorm_invSq_sum_le
    (D : NumberField.OddFundamentalDiscriminant) (B M : Nat) :
    ((primeIdealsUpToNorm D.QuadraticField B).filter
        (fun P => M < Ideal.absNorm P)).sum
        (fun P => (Inv.inv (Ideal.absNorm P : Real)) ^ (2 : Nat)) <=
      2 * (Finset.Ioc M B).sum
        (fun n => (Inv.inv (n : Real)) ^ (2 : Nat)) := by
  classical
  let high := (primeIdealsUpToNorm D.QuadraticField B).filter
    (fun P => M < Ideal.absNorm P)
  let f := fun P : Ideal
      (NumberField.RingOfIntegers D.QuadraticField) =>
    (Inv.inv (Ideal.absNorm P : Real)) ^ (2 : Nat)
  have hMaps : Set.MapsTo Ideal.absNorm
      (high : Set (Ideal (NumberField.RingOfIntegers D.QuadraticField)))
      (Finset.Ioc M B : Set Nat) := by
    intro P hP
    have hFilter := Finset.mem_filter.mp hP
    change Membership.mem (Finset.Ioc M B) (Ideal.absNorm P)
    rw [Finset.mem_Ioc]
    exact And.intro hFilter.2
      (absNorm_le_of_mem_primeIdealsUpToNorm D.QuadraticField hFilter.1)
  have hFiberCard : forall n : Nat,
      (high.filter (fun P => Ideal.absNorm P = n)).card <= 2 := by
    intro n
    letI : Finite (quadraticPrimeIdealNormFiber D n) :=
      (Ideal.finite_setOfPred_absNorm_eq n).subset
        (fun _P hP => hP.2)
    let toFiber :
        {P // Membership.mem
          (high.filter (fun Q => Ideal.absNorm Q = n)) P} ->
          quadraticPrimeIdealNormFiber D n := fun P =>
      Subtype.mk P.val (And.intro
        (mem_primeIdealsUpToNorm_prime D.QuadraticField
          (Finset.mem_filter.mp
            (Finset.mem_filter.mp P.property).1).1)
        (Finset.mem_filter.mp P.property).2)
    have hInjective : Function.Injective toFiber := by
      intro P Q hPQ
      have hVal : P.val = Q.val :=
        congrArg
          (fun Z : quadraticPrimeIdealNormFiber D n => Z.val)
          hPQ
      apply Subtype.ext
      exact hVal
    calc
      (high.filter (fun P => Ideal.absNorm P = n)).card =
          Nat.card
            {P // Membership.mem
              (high.filter (fun Q => Ideal.absNorm Q = n)) P} := by
        rw [Nat.card_eq_fintype_card]
        exact (Fintype.card_coe
          (high.filter (fun Q => Ideal.absNorm Q = n))).symm
      _ <= Nat.card (quadraticPrimeIdealNormFiber D n) :=
        Nat.card_le_card_of_injective toFiber hInjective
      _ <= 2 := quadraticPrimeIdealNormFiber_card_le_two D n
  have hInner : forall n : Nat, Membership.mem (Finset.Ioc M B) n ->
      (high.filter (fun P => Ideal.absNorm P = n)).sum f <=
        2 * (Inv.inv (n : Real)) ^ (2 : Nat) := by
    intro n _hn
    calc
      (high.filter (fun P => Ideal.absNorm P = n)).sum f =
          (high.filter (fun P => Ideal.absNorm P = n)).sum
            (fun _P => (Inv.inv (n : Real)) ^ (2 : Nat)) := by
        apply Finset.sum_congr rfl
        intro P hP
        have hNorm := (Finset.mem_filter.mp hP).2
        unfold f
        rw [hNorm]
      _ = ((high.filter (fun P => Ideal.absNorm P = n)).card : Real) *
          (Inv.inv (n : Real)) ^ (2 : Nat) := by simp
      _ <= 2 * (Inv.inv (n : Real)) ^ (2 : Nat) := by
        apply mul_le_mul_of_nonneg_right
        next => exact_mod_cast hFiberCard n
        next => positivity
  change high.sum f <=
    2 * (Finset.Ioc M B).sum
      (fun n => (Inv.inv (n : Real)) ^ (2 : Nat))
  calc
    high.sum f = (Finset.Ioc M B).sum
        (fun n =>
          (high.filter (fun P => Ideal.absNorm P = n)).sum f) := by
      exact (Finset.sum_fiberwise_of_maps_to hMaps f).symm
    _ <= (Finset.Ioc M B).sum
        (fun n => 2 * (Inv.inv (n : Real)) ^ (2 : Nat)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hInner n hn
    _ = 2 * (Finset.Ioc M B).sum
        (fun n => (Inv.inv (n : Real)) ^ (2 : Nat)) := by
      rw [Finset.mul_sum]

/-- The quadratic high-norm reciprocal-square tail is at most `2 / M`. -/
theorem quadraticPrimeIdealsHighNorm_invSq_sum_le_inv
    (D : NumberField.OddFundamentalDiscriminant) {B M : Nat}
    (hM : Not (M = 0)) (hMB : M <= B) :
    ((primeIdealsUpToNorm D.QuadraticField B).filter
        (fun P => M < Ideal.absNorm P)).sum
        (fun P => (Inv.inv (Ideal.absNorm P : Real)) ^ (2 : Nat)) <=
      2 * Inv.inv (M : Real) := by
  have hTail :
      (Finset.Ioc M B).sum
          (fun n => Inv.inv ((n : Real) ^ (2 : Nat))) <=
        Inv.inv (M : Real) - Inv.inv (B : Real) :=
    sum_Ioc_inv_sq_le_sub hM hMB
  have hTailInv :
      (Finset.Ioc M B).sum
          (fun n => (Inv.inv (n : Real)) ^ (2 : Nat)) <=
        Inv.inv (M : Real) := by
    calc
      _ <= Inv.inv (M : Real) - Inv.inv (B : Real) := by
        simpa [inv_pow] using hTail
      _ <= Inv.inv (M : Real) := by
        have hInvB : 0 <= Inv.inv (B : Real) := by positivity
        linarith
  exact (quadraticPrimeIdealsHighNorm_invSq_sum_le D B M).trans
    (mul_le_mul_of_nonneg_left hTailInv (by norm_num))

/-- Before the final square-root simplification, the quadratic tower reserve
is bounded by explicit low- and high-norm contributions. -/
theorem quadraticIdealLcmTowerReserve_le_sqrt_envelope
    (D : NumberField.OddFundamentalDiscriminant) {B : Nat}
    (hB : 0 < B) :
    idealLcmTowerReserve D.QuadraticField B <=
      2 *
        (((2 * (Nat.sqrt B + 1) : Nat) : Real) * Inv.inv (B : Real) +
          2 * Inv.inv (Nat.sqrt B : Real)) := by
  have hSqrtPos : 0 < Nat.sqrt B := (Nat.sqrt_pos).2 hB
  have hLowNat :=
    quadraticPrimeIdealsLowNorm_card_le D B (Nat.sqrt B)
  have hLowReal :
      (((primeIdealsUpToNorm D.QuadraticField B).filter
          (fun P => Ideal.absNorm P <= Nat.sqrt B)).card : Real) <=
        ((2 * (Nat.sqrt B + 1) : Nat) : Real) := by
    exact_mod_cast hLowNat
  have hLow :
      (((primeIdealsUpToNorm D.QuadraticField B).filter
          (fun P => Ideal.absNorm P <= Nat.sqrt B)).card : Real) *
          Inv.inv (B : Real) <=
        ((2 * (Nat.sqrt B + 1) : Nat) : Real) *
          Inv.inv (B : Real) := by
    exact mul_le_mul_of_nonneg_right hLowReal (by positivity)
  have hHighRaw :=
    quadraticPrimeIdealsHighNorm_invSq_sum_le_inv D
      (Nat.ne_of_gt hSqrtPos) (Nat.sqrt_le_self B)
  have hHigh :
      ((primeIdealsUpToNorm D.QuadraticField B).filter
          (fun P => Not (Ideal.absNorm P <= Nat.sqrt B))).sum
          (fun P =>
            (Inv.inv (Ideal.absNorm P : Real)) ^ (2 : Nat)) <=
        2 * Inv.inv (Nat.sqrt B : Real) := by
    simpa only [not_le] using hHighRaw
  exact (idealLcmTowerReserve_le_two_mul_sqrt_split
      D.QuadraticField B).trans
    (mul_le_mul_of_nonneg_left (add_le_add hLow hHigh) (by norm_num))

/-- The complete quadratic ideal-lcm tower reserve has the elementary
critical-scale bound `12 / floor(sqrt B)`. -/
theorem quadraticIdealLcmTowerReserve_le_twelve_inv_sqrt
    (D : NumberField.OddFundamentalDiscriminant) {B : Nat}
    (hB : 0 < B) :
    idealLcmTowerReserve D.QuadraticField B <=
      12 * Inv.inv (Nat.sqrt B : Real) := by
  let m := Nat.sqrt B
  have hmPosNat : 0 < m := by
    exact (Nat.sqrt_pos).2 hB
  have hmPos : (0 : Real) < m := by exact_mod_cast hmPosNat
  have hBPos : (0 : Real) < B := by exact_mod_cast hB
  have hSquareNat : m * m <= B := by
    exact Nat.sqrt_le B
  have hSquare : (m : Real) * m <= B := by exact_mod_cast hSquareNat
  have hCross : 2 * ((m : Real) + 1) * m <= 4 * (B : Real) := by
    have hmOne : (1 : Real) <= m := by exact_mod_cast hmPosNat
    nlinarith
  have hLeftCancel :
      (2 * ((m : Real) + 1) * Inv.inv (B : Real)) *
          ((B : Real) * m) =
        2 * ((m : Real) + 1) * m := by
    field_simp
  have hRightCancel :
      (4 * Inv.inv (m : Real)) * ((B : Real) * m) =
        4 * (B : Real) := by
    field_simp
  have hLowScale :
      2 * ((m : Real) + 1) * Inv.inv (B : Real) <=
        4 * Inv.inv (m : Real) := by
    by_contra hNot
    have hGt :
        4 * Inv.inv (m : Real) <
          2 * ((m : Real) + 1) * Inv.inv (B : Real) :=
      lt_of_not_ge hNot
    have hMul := mul_lt_mul_of_pos_right hGt (mul_pos hBPos hmPos)
    rw [hLeftCancel, hRightCancel] at hMul
    linarith
  have hEnvelope := quadraticIdealLcmTowerReserve_le_sqrt_envelope D hB
  have hCoeff :
      (((2 * (Nat.sqrt B + 1) : Nat) : Real)) =
        2 * ((m : Real) + 1) := by
    unfold m
    push_cast
    ring
  rw [hCoeff] at hEnvelope
  change idealLcmTowerReserve D.QuadraticField B <=
    12 * Inv.inv (m : Real)
  calc
    idealLcmTowerReserve D.QuadraticField B <=
        2 *
          (2 * ((m : Real) + 1) * Inv.inv (B : Real) +
            2 * Inv.inv (m : Real)) := hEnvelope
    _ <= 12 * Inv.inv (m : Real) := by linarith

end

end RobinBV.NumberField
