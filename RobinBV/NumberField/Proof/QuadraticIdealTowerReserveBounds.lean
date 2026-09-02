import RobinBV.NumberField.Proof.IdealEulerReserveBounds
import RobinBV.NumberField.Proof.QuadraticPrimeIdealNormMultiplicity
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt

/-!
# Quadratic ideal-lcm tower reserve bounds

The degree-two norm-fiber bound controls both sides of the square-root split.
Low norms contribute at most their cardinality times the reciprocal frontier;
high norms are grouped by exact absolute norm and bounded by a telescoping
reciprocal-square tail. The resulting tower reserve is at most
`12 / floor(sqrt B)` for every positive frontier.
-/

namespace RobinBV.NumberField

open Asymptotics
open Filter

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

private theorem rpow_isLittleO_rpow_atTop_of_lt
    {a b : Real} (hab : a < b) :
    (fun x : Real => x ^ a) =o[(atTop : Filter Real)]
      (fun x : Real => x ^ b) := by
  apply isLittleO_of_tendsto'
  next =>
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    intro hZero
    exact False.elim ((Real.rpow_pos_of_pos hx b).ne' hZero)
  next =>
    have hLimit := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
    exact hLimit.congr' ((eventually_gt_atTop (0 : Real)).mono
      (fun x hx => by
        calc
          x ^ (-(b - a)) = x ^ (a - b) := by
            congr 1
            ring
          _ = x ^ a / x ^ b := Real.rpow_sub hx a b))

/-- The floor-square-root bound implies a comparable bound using the ordinary
real square root. -/
theorem quadraticIdealLcmTowerReserve_le_twentyFour_inv_realSqrt
    (D : NumberField.OddFundamentalDiscriminant) {B : Nat}
    (hB : 0 < B) :
    idealLcmTowerReserve D.QuadraticField B <=
      24 * Inv.inv (Real.sqrt (B : Real)) := by
  let m := Nat.sqrt B
  have hmPosNat : 0 < m := (Nat.sqrt_pos).2 hB
  have hmPos : (0 : Real) < m := by exact_mod_cast hmPosNat
  have hSqrtPos : 0 < Real.sqrt (B : Real) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hB)
  have hUpperNat : B <= (m + 1) ^ (2 : Nat) := by
    simpa [pow_two] using (Nat.lt_succ_sqrt B).le
  have hUpperReal : (B : Real) <= ((m + 1 : Nat) : Real) ^ (2 : Nat) := by
    exact_mod_cast hUpperNat
  have hSqrtLeSucc : Real.sqrt (B : Real) <= (m : Real) + 1 := by
    rw [Real.sqrt_le_iff]
    apply And.intro
    next => positivity
    next =>
      push_cast at hUpperReal
      nlinarith
  have hmOne : (1 : Real) <= m := by exact_mod_cast hmPosNat
  have hSqrtLeTwo : Real.sqrt (B : Real) <= 2 * (m : Real) := by
    linarith
  have hLeftCancel :
      Inv.inv (m : Real) *
          ((m : Real) * Real.sqrt (B : Real)) =
        Real.sqrt (B : Real) := by
    field_simp
  have hRightCancel :
      (2 * Inv.inv (Real.sqrt (B : Real))) *
          ((m : Real) * Real.sqrt (B : Real)) =
        2 * (m : Real) := by
    field_simp
  have hInv :
      Inv.inv (m : Real) <= 2 * Inv.inv (Real.sqrt (B : Real)) := by
    by_contra hNot
    have hGt :
        2 * Inv.inv (Real.sqrt (B : Real)) < Inv.inv (m : Real) :=
      lt_of_not_ge hNot
    have hMul := mul_lt_mul_of_pos_right hGt (mul_pos hmPos hSqrtPos)
    rw [hLeftCancel, hRightCancel] at hMul
    linarith
  have hTower := quadraticIdealLcmTowerReserve_le_twelve_inv_sqrt D hB
  change idealLcmTowerReserve D.QuadraticField B <=
    24 * Inv.inv (Real.sqrt (B : Real))
  calc
    idealLcmTowerReserve D.QuadraticField B <=
        12 * Inv.inv (m : Real) := hTower
    _ <= 24 * Inv.inv (Real.sqrt (B : Real)) := by linarith

/-- For every real exponent below the critical half exponent, the quadratic
ideal-lcm tower reserve is little-o of `B ^ (-b)`. -/
theorem quadraticIdealLcmTowerReserve_isLittleO_rpow
    (D : NumberField.OddFundamentalDiscriminant) {b : Real}
    (hb : b < (1 : Real) / 2) :
    (fun B : Nat => idealLcmTowerReserve D.QuadraticField B) =o[
      (atTop : Filter Nat)]
      (fun B : Nat => (B : Real) ^ (-b)) := by
  have hBigO :
      (fun B : Nat => idealLcmTowerReserve D.QuadraticField B) =O[
        (atTop : Filter Nat)]
        (fun B : Nat => (B : Real) ^ (-((1 : Real) / 2))) := by
    apply IsBigO.of_bound 24
    filter_upwards [eventually_ge_atTop 1] with B hB
    have hBPos : 0 < B := by omega
    have hReserveNonneg := idealLcmTowerReserve_nonneg D.QuadraticField B
    have hReserveBound :=
      quadraticIdealLcmTowerReserve_le_twentyFour_inv_realSqrt D hBPos
    have hEq :
        Inv.inv (Real.sqrt (B : Real)) =
          (B : Real) ^ (-((1 : Real) / 2)) := by
      have hNonneg : (0 : Real) <= B := by positivity
      simpa [Real.sqrt_eq_rpow] using
        (Real.rpow_neg hNonneg ((1 : Real) / 2)).symm
    rw [Real.norm_of_nonneg hReserveNonneg]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    rw [<- hEq]
    exact hReserveBound
  have hPowersReal :
      (fun x : Real => x ^ (-((1 : Real) / 2))) =o[
        (atTop : Filter Real)]
        (fun x : Real => x ^ (-b)) :=
    rpow_isLittleO_rpow_atTop_of_lt (by linarith)
  have hPowersNat :
      (fun B : Nat => (B : Real) ^ (-((1 : Real) / 2))) =o[
        (atTop : Filter Nat)]
        (fun B : Nat => (B : Real) ^ (-b)) :=
    hPowersReal.comp_tendsto tendsto_natCast_atTop_atTop
  exact hBigO.trans_isLittleO hPowersNat

end

end RobinBV.NumberField
