import RobinBV.NumberField.Definitions.IdealEulerReserve
import RobinBV.NumberField.Proof.IdealAbundancyEulerProduct
import RobinBV.NumberField.Proof.IdealLcmPacket

/-!
# Exact Euler reserve identity for ideal lcm packets

The ideal abundancy of the complete packet is rewritten as a finite Euler
product.  Taking logarithms separates the inverse Mertens product from the
positive local tower reserve exactly.
-/

namespace RobinBV.NumberField

open UniqueFactorizationMonoid

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem idealLocalAbundancy_eq_eulerFactor
    {q : Nat} (hq : 1 < q) (e : Nat) :
    (Finset.univ.sum fun j : Fin (e + 1) => (q : Real) ^ j.val) /
        (q : Real) ^ e =
      (1 - (Inv.inv (q : Real)) ^ (e + 1)) /
        (1 - Inv.inv (q : Real)) := by
  have hqRealZero : Not ((q : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq))
  have hqRealOne : Not ((q : Real) = 1) := by
    exact_mod_cast (Nat.ne_of_gt hq)
  rw [Fin.sum_univ_eq_sum_range]
  rw [geom_sum_eq hqRealOne]
  rw [inv_pow]
  field_simp [hqRealZero]
  ring

theorem idealAbundancy_idealLcmPacket_eq_prod_local (B : Nat) :
    idealAbundancy K (idealLcmPacketNonZero K B) =
      (primeIdealsUpToNorm K B).prod fun P =>
        (Finset.univ.sum fun j : Fin
            (Nat.log (Ideal.absNorm P) B + 1) =>
          (Ideal.absNorm P : Real) ^ j.val) /
        ((Ideal.absNorm P : Real) ^ Nat.log (Ideal.absNorm P) B) := by
  rw [idealAbundancy_eq_prod_local]
  let support :=
    (normalizedFactors (idealLcmPacket K B)).toFinset
  change
    (Finset.univ.prod fun P : {P : Ideal
        (NumberField.RingOfIntegers K) // Membership.mem support P} =>
      (Finset.univ.sum fun j : Fin
          (Multiset.count P.val
            (normalizedFactors (idealLcmPacket K B)) + 1) =>
        (Ideal.absNorm P.val : Real) ^ j.val) /
      ((Ideal.absNorm P.val : Real) ^ Multiset.count P.val
        (normalizedFactors (idealLcmPacket K B)))) = _
  have hSubtype := Finset.prod_coe_sort
    (s := support)
    (f := fun P : Ideal (NumberField.RingOfIntegers K) =>
      (Finset.univ.sum fun j : Fin
          (Multiset.count P
            (normalizedFactors (idealLcmPacket K B)) + 1) =>
        (Ideal.absNorm P : Real) ^ j.val) /
      ((Ideal.absNorm P : Real) ^ Multiset.count P
        (normalizedFactors (idealLcmPacket K B))))
  rw [hSubtype]
  dsimp only [support]
  rw [support_normalizedFactors_idealLcmPacket]
  apply Finset.prod_congr rfl
  intro P hP
  rw [count_normalizedFactors_idealLcmPacket K B hP]

private theorem idealEulerDenominator_pos
    {B : Nat} {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (primeIdealsUpToNorm K B) P) :
    0 < 1 - Inv.inv (Ideal.absNorm P : Real) := by
  have hq := one_lt_absNorm_of_mem_primeIdealsUpToNorm K hP
  have hqReal : (1 : Real) < Ideal.absNorm P := by exact_mod_cast hq
  have hInvLt : Inv.inv (Ideal.absNorm P : Real) < 1 := by
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (a := (1 : Real))
        (b := (Ideal.absNorm P : Real)) zero_lt_one hqReal)
  exact sub_pos.mpr hInvLt

private theorem idealEulerNumerator_pos
    {B : Nat} {P : Ideal (NumberField.RingOfIntegers K)}
    (hP : Membership.mem (primeIdealsUpToNorm K B) P) :
    0 < 1 - (Inv.inv (Ideal.absNorm P : Real)) ^
        (Nat.log (Ideal.absNorm P) B + 1) := by
  have hq := one_lt_absNorm_of_mem_primeIdealsUpToNorm K hP
  have hqReal : (1 : Real) < Ideal.absNorm P := by exact_mod_cast hq
  have hInvNonneg : 0 <= Inv.inv (Ideal.absNorm P : Real) := by
    exact inv_nonneg.mpr (lt_trans zero_lt_one hqReal).le
  have hInvLt : Inv.inv (Ideal.absNorm P : Real) < 1 := by
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (a := (1 : Real))
        (b := (Ideal.absNorm P : Real)) zero_lt_one hqReal)
  exact sub_pos.mpr
    ((pow_lt_one_iff_of_nonneg hInvNonneg (Nat.succ_ne_zero _)).2 hInvLt)

theorem idealAbundancy_idealLcmPacket_eq_eulerProduct (B : Nat) :
    idealAbundancy K (idealLcmPacketNonZero K B) =
      (primeIdealsUpToNorm K B).prod fun P =>
        (1 - (Inv.inv (Ideal.absNorm P : Real)) ^
            (Nat.log (Ideal.absNorm P) B + 1)) /
          (1 - Inv.inv (Ideal.absNorm P : Real)) := by
  rw [idealAbundancy_idealLcmPacket_eq_prod_local]
  apply Finset.prod_congr rfl
  intro P hP
  exact idealLocalAbundancy_eq_eulerFactor
    (one_lt_absNorm_of_mem_primeIdealsUpToNorm K hP)
    (Nat.log (Ideal.absNorm P) B)

/-- The exact finite ideal Nicolas core: logarithmic packet abundancy equals
the logarithm of the inverse ideal Mertens product minus the tower reserve. -/
theorem log_idealAbundancy_idealLcmPacket_eq_mertens_sub_reserve
    (B : Nat) :
    Real.log (idealAbundancy K (idealLcmPacketNonZero K B)) =
      -Real.log (idealMertensProduct K B) -
        idealLcmTowerReserve K B := by
  rw [idealAbundancy_idealLcmPacket_eq_eulerProduct]
  have hLocal : forall P,
      Membership.mem (primeIdealsUpToNorm K B) P ->
        Not (((1 - (Inv.inv (Ideal.absNorm P : Real)) ^
            (Nat.log (Ideal.absNorm P) B + 1)) /
          (1 - Inv.inv (Ideal.absNorm P : Real))) = 0) := by
    intro P hP
    exact div_ne_zero (idealEulerNumerator_pos K hP).ne'
      (idealEulerDenominator_pos K hP).ne'
  rw [Real.log_prod hLocal]
  unfold idealMertensProduct idealLcmTowerReserve
  have hDen : forall P,
      Membership.mem (primeIdealsUpToNorm K B) P ->
        Not ((1 - Inv.inv (Ideal.absNorm P : Real)) = 0) := by
    intro P hP
    exact (idealEulerDenominator_pos K hP).ne'
  rw [Real.log_prod hDen]
  have hLogLocal : forall P,
      Membership.mem (primeIdealsUpToNorm K B) P ->
        Real.log ((1 - (Inv.inv (Ideal.absNorm P : Real)) ^
            (Nat.log (Ideal.absNorm P) B + 1)) /
          (1 - Inv.inv (Ideal.absNorm P : Real))) =
        Real.log (1 - (Inv.inv (Ideal.absNorm P : Real)) ^
            (Nat.log (Ideal.absNorm P) B + 1)) -
          Real.log (1 - Inv.inv (Ideal.absNorm P : Real)) := by
    intro P hP
    exact Real.log_div (idealEulerNumerator_pos K hP).ne'
      (idealEulerDenominator_pos K hP).ne'
  rw [Finset.sum_congr rfl hLogLocal]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end

end RobinBV.NumberField
