import RobinBV.NumberField.Proof.IdealEulerReserve

/-!
# Bounds for the ideal lcm tower reserve

Each local tower loss is bounded by twice its first omitted reciprocal
prime-power term. Summing gives a nonnegative finite envelope for the complete
ideal-lcm tower reserve without any prime-ideal theorem.
-/

namespace RobinBV.NumberField

noncomputable section

private theorem neg_log_one_sub_nonneg_and_le_two_mul
    {x : Real} (hx0 : 0 <= x) (hxHalf : x <= (1 : Real) / 2) :
    And (0 <= -Real.log (1 - x))
      (-Real.log (1 - x) <= 2 * x) := by
  have hOneSubPos : 0 < 1 - x := by linarith
  have hLogNonpos : Real.log (1 - x) <= 0 := by
    exact Real.log_nonpos hOneSubPos.le (by linarith)
  have hLogLower := Real.one_sub_inv_le_log_of_pos hOneSubPos
  have hCancel : x / (1 - x) * (1 - x) = x := by
    field_simp
  have hDiv : x / (1 - x) <= 2 * x := by
    by_contra hNot
    have hGt : 2 * x < x / (1 - x) := lt_of_not_ge hNot
    have hMul := mul_lt_mul_of_pos_right hGt hOneSubPos
    rw [hCancel] at hMul
    nlinarith
  apply And.intro
  next => linarith
  next =>
    calc
      -Real.log (1 - x) <= Inv.inv (1 - x) - 1 := by linarith
      _ = x / (1 - x) := by
        field_simp
        ring
      _ <= 2 * x := hDiv

/-- A local tower loss is nonnegative and at most twice its first omitted
reciprocal prime-power term. -/
theorem idealLocalTowerReserve_nonneg_and_le
    {q : Nat} (hq : 1 < q) (e : Nat) :
    And
      (0 <= -Real.log
        (1 - (Inv.inv (q : Real)) ^ (e + 1)))
      (-Real.log (1 - (Inv.inv (q : Real)) ^ (e + 1)) <=
        2 * (Inv.inv (q : Real)) ^ (e + 1)) := by
  have hqReal : (2 : Real) <= q := by exact_mod_cast hq
  have hqPos : (0 : Real) < q := lt_of_lt_of_le (by norm_num) hqReal
  have hInvNonneg : 0 <= Inv.inv (q : Real) := inv_nonneg.mpr hqPos.le
  have hInvHalf : Inv.inv (q : Real) <= (1 : Real) / 2 := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2) hqReal)
  have hInvOne : Inv.inv (q : Real) <= 1 := by linarith
  have hPowHalf :
      (Inv.inv (q : Real)) ^ (e + 1) <= (1 : Real) / 2 := by
    exact (pow_le_of_le_one hInvNonneg hInvOne (Nat.succ_ne_zero e)).trans
      hInvHalf
  exact neg_log_one_sub_nonneg_and_le_two_mul
    (pow_nonneg hInvNonneg (e + 1)) hPowHalf

/-- The complete ideal-lcm tower reserve is nonnegative. -/
theorem idealLcmTowerReserve_nonneg
    (K : Type*) [Field K] [NumberField K] (B : Nat) :
    0 <= idealLcmTowerReserve K B := by
  unfold idealLcmTowerReserve
  apply Finset.sum_nonneg
  intro P hP
  exact (idealLocalTowerReserve_nonneg_and_le
    (one_lt_absNorm_of_mem_primeIdealsUpToNorm K hP)
    (Nat.log (Ideal.absNorm P) B)).1

/-- The complete tower reserve is bounded by twice the sum of its first
omitted reciprocal prime-ideal powers. -/
theorem idealLcmTowerReserve_le_two_mul_sum
    (K : Type*) [Field K] [NumberField K] (B : Nat) :
    idealLcmTowerReserve K B <=
      2 * (primeIdealsUpToNorm K B).sum
        (fun P =>
          (Inv.inv (Ideal.absNorm P : Real)) ^
            (Nat.log (Ideal.absNorm P) B + 1)) := by
  unfold idealLcmTowerReserve
  calc
    _ <= (primeIdealsUpToNorm K B).sum
        (fun P =>
          2 * (Inv.inv (Ideal.absNorm P : Real)) ^
            (Nat.log (Ideal.absNorm P) B + 1)) := by
      apply Finset.sum_le_sum
      intro P hP
      exact (idealLocalTowerReserve_nonneg_and_le
        (one_lt_absNorm_of_mem_primeIdealsUpToNorm K hP)
        (Nat.log (Ideal.absNorm P) B)).2
    _ = 2 * (primeIdealsUpToNorm K B).sum
        (fun P =>
          (Inv.inv (Ideal.absNorm P : Real)) ^
            (Nat.log (Ideal.absNorm P) B + 1)) := by
      rw [Finset.mul_sum]

end

end RobinBV.NumberField
