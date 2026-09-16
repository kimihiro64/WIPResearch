/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.LSeries.TruncatedMoebius

/-!
# Unit coefficients with an independent normalization exponent

Choose epsilon=eta/(a+b), independently of the mollifier cutoff b, and
divide the retained coefficients by C_epsilon*T^eta. The full support
satisfies r<=floor(T^b)*floor(T^a)<=T^(a+b), so coefficients have norm
at most one. The additional threshold pays the complete loss and gives
Type-I level T^(-2*b) and Type-II level T^(-2*eta).

Thus the separate length-normalized losses 2*b/a and 2*eta/b can both
be made small. Positivity, both cutoffs and every threshold are retained.
No zero-density, large-value energy or prime-count estimate is assumed.
-/

set_option autoImplicit false

namespace LSeries

/-- The explicit divisor-growth constant, used only with positive epsilon. -/
noncomputable def moebiusSubpowerConstant (epsilon : Real) : Real :=
  (((2 : Real)^epsilon)/((2 : Real)^epsilon-1))^(Nat.ceil ((2 : Real)^(1/epsilon)))

/-- The positive height normalization under the admissible parameter hypotheses. -/
noncomputable def moebiusHeightScale (a b eta T : Real) : Real :=
  moebiusSubpowerConstant (eta/(a+b))*T^eta

/-- Divide every actual truncated coefficient by the same real scalar. -/
noncomputable def normalizedTruncatedMoebius (H L : Nat) (Z : Real) (n : Nat) : Complex :=
  truncatedMoebius H L n/(Z : Complex)

/-- The explicit coefficient reserve is at least one for positive epsilon. -/
theorem one_le_moebiusSubpowerConstant {epsilon : Real} (hepsilon : 0 < epsilon) :
    1 <= moebiusSubpowerConstant epsilon := by
  have hq : 1 < (2 : Real)^epsilon := Real.one_lt_rpow (by norm_num) hepsilon
  have hA := Real.one_le_geometric_ratio hq
  have hh := Real.one_le_rpow hA (Nat.cast_nonneg (Nat.ceil ((2 : Real)^(1/epsilon))))
  simpa only [moebiusSubpowerConstant, Real.rpow_natCast] using hh

/-- The height normalization is at least one on the admissible domain. -/
theorem one_le_moebiusHeightScale {a b eta T : Real} (hb : 0 < b) (hba : b < a) (heta : 0 < eta)
    (hT : 1 <= T) :
    1 <= moebiusHeightScale a b eta T := by
  have hepsilon : 0 < eta/(a+b) := div_pos heta (by linarith)
  have hC := one_le_moebiusSubpowerConstant hepsilon
  have ht := Real.one_le_rpow hT (le_of_lt heta)
  change 1 <= moebiusSubpowerConstant (eta/(a+b))*T^eta
  simpa only [one_mul] using mul_le_mul hC ht zero_le_one (le_trans zero_le_one hC)

/-- The entire positive coefficient support is bounded by the height scale. -/
theorem norm_truncatedMoebius_le_heightScale {a b eta T : Real} (hb : 0 < b) (hba : b < a) (heta : 0 < eta)
    (hT : 1 <= T) {n : Nat} (hn : 0 < n)
    (hnTop : n <= Nat.floor (T^b)*Nat.floor (T^a)) :
    norm (truncatedMoebius (Nat.floor (T^b)) (Nat.floor (T^a)) n) <=
      moebiusHeightScale a b eta T := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hab : 0 < a+b := by linarith
  have hepsilon : 0 < eta/(a+b) := div_pos heta hab
  have hC := one_le_moebiusSubpowerConstant hepsilon
  have hHL : ((Nat.floor (T^b)*Nat.floor (T^a) : Nat) : Real) <= T^(a+b) := by
    rw [Nat.cast_mul]
    calc
      _ <= T^b*T^a := mul_le_mul
        (Nat.floor_le (Real.rpow_nonneg (le_of_lt hTpos) _))
        (Nat.floor_le (Real.rpow_nonneg (le_of_lt hTpos) _))
        (Nat.cast_nonneg _) (Real.rpow_nonneg (le_of_lt hTpos) _)
      _ = T^(a+b) := by rw [<- Real.rpow_add hTpos, add_comm b a]
  have hnT : (n : Real) <= T^(a+b) :=
    (show (n : Real) <= ((Nat.floor (T^b)*Nat.floor (T^a) : Nat) : Real) by
      exact_mod_cast hnTop).trans hHL
  have hpower : (n : Real)^(eta/(a+b)) <= T^eta := by
    calc
      _ <= (T^(a+b))^(eta/(a+b)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hnT (le_of_lt hepsilon)
      _ = T^eta := by
        rw [<- Real.rpow_mul (le_of_lt hTpos)]
        congr 1
        field_simp
  calc
    _ <= moebiusSubpowerConstant (eta/(a+b))*(n : Real)^(eta/(a+b)) :=
      norm_truncatedMoebius_le_rpow_explicit _ _ (by omega) hepsilon
    _ <= moebiusSubpowerConstant (eta/(a+b))*T^eta :=
      mul_le_mul_of_nonneg_left hpower (le_trans zero_le_one hC)
    _ = moebiusHeightScale a b eta T := rfl

/-- Normalized coefficients have norm at most one on the full finite support. -/
theorem norm_normalizedTruncatedMoebius_le_one {a b eta T : Real} (hb : 0 < b) (hba : b < a) (heta : 0 < eta)
    (hT : 1 <= T) {n : Nat} (hn : 0 < n)
    (hnTop : n <= Nat.floor (T^b)*Nat.floor (T^a)) :
    norm (normalizedTruncatedMoebius (Nat.floor (T^b)) (Nat.floor (T^a))
      (moebiusHeightScale a b eta T) n) <= 1 := by
  have hZ : 0 < moebiusHeightScale a b eta T :=
    lt_of_lt_of_le zero_lt_one (one_le_moebiusHeightScale hb hba heta hT)
  rw [normalizedTruncatedMoebius, norm_div, Complex.norm_of_nonneg (le_of_lt hZ)]
  have hh := div_le_div_of_nonneg_right
    (norm_truncatedMoebius_le_heightScale hb hba heta hT hn hnTop) (le_of_lt hZ)
  rw [div_self (ne_of_gt hZ)] at hh
  exact hh

/-- The additional threshold pays the complete coefficient-normalization loss. -/
theorem moebiusHeightScale_mul_detection_level_le {a b eta T : Real}
    (hb : 0 < b) (hba : b < a) (heta : 0 < eta) (hT : 1 <= T)
    (hExtra : (2*moebiusSubpowerConstant (eta/(a+b)))^(1/eta) <= T) :
    moebiusHeightScale a b eta T*T^(-2*eta) <= (1 : Real)/2 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hepsilon : 0 < eta/(a+b) := div_pos heta (by linarith)
  have hC := one_le_moebiusSubpowerConstant hepsilon
  have hC0 : 0 <= 2*moebiusSubpowerConstant (eta/(a+b)) := by linarith
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hC0 _) hExtra (le_of_lt heta)
  rw [<- Real.rpow_mul hC0, show (1/eta)*eta = 1 by field_simp, Real.rpow_one] at hh
  have hmul := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (le_of_lt hTpos) (-eta))
  rw [<- Real.rpow_add hTpos, add_neg_cancel, Real.rpow_zero] at hmul
  have he : moebiusHeightScale a b eta T*T^(-2*eta) =
      moebiusSubpowerConstant (eta/(a+b))*T^(-eta) := by
    rw [moebiusHeightScale, mul_assoc, <- Real.rpow_add hTpos]
    congr 1
    congr 1
    ring
  rw [he]
  linarith

/-- The full normalized residual norm equals the original norm divided by its scale. -/
theorem norm_sum_normalizedTruncatedMoebius (H L : Nat) {Z : Real} (hZ : 0 <= Z)
    (s : Complex) :
    norm ((Finset.range (H*L-H)).sum (fun j =>
      normalizedTruncatedMoebius H L Z (H+j+1)*((H+j+1 : Nat) : Complex)^(-s))) =
    norm ((Finset.range (H*L-H)).sum (fun j =>
      truncatedMoebius H L (H+j+1)*((H+j+1 : Nat) : Complex)^(-s)))/Z := by
  simp only [normalizedTruncatedMoebius, div_mul_eq_mul_div]
  rw [<- Finset.sum_div, norm_div, Complex.norm_of_nonneg hZ]

/-- The branches have independent detection levels and unit-bounded coefficients. -/
theorem dirichlet_sum_height_or_unit_moebius_large
    {C T a b eta : Real} (hC : 1 <= C) (hb : 0 < b) (hba : b < a) (heta : 0 < eta) (ha : a < 1)
    (hbSmall : b < (1/8 : Real))
    (hT : max (max 1 (max (C^(1/((1/4 : Real)-2*b))) ((4 : Real)^(1/b))))
      ((2*moebiusSubpowerConstant (eta/(a+b)))^(1/eta)) <= T)
    {s : Complex} (hs : 0 <= s.re)
    (hsmall : norm ((Finset.range (Nat.floor T)).sum
      (fun j => ((j+1 : Nat) : Complex)^(-s))) <= C*T^(-(1/4 : Real))) :
    (forall n : Nat, 0 < n -> n <= Nat.floor (T^b)*Nat.floor (T^a) ->
      norm (normalizedTruncatedMoebius (Nat.floor (T^b)) (Nat.floor (T^a))
        (moebiusHeightScale a b eta T) n) <= 1) /\
    (T^(-2*b) <= norm ((Finset.range (Nat.floor T-Nat.floor (T^a))).sum
      (fun j => ((Nat.floor (T^a)+j+1 : Nat) : Complex)^(-s))) \/
    T^(-2*eta) <= norm
      ((Finset.range (Nat.floor (T^b)*Nat.floor (T^a)-Nat.floor (T^b))).sum
        (fun j => normalizedTruncatedMoebius (Nat.floor (T^b)) (Nat.floor (T^a))
          (moebiusHeightScale a b eta T) (Nat.floor (T^b)+j+1)*
          ((Nat.floor (T^b)+j+1 : Nat) : Complex)^(-s)))) := by
  have hOld : max 1 (max (C^(1/((1/4 : Real)-2*b))) ((4 : Real)^(1/b))) <= T :=
    (le_max_left _ _).trans hT
  have hExtra : (2*moebiusSubpowerConstant (eta/(a+b)))^(1/eta) <= T :=
    (le_max_right _ _).trans hT
  have hT1 : 1 <= T := (le_max_left _ _).trans hOld
  have hZ : 0 < moebiusHeightScale a b eta T :=
    lt_of_lt_of_le zero_lt_one (one_le_moebiusHeightScale hb hba heta hT1)
  constructor
  next =>
    intro n hn hnTop
    exact norm_normalizedTruncatedMoebius_le_one hb hba heta hT1 hn hnTop
  next =>
    cases dirichlet_sum_height_or_moebius_residual_large hC hb hba ha hbSmall hOld hs hsmall with
    | inl hlarge => exact Or.inl hlarge
    | inr hlarge =>
      apply Or.inr
      rw [norm_sum_normalizedTruncatedMoebius _ _ (le_of_lt hZ)]
      calc
        T^(-2*eta) =
            (moebiusHeightScale a b eta T*T^(-2*eta))/moebiusHeightScale a b eta T := by
          field_simp
        _ <= ((1 : Real)/2)/moebiusHeightScale a b eta T :=
          div_le_div_of_nonneg_right
            (moebiusHeightScale_mul_detection_level_le hb hba heta hT1 hExtra) (le_of_lt hZ)
        _ <= _ := div_le_div_of_nonneg_right hlarge (le_of_lt hZ)

end LSeries
