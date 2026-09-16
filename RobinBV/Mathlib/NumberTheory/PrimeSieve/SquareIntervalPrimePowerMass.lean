/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import RobinBV.Mathlib.NumberTheory.PrimePow.LogCutoff
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalCounts

/-!
# Prime-power mass between consecutive squares

The open interval contains no squares. Its nonprime prime powers therefore
have exponent at least three, yielding a complete cube-root and logarithmic
upper bound. The consumer preserves arbitrary weights between zero and one
and the actual interval prime count.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- Nonprime prime powers in the actual open interval between consecutive squares. -/
noncomputable def squareIntervalCompositePowers (n : Nat) : Finset Nat :=
  (Finset.Ioo (n*n) ((n+1)*(n+1))).filter
    (fun m => Not (Nat.Prime m) /\ IsPrimePow m)

/-- A nonprime prime power in this open interval has exponent at least three. -/
theorem square_interval_prime_power_exponent_ge_three
    {n p k : Nat} (hp : p.Prime) (hk : 0 < k)
    (hlo : n*n < p^k) (hhi : p^k < (n+1)*(n+1))
    (hnp : Not (Nat.Prime (p^k))) : 3 <= k := by
  by_contra hnot
  have hcases : k = 1 \/ k = 2 := by omega
  rcases hcases with h | h
  next =>
    subst k
    exact hnp (by simpa using hp)
  next =>
    subst k
    simp only [pow_two] at hlo hhi
    by_cases hpn : p <= n
    next =>
      have hsq := Nat.pow_le_pow_left hpn 2
      simp only [pow_two] at hsq
      omega
    next =>
      have hnp' : n+1 <= p := by omega
      have hsq := Nat.pow_le_pow_left hnp' 2
      simp only [pow_two] at hsq
      omega

/-- Every such prime power is covered by the complete finite base-exponent rectangle. -/
theorem card_squareIntervalCompositePowers_le (n : Nat) :
    (squareIntervalCompositePowers n).card <=
      Nat.nthRoot 3 ((n+1)*(n+1)) * Nat.log 2 ((n+1)*(n+1)) := by
  let A := (n+1)*(n+1)
  let R := Nat.nthRoot 3 A
  let K := Nat.log 2 A
  let Q : Finset (Prod Nat Nat) :=
    SProd.sprod (Finset.Icc 1 R) (Finset.Icc 1 K)
  have hcover : squareIntervalCompositePowers n <=
      Q.image (fun a => a.1^a.2) := by
    intro m hm
    have hd := Finset.mem_filter.mp hm
    have hi := Finset.mem_Ioo.mp hd.1
    choose p k hp hk hpk using (isPrimePow_nat_iff m).mp hd.2.2
    have hk3 : 3 <= k := by
      apply square_interval_prime_power_exponent_ge_three hp hk
      next => rw [hpk]; exact hi.1
      next => rw [hpk]; exact hi.2
      next => rw [hpk]; exact hd.2.1
    have hpkA : p^k <= A := by rw [hpk]; exact hi.2.le
    have hpR : p <= R :=
      (Nat.le_nthRoot_iff (by decide : Not (3 = 0))).mpr
        ((Nat.pow_le_pow_right hp.pos hk3).trans hpkA)
    have hkK : k <= K :=
      Nat.le_log_of_pow_le (by decide : 1 < 2)
        ((Nat.pow_le_pow_left hp.two_le k).trans hpkA)
    apply Finset.mem_image.mpr
    refine Exists.intro (Prod.mk p k) (And.intro ?_ hpk)
    exact Finset.mem_product.mpr (And.intro
      (Finset.mem_Icc.mpr (And.intro hp.one_le hpR))
      (Finset.mem_Icc.mpr (And.intro hk hkK)))
  calc
    _ <= (Q.image (fun a => a.1^a.2)).card := Finset.card_le_card hcover
    _ <= Q.card := Finset.card_image_le
    _ = R*K := by simp [Q]

/-- The full weighted Mangoldt mass is bounded by actual primes plus the finite power rectangle. -/
theorem square_interval_weighted_mangoldt_le_finite
    (n : Nat) (w : Nat -> Real)
    (hw : forall m, Membership.mem (Finset.Ioo (n*n) ((n+1)*(n+1))) m ->
      0 <= w m /\ w m <= 1) :
    Finset.sum (Finset.Ioo (n*n) ((n+1)*(n+1)))
      (fun m => ArithmeticFunction.vonMangoldt m * w m) <=
    ((squareIntervalPrimes n).card : Real)*Real.log ((n+1)*(n+1) : Nat) +
      (Nat.nthRoot 3 ((n+1)*(n+1)) : Real) *
        (Nat.log 2 ((n+1)*(n+1)) : Real)*Real.log ((n+1)*(n+1) : Nat) := by
  let A : Nat := (n+1)*(n+1)
  let I : Finset Nat := Finset.Ioo (n*n) A
  let f : Nat -> Real := fun m => ArithmeticFunction.vonMangoldt m*w m
  have hA : 1 <= A := by dsimp [A]; nlinarith
  have hlogA : 0 <= Real.log (A : Real) :=
    Real.log_nonneg (by exact_mod_cast hA)
  have hpoint : forall m, Membership.mem I m -> f m <= Real.log (A : Real) := by
    intro m hm
    have hi := Finset.mem_Ioo.mp hm
    have hmpos : 0 < m := by omega
    calc
      f m <= ArithmeticFunction.vonMangoldt m*1 :=
        mul_le_mul_of_nonneg_left (hw m hm).2 ArithmeticFunction.vonMangoldt_nonneg
      _ <= Real.log (m : Real) := by
        simpa only [mul_one] using (ArithmeticFunction.vonMangoldt_le_log (n := m))
      _ <= Real.log (A : Real) :=
        Real.log_le_log (by exact_mod_cast hmpos) (by exact_mod_cast hi.2.le)
  have hprime : I.filter Nat.Prime = squareIntervalPrimes n := by
    ext m
    simp only [I, A, squareIntervalPrimes, Finset.mem_filter,
      Finset.mem_Ioo, Finset.mem_range]
    tauto
  have hnonprime :
      Finset.sum (I.filter (fun m => Not (Nat.Prime m))) f =
        Finset.sum (squareIntervalCompositePowers n) f := by
    have hset : (I.filter (fun m => Not (Nat.Prime m))).filter IsPrimePow =
        squareIntervalCompositePowers n := by
      ext m
      simp [squareIntervalCompositePowers, I, A, and_assoc]
    rw [<- hset]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hp : Nat.Prime m
    next => simp [hp]
    next =>
      by_cases hpp : IsPrimePow m
      next => simp [hp, hpp]
      next => simp [hp, hpp, f, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
  have hP :
      Finset.sum (I.filter Nat.Prime) f <=
        ((squareIntervalPrimes n).card : Real)*Real.log (A : Real) := by
    have h := Finset.sum_le_card_nsmul (I.filter Nat.Prime) f (Real.log (A : Real))
      (fun m hm => hpoint m (Finset.mem_filter.mp hm).1)
    simpa only [hprime, nsmul_eq_mul] using h
  have hS :
      Finset.sum (squareIntervalCompositePowers n) f <=
        (Nat.nthRoot 3 A : Real)*(Nat.log 2 A : Real)*Real.log (A : Real) := by
    have h := Finset.sum_le_card_nsmul (squareIntervalCompositePowers n) f
      (Real.log (A : Real)) (fun m hm => hpoint m (Finset.mem_filter.mp hm).1)
    have hc : ((squareIntervalCompositePowers n).card : Real) <=
        (Nat.nthRoot 3 A : Real)*(Nat.log 2 A : Real) := by
      exact_mod_cast card_squareIntervalCompositePowers_le n
    calc
      _ <= ((squareIntervalCompositePowers n).card : Real)*Real.log (A : Real) := by
        simpa only [nsmul_eq_mul] using h
      _ <= _ := mul_le_mul_of_nonneg_right hc hlogA
  have hsplit := Finset.sum_filter_add_sum_filter_not I Nat.Prime f
  rw [hnonprime] at hsplit
  change Finset.sum I f <= _
  rw [<- hsplit]
  exact _root_.add_le_add hP hS

/-- An explicit cube-root/logarithmic bound for the complete weighted prime-power loss. -/
theorem square_interval_weighted_mangoldt_le
    (n : Nat) (w : Nat -> Real)
    (hw : forall m, Membership.mem (Finset.Ioo (n*n) ((n+1)*(n+1))) m ->
      0 <= w m /\ w m <= 1) :
    Finset.sum (Finset.Ioo (n*n) ((n+1)*(n+1)))
      (fun m => ArithmeticFunction.vonMangoldt m*w m) <=
    ((squareIntervalPrimes n).card : Real)*Real.log ((n+1)*(n+1) : Nat) +
      (((n+1)*(n+1) : Nat) : Real)^(1/3 : Real) *
        (Real.log ((n+1)*(n+1) : Nat))^2 / Real.log 2 := by
  let A : Nat := (n+1)*(n+1)
  let R : Nat := Nat.nthRoot 3 A
  let K : Nat := Nat.log 2 A
  have hA : 1 <= A := by dsimp [A]; nlinarith
  have hlogA : 0 <= Real.log (A : Real) :=
    Real.log_nonneg (by exact_mod_cast hA)
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hR : (R : Real) <= (A : Real)^(1/3 : Real) := by
    have hpow : (R : Real)^(3 : Real) <= (A : Real) := by
      change (R : Real)^((3 : Nat) : Real) <= (A : Real)
      rw [Real.rpow_natCast]
      exact_mod_cast (Nat.pow_nthRoot_le (n := 3) (a := A)
        (Or.inl (by decide : Not (3 = 0))))
    have h := (Real.le_rpow_inv_iff_of_pos
      (Nat.cast_nonneg R) (Nat.cast_nonneg A) (by norm_num : (0 : Real) < 3)).mpr hpow
    simpa only [one_div] using h
  have hK : (K : Real)*Real.log 2 <= Real.log (A : Real) := by
    have h := Nat.log_sub_log_floor_mul_log_bounds (b := 2)
      (by decide) (show (1 : Real) <= A by exact_mod_cast hA)
    simpa only [Nat.floor_natCast, Nat.cast_ofNat] using (sub_nonneg.mp h.1)
  have hRK : (R : Real)*(K : Real)*Real.log (A : Real) <=
      (A : Real)^(1/3 : Real)*(Real.log (A : Real))^2/Real.log 2 := by
    calc
      _ = ((R : Real)*((K : Real)*Real.log 2)*Real.log (A : Real))/Real.log 2 := by
        field_simp
      _ <= ((A : Real)^(1/3 : Real)*Real.log (A : Real)*Real.log (A : Real)) /
          Real.log 2 := by
        simp only [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hlog2.le)
        apply mul_le_mul_of_nonneg_right _ hlogA
        exact mul_le_mul hR hK (mul_nonneg (Nat.cast_nonneg K) hlog2.le)
          (Real.rpow_nonneg (Nat.cast_nonneg A) _)
      _ = _ := by ring
  exact (square_interval_weighted_mangoldt_le_finite n w hw).trans
    (_root_.add_le_add (le_refl _) hRK)

end Nat.PrimeSieve
