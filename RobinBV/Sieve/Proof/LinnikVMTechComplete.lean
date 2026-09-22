/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMTechBox

/-!
# Explicit max-fiber fallback for Vinogradov's technical estimate

This module reconnects the exact difference-range and kernel estimates to the
original bilinear exponential sum. It retains both Holder losses, both
Vinogradov mean-value factors, and the complete rational-approximation packet.
The first grouping uses a maximum-fiber bound followed by support Holder, so
this is a valid explicit fallback, not the sharp Theorem 24.7 exponent.
-/

open Complex

noncomputable def linnikVMTechDoubleSum
    {k : Nat} (alpha : Fin k -> Real) (L X : Nat) : Complex :=
  Finset.univ.sum (fun l : Fin L =>
    Finset.univ.sum (fun m : Fin X =>
      Complex.exp (Complex.I *
        (linnikVMTechPolynomialPhase
          (fun j => 2 * Real.pi * alpha j) (l.val * m.val) : Complex))))

noncomputable def linnikVMTechOuterWeight
    {k : Nat} (alpha : Fin k -> Real) (L : Nat)
    (h : Fin k -> Int) : Complex :=
  Finset.univ.sum (fun l : Fin L =>
    Complex.exp (Complex.I *
      (Finset.univ.sum (fun j : Fin k =>
        (2 * Real.pi * alpha j) *
          (l.val : Real) ^ (j.val + 1) * (h j : Real)) : Real) : Complex))

theorem linnik_vmtech_outer_moment_sum_le
    (k r X L : Nat) (alpha : Fin k -> Real) :
    Finset.univ.sum (fun l : Fin L =>
        norm (Finset.univ.sum (fun m : Fin X =>
          Complex.exp (Complex.I *
            (linnikVMTechPolynomialPhase
              (fun j => 2 * Real.pi * alpha j)
              (l.val * m.val) : Complex)))) ^ (2 * (k * r))) <=
      (Finset.vinogradovMeanValue k (k * r) X : Real) *
        (linnikVMTechDifferenceRange k r X).sum (fun h =>
          norm (linnikVMTechOuterWeight alpha L h)) := by
  let pairs : Finset
      (Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X)) :=
    (Finset.univ : Finset (Fin (k * r) -> Fin X)).product Finset.univ
  let diff : Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X) ->
      Fin k -> Int := fun uv j =>
    linnikVMTechPowerDifference (fun x : Fin X => x.val)
      uv.fst uv.snd j
  have hidentity :
      ((Finset.univ.sum (fun l : Fin L =>
          norm (Finset.univ.sum (fun m : Fin X =>
            Complex.exp (Complex.I *
              (linnikVMTechPolynomialPhase
                (fun j => 2 * Real.pi * alpha j)
                (l.val * m.val) : Complex)))) ^
              (2 * (k * r))) : Real) : Complex) =
        pairs.sum (fun uv =>
          linnikVMTechOuterWeight alpha L (diff uv)) := by
    have hcast :
        ((Finset.univ.sum (fun l : Fin L =>
            norm (Finset.univ.sum (fun m : Fin X =>
              Complex.exp (Complex.I *
                (linnikVMTechPolynomialPhase
                  (fun j => 2 * Real.pi * alpha j)
                  (l.val * m.val) : Complex)))) ^
                (2 * (k * r))) : Real) : Complex) =
          Finset.univ.sum (fun l : Fin L =>
            ((norm (Finset.univ.sum (fun m : Fin X =>
              Complex.exp (Complex.I *
                (linnikVMTechPolynomialPhase
                  (fun j => 2 * Real.pi * alpha j)
                  (l.val * m.val) : Complex)))) ^
                (2 * (k * r)) : Real) : Complex)) := by
      push_cast
      rfl
    rw [hcast]
    simp_rw [linnik_vmtech_polynomial_even_moment_expansion]
    let term : Fin L ->
        Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X) ->
        Complex := fun l uv =>
      Complex.exp (Complex.I * Finset.univ.sum (fun j : Fin k =>
        ((2 * Real.pi * alpha j : Real) : Complex) *
          (l.val : Complex) ^ (j.val + 1) *
            (linnikVMTechPowerDifferenceReal
              (fun x : Fin X => x.val) uv.fst uv.snd j : Complex)))
    change Finset.univ.sum (fun l : Fin L =>
        Finset.univ.sum (fun u : Fin (k * r) -> Fin X =>
          Finset.univ.sum (fun v : Fin (k * r) -> Fin X =>
            term l (u, v)))) =
      pairs.sum (fun uv => linnikVMTechOuterWeight alpha L (diff uv))
    rw [show Finset.univ.sum (fun l : Fin L =>
          Finset.univ.sum (fun u : Fin (k * r) -> Fin X =>
            Finset.univ.sum (fun v : Fin (k * r) -> Fin X =>
              term l (u, v)))) =
        Finset.univ.sum (fun l : Fin L => pairs.sum (term l)) by
      unfold pairs
      apply Finset.sum_congr rfl
      intro l hl
      exact (Finset.sum_product
        (s := (Finset.univ : Finset (Fin (k * r) -> Fin X)))
        (t := (Finset.univ : Finset (Fin (k * r) -> Fin X)))
        (f := term l)).symm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro uv huv
    unfold linnikVMTechOuterWeight diff
    apply Finset.sum_congr rfl
    intro l hl
    congr 2
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw [show (linnikVMTechPowerDifferenceReal
        (fun x : Fin X => x.val) uv.fst uv.snd j : Complex) =
      ((linnikVMTechPowerDifference
        (fun x : Fin X => x.val) uv.fst uv.snd j : Real) : Complex) by
      exact congrArg (fun x : Real => (x : Complex))
        (linnikVMTechPowerDifference_cast
          (fun x : Fin X => x.val) uv.fst uv.snd j).symm]
    norm_num
  have hnonneg : 0 <= Finset.univ.sum (fun l : Fin L =>
      norm (Finset.univ.sum (fun m : Fin X =>
        Complex.exp (Complex.I *
          (linnikVMTechPolynomialPhase
            (fun j => 2 * Real.pi * alpha j)
            (l.val * m.val) : Complex)))) ^ (2 * (k * r))) := by
    apply Finset.sum_nonneg
    intro l hl
    positivity
  calc
    Finset.univ.sum (fun l : Fin L =>
        norm (Finset.univ.sum (fun m : Fin X =>
          Complex.exp (Complex.I *
            (linnikVMTechPolynomialPhase
              (fun j => 2 * Real.pi * alpha j)
              (l.val * m.val) : Complex)))) ^ (2 * (k * r))) =
      norm (((Finset.univ.sum (fun l : Fin L =>
        norm (Finset.univ.sum (fun m : Fin X =>
          Complex.exp (Complex.I *
            (linnikVMTechPolynomialPhase
              (fun j => 2 * Real.pi * alpha j)
              (l.val * m.val) : Complex)))) ^
            (2 * (k * r))) : Real) : Complex)) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = norm (pairs.sum (fun uv =>
        linnikVMTechOuterWeight alpha L (diff uv))) := by rw [hidentity]
    _ <= (Finset.vinogradovMeanValue k (k * r) X : Real) *
        (linnikVMTechDifferenceRange k r X).sum (fun h =>
          norm (linnikVMTechOuterWeight alpha L h)) := by
      simpa only [pairs, diff] using
        (linnik_vmtech_pair_sum_norm_le_vmvt_mul_sum_norm
          k r X (linnikVMTechOuterWeight alpha L))

theorem linnik_vmtech_outer_weight_moment
    {k : Nat} (alpha : Fin k -> Real) (L s : Nat)
    (h : Fin k -> Int) :
    norm (linnikVMTechOuterWeight alpha L h) ^ (2 * s) =
      linnikVMTechDifferenceMoment alpha L s h := by
  unfold linnikVMTechOuterWeight linnikVMTechDifferenceMoment
  congr 2
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem linnik_vmtech_difference_weight_holder
    (k r X L : Nat) (alpha : Fin k -> Real)
    (hkr : 0 < k * r) :
    ((linnikVMTechDifferenceRange k r X).sum (fun h =>
        norm (linnikVMTechOuterWeight alpha L h))) ^ (2 * (k * r)) <=
      ((linnikVMTechDifferenceRange k r X).card : Real) ^
          (2 * (k * r) - 1) *
        (linnikVMTechDifferenceRange k r X).sum
          (linnikVMTechDifferenceMoment alpha L (k * r)) := by
  have hexponent : 2 * (k * r) - 1 + 1 = 2 * (k * r) :=
    Nat.sub_add_cancel (by omega)
  have hholder := pow_sum_le_card_mul_sum_pow
    (s := linnikVMTechDifferenceRange k r X)
    (f := fun h => norm (linnikVMTechOuterWeight alpha L h))
    (fun h hh => norm_nonneg (linnikVMTechOuterWeight alpha L h))
    (2 * (k * r) - 1)
  simpa only [hexponent,
    linnik_vmtech_outer_weight_moment] using hholder

theorem linnik_vmtech_outer_moment_power_le_envelope
    (k r X L : Nat) (alpha theta : Fin k -> Real)
    (a q : Fin k -> Nat)
    (hkr : 0 < k * r)
    (hq : forall j, 0 < q j)
    (hcop : forall j, Nat.Coprime (a j) (q j))
    (htheta : forall j, abs (theta j) <= 1)
    (halpha : forall j,
      alpha j = (a j : Real) / q j + theta j / (q j : Real) ^ 2) :
    (Finset.univ.sum (fun l : Fin L =>
        norm (Finset.univ.sum (fun m : Fin X =>
          Complex.exp (Complex.I *
            (linnikVMTechPolynomialPhase
              (fun j => 2 * Real.pi * alpha j)
              (l.val * m.val) : Complex)))) ^ (2 * (k * r)))) ^
        (2 * (k * r)) <=
      (Finset.vinogradovMeanValue k (k * r) X : Real) ^
          (2 * (k * r)) *
        (((linnikVMTechDifferenceRange k r X).card : Real) ^
            (2 * (k * r) - 1) *
          ((Finset.vinogradovMeanValue k (k * r) L : Real) *
            ((2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
              48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
                (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
                  (k * r * L ^ (j.val + 1) + 1) +
                  (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j))))) := by
  let A : Real := Finset.univ.sum (fun l : Fin L =>
    norm (Finset.univ.sum (fun m : Fin X =>
      Complex.exp (Complex.I *
        (linnikVMTechPolynomialPhase
          (fun j => 2 * Real.pi * alpha j)
          (l.val * m.val) : Complex)))) ^ (2 * (k * r)))
  let V : Real := Finset.vinogradovMeanValue k (k * r) X
  let W : Real := (linnikVMTechDifferenceRange k r X).sum (fun h =>
    norm (linnikVMTechOuterWeight alpha L h))
  have houter : A <= V * W := by
    exact linnik_vmtech_outer_moment_sum_le k r X L alpha
  have hpow : A ^ (2 * (k * r)) <= (V * W) ^ (2 * (k * r)) := by
    gcongr
  have hholder := linnik_vmtech_difference_weight_holder
    k r X L alpha hkr
  have hmoment := linnik_vmtech_difference_moment_sum_le_envelope
    k r X L alpha theta a q hq hcop htheta halpha
  calc
    A ^ (2 * (k * r)) <= (V * W) ^ (2 * (k * r)) := hpow
    _ = V ^ (2 * (k * r)) * W ^ (2 * (k * r)) := by rw [mul_pow]
    _ <= V ^ (2 * (k * r)) *
        (((linnikVMTechDifferenceRange k r X).card : Real) ^
            (2 * (k * r) - 1) *
          (linnikVMTechDifferenceRange k r X).sum
            (linnikVMTechDifferenceMoment alpha L (k * r))) := by
      exact mul_le_mul_of_nonneg_left hholder (by positivity)
    _ <= V ^ (2 * (k * r)) *
        (((linnikVMTechDifferenceRange k r X).card : Real) ^
            (2 * (k * r) - 1) *
          ((Finset.vinogradovMeanValue k (k * r) L : Real) *
            ((2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
              48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
                (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
                  (k * r * L ^ (j.val + 1) + 1) +
                  (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j))))) := by
      gcongr

theorem linnikVMTechDifferenceRange_card_le_box
    (k r X : Nat) :
    (linnikVMTechDifferenceRange k r X).card <=
      Finset.univ.prod (fun j : Fin k =>
        2 * (k * r * X ^ (j.val + 1)) + 1) := by
  have hinj :
      Fintype.card {h : Fin k -> Int // Membership.mem
          (linnikVMTechDifferenceRange k r X) h} <=
        Fintype.card (linnikVMTechDifferenceBox k r X) :=
    Fintype.card_le_of_injective
      (linnikVMTechDifferenceBoxOfRange k r X)
      (linnikVMTechDifferenceBoxOfRange_injective k r X)
  calc
    (linnikVMTechDifferenceRange k r X).card =
        Fintype.card {h : Fin k -> Int // Membership.mem
          (linnikVMTechDifferenceRange k r X) h} := by simp
    _ <= Fintype.card (linnikVMTechDifferenceBox k r X) := hinj
    _ = Finset.univ.prod (fun j : Fin k =>
        2 * (k * r * X ^ (j.val + 1)) + 1) := by
      simp only [linnikVMTechDifferenceBox, Fintype.card_pi,
        Fintype.card_coe]
      apply Finset.prod_congr rfl
      intro j hj
      rw [Int.card_Icc]
      have heq :
          (k : Int) * r * (X : Int) ^ (j.val + 1) + 1 +
              (k : Int) * r * (X : Int) ^ (j.val + 1) =
            ((2 * (k * r * X ^ (j.val + 1)) + 1 : Nat) : Int) := by
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_one, Nat.cast_ofNat]
        ring
      rw [sub_neg_eq_add, heq, Int.toNat_natCast]

theorem linnik_vmtech_outer_moment_power_le_explicit
    (k r X L : Nat) (alpha theta : Fin k -> Real)
    (a q : Fin k -> Nat)
    (hkr : 0 < k * r)
    (hq : forall j, 0 < q j)
    (hcop : forall j, Nat.Coprime (a j) (q j))
    (htheta : forall j, abs (theta j) <= 1)
    (halpha : forall j,
      alpha j = (a j : Real) / q j + theta j / (q j : Real) ^ 2) :
    (Finset.univ.sum (fun l : Fin L =>
        norm (Finset.univ.sum (fun m : Fin X =>
          Complex.exp (Complex.I *
            (linnikVMTechPolynomialPhase
              (fun j => 2 * Real.pi * alpha j)
              (l.val * m.val) : Complex)))) ^ (2 * (k * r)))) ^
        (2 * (k * r)) <=
      (Finset.vinogradovMeanValue k (k * r) X : Real) ^
          (2 * (k * r)) *
        (((Finset.univ.prod (fun j : Fin k =>
            2 * (k * r * X ^ (j.val + 1)) + 1) : Nat) : Real) ^
            (2 * (k * r) - 1) *
          ((Finset.vinogradovMeanValue k (k * r) L : Real) *
            ((2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
              48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
                (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
                  (k * r * L ^ (j.val + 1) + 1) +
                  (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j))))) := by
  have hbase := linnik_vmtech_outer_moment_power_le_envelope
    k r X L alpha theta a q hkr hq hcop htheta halpha
  have hcard :
      ((linnikVMTechDifferenceRange k r X).card : Real) <=
        ((Finset.univ.prod (fun j : Fin k =>
          2 * (k * r * X ^ (j.val + 1)) + 1) : Nat) : Real) := by
    exact_mod_cast linnikVMTechDifferenceRange_card_le_box k r X
  exact hbase.trans (by gcongr)

theorem linnik_vmtech_double_sum_power_le_explicit
    (k r X L : Nat) (alpha theta : Fin k -> Real)
    (a q : Fin k -> Nat)
    (hkr : 0 < k * r)
    (hq : forall j, 0 < q j)
    (hcop : forall j, Nat.Coprime (a j) (q j))
    (htheta : forall j, abs (theta j) <= 1)
    (halpha : forall j,
      alpha j = (a j : Real) / q j + theta j / (q j : Real) ^ 2) :
    norm (linnikVMTechDoubleSum alpha L X) ^
        ((2 * (k * r)) * (2 * (k * r))) <=
      ((L : Real) ^ (2 * (k * r) - 1)) ^ (2 * (k * r)) *
        ((Finset.vinogradovMeanValue k (k * r) X : Real) ^
            (2 * (k * r)) *
          (((Finset.univ.prod (fun j : Fin k =>
              2 * (k * r * X ^ (j.val + 1)) + 1) : Nat) : Real) ^
              (2 * (k * r) - 1) *
            ((Finset.vinogradovMeanValue k (k * r) L : Real) *
              ((2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
                48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
                  (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
                    (k * r * L ^ (j.val + 1) + 1) +
                    (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j)))))) := by
  let A : Real := Finset.univ.sum (fun l : Fin L =>
    norm (Finset.univ.sum (fun m : Fin X =>
      Complex.exp (Complex.I *
        (linnikVMTechPolynomialPhase
          (fun j => 2 * Real.pi * alpha j)
          (l.val * m.val) : Complex)))) ^ (2 * (k * r)))
  have houter :
      norm (linnikVMTechDoubleSum alpha L X) ^ (2 * (k * r)) <=
        (L : Real) ^ (2 * (k * r) - 1) * A := by
    simpa only [linnikVMTechDoubleSum, A, Fintype.card_fin] using
      (linnik_vmtech_outer_holder (I := Fin L) (J := Fin X)
        (fun l m => Complex.exp (Complex.I *
          (linnikVMTechPolynomialPhase
            (fun j => 2 * Real.pi * alpha j)
            (l.val * m.val) : Complex))) (k * r) hkr)
  have houterPow :
      (norm (linnikVMTechDoubleSum alpha L X) ^ (2 * (k * r))) ^
          (2 * (k * r)) <=
        ((L : Real) ^ (2 * (k * r) - 1) * A) ^ (2 * (k * r)) := by
    gcongr
  have hexplicit := linnik_vmtech_outer_moment_power_le_explicit
    k r X L alpha theta a q hkr hq hcop htheta halpha
  calc
    norm (linnikVMTechDoubleSum alpha L X) ^
        ((2 * (k * r)) * (2 * (k * r))) =
      (norm (linnikVMTechDoubleSum alpha L X) ^ (2 * (k * r))) ^
        (2 * (k * r)) := by rw [pow_mul]
    _ <= ((L : Real) ^ (2 * (k * r) - 1) * A) ^
        (2 * (k * r)) := houterPow
    _ = ((L : Real) ^ (2 * (k * r) - 1)) ^ (2 * (k * r)) *
        A ^ (2 * (k * r)) := by rw [mul_pow]
    _ <= ((L : Real) ^ (2 * (k * r) - 1)) ^ (2 * (k * r)) *
        ((Finset.vinogradovMeanValue k (k * r) X : Real) ^
            (2 * (k * r)) *
          (((Finset.univ.prod (fun j : Fin k =>
              2 * (k * r * X ^ (j.val + 1)) + 1) : Nat) : Real) ^
              (2 * (k * r) - 1) *
            ((Finset.vinogradovMeanValue k (k * r) L : Real) *
              ((2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
                48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
                  (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
                    (k * r * L ^ (j.val + 1) + 1) +
                    (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j)))))) := by
      exact mul_le_mul_of_nonneg_left hexplicit (by positivity)
