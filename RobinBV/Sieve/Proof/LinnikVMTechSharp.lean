/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikVMTechComplete

/-!
# Sharp Holder order for Vinogradov's technical estimate

The source proof applies its second Holder inequality over the complete pair
of `b`-tuples before grouping by the power-difference vector. This order keeps
one first-stage VMVT factor and introduces no independent support-cardinality
loss. The module supplies that exact replacement for the max-fiber fallback.
-/

open Complex

theorem linnik_vmtech_outer_moment_sum_eq_norm_pair_sum
    (k r X L : Nat) (alpha : Fin k -> Real) :
    Finset.univ.sum (fun l : Fin L =>
        norm (Finset.univ.sum (fun m : Fin X =>
          Complex.exp (Complex.I *
            (linnikVMTechPolynomialPhase
              (fun j => 2 * Real.pi * alpha j)
              (l.val * m.val) : Complex)))) ^ (2 * (k * r))) =
      norm (Finset.univ.sum (fun uv :
          Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X) =>
        linnikVMTechOuterWeight alpha L (fun j =>
          linnikVMTechPowerDifference (fun x : Fin X => x.val)
            uv.fst uv.snd j))) := by
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
    _ = norm (Finset.univ.sum (fun uv :
          Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X) =>
        linnikVMTechOuterWeight alpha L (fun j =>
          linnikVMTechPowerDifference (fun x : Fin X => x.val)
            uv.fst uv.snd j))) := by
      unfold pairs diff
      have hpairs :
          (Finset.univ : Finset (Fin (k * r) -> Fin X)).product
              (Finset.univ : Finset (Fin (k * r) -> Fin X)) =
            (Finset.univ : Finset
              (Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X))) := by
        exact Finset.univ_product_univ
      rw [hpairs]

theorem linnik_vmtech_outer_second_holder
    (k r X L : Nat) (alpha : Fin k -> Real) (hkr : 0 < k * r) :
    (Finset.univ.sum (fun l : Fin L =>
        norm (Finset.univ.sum (fun m : Fin X =>
          Complex.exp (Complex.I *
            (linnikVMTechPolynomialPhase
              (fun j => 2 * Real.pi * alpha j)
              (l.val * m.val) : Complex)))) ^ (2 * (k * r)))) ^
        (2 * (k * r)) <=
      Fintype.card
          (Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X)) ^
            (2 * (k * r) - 1) *
        Finset.univ.sum (fun uv :
          Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X) =>
          norm (linnikVMTechOuterWeight alpha L (fun j =>
            linnikVMTechPowerDifference (fun x : Fin X => x.val)
              uv.fst uv.snd j)) ^ (2 * (k * r))) := by
  rw [linnik_vmtech_outer_moment_sum_eq_norm_pair_sum]
  exact Finset.norm_sum_pow_le_card_pow_mul_sum_norm_pow
    (fun uv : Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X) =>
      linnikVMTechOuterWeight alpha L (fun j =>
        linnikVMTechPowerDifference (fun x : Fin X => x.val)
          uv.fst uv.snd j))
    (2 * (k * r)) (Nat.mul_pos (by omega) hkr)

theorem linnik_vmtech_pair_moment_sum_le_vmvt
    (k r X L : Nat) (alpha : Fin k -> Real) :
    Finset.univ.sum (fun uv :
        Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X) =>
      norm (linnikVMTechOuterWeight alpha L (fun j =>
        linnikVMTechPowerDifference (fun x : Fin X => x.val)
          uv.fst uv.snd j)) ^ (2 * (k * r))) <=
      (Finset.vinogradovMeanValue k (k * r) X : Real) *
        (linnikVMTechDifferenceRange k r X).sum
          (linnikVMTechDifferenceMoment alpha L (k * r)) := by
  have hbound := linnik_vmtech_pair_sum_le_vmvt_mul_difference_sum
    k r X (linnikVMTechDifferenceMoment alpha L (k * r))
    (fun h => linnikVMTechDifferenceMoment_nonneg alpha L (k * r) h)
  have hpairs :
      (Finset.univ : Finset (Fin (k * r) -> Fin X)).product
          (Finset.univ : Finset (Fin (k * r) -> Fin X)) =
        (Finset.univ : Finset
          (Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X))) := by
    exact Finset.univ_product_univ
  rw [hpairs] at hbound
  simpa only [linnik_vmtech_outer_weight_moment] using hbound

theorem linnik_vmtech_pair_domain_card
    (k r X : Nat) :
    Fintype.card (Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X)) =
      X ^ (2 * (k * r)) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [<- pow_add]
  congr 2
  omega

theorem linnik_vmtech_outer_moment_power_le_sharp_envelope
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
      Fintype.card
          (Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X)) ^
            (2 * (k * r) - 1) *
        ((Finset.vinogradovMeanValue k (k * r) X : Real) *
          ((Finset.vinogradovMeanValue k (k * r) L : Real) *
            ((2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
              48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
                (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
                  (k * r * L ^ (j.val + 1) + 1) +
                  (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j))))) := by
  have hsecond := linnik_vmtech_outer_second_holder
    k r X L alpha hkr
  have hpair := linnik_vmtech_pair_moment_sum_le_vmvt
    k r X L alpha
  have hmoment := linnik_vmtech_difference_moment_sum_le_envelope
    k r X L alpha theta a q hq hcop htheta halpha
  calc
    _ <= Fintype.card
          (Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X)) ^
            (2 * (k * r) - 1) *
        Finset.univ.sum (fun uv :
          Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X) =>
          norm (linnikVMTechOuterWeight alpha L (fun j =>
            linnikVMTechPowerDifference (fun x : Fin X => x.val)
              uv.fst uv.snd j)) ^ (2 * (k * r))) := hsecond
    _ <= Fintype.card
          (Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X)) ^
            (2 * (k * r) - 1) *
        ((Finset.vinogradovMeanValue k (k * r) X : Real) *
          (linnikVMTechDifferenceRange k r X).sum
            (linnikVMTechDifferenceMoment alpha L (k * r))) := by
      exact mul_le_mul_of_nonneg_left hpair (by positivity)
    _ <= Fintype.card
          (Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X)) ^
            (2 * (k * r) - 1) *
        ((Finset.vinogradovMeanValue k (k * r) X : Real) *
          ((Finset.vinogradovMeanValue k (k * r) L : Real) *
            ((2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
              48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
                (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
                  (k * r * L ^ (j.val + 1) + 1) +
                  (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j))))) := by
      gcongr

theorem linnik_vmtech_outer_moment_power_le_sharp_explicit
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
      ((X : Real) ^ (2 * (k * r))) ^ (2 * (k * r) - 1) *
        ((Finset.vinogradovMeanValue k (k * r) X : Real) *
          ((Finset.vinogradovMeanValue k (k * r) L : Real) *
            ((2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
              48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
                (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
                  (k * r * L ^ (j.val + 1) + 1) +
                  (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j))))) := by
  have h := linnik_vmtech_outer_moment_power_le_sharp_envelope
    k r X L alpha theta a q hkr hq hcop htheta halpha
  simpa only [linnik_vmtech_pair_domain_card, Nat.cast_pow] using h

theorem linnik_vmtech_double_sum_power_le_sharp_explicit
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
        (((X : Real) ^ (2 * (k * r))) ^ (2 * (k * r) - 1) *
          ((Finset.vinogradovMeanValue k (k * r) X : Real) *
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
  have hexplicit := linnik_vmtech_outer_moment_power_le_sharp_explicit
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
        (((X : Real) ^ (2 * (k * r))) ^ (2 * (k * r) - 1) *
          ((Finset.vinogradovMeanValue k (k * r) X : Real) *
            ((Finset.vinogradovMeanValue k (k * r) L : Real) *
              ((2 : Real) ^ k * Finset.univ.prod (fun j : Fin k =>
                48 * (((((k * r * L ^ (j.val + 1) + 1 : Nat) : Real) *
                  (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat)) / q j) +
                    (k * r * L ^ (j.val + 1) + 1) +
                    (4 * (k * r * X ^ (j.val + 1)) + 1 : Nat) + q j)))))) := by
      exact mul_le_mul_of_nonneg_left hexplicit (by positivity)
