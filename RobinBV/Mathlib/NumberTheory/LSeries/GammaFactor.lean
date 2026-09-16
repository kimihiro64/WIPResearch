/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The gamma factor in the zeta functional equation

The actual quotient of gamma functions is differentiable on Re(s) < 1.
Its modulus on Re(s) = 1/2 - 2*k is an exact finite product, including k = 0.
Gamma recurrence gives a polynomial vertical bound, while Euler reflection
and the convergent gamma integral give an exponential bound across the entire
left half-plane. All zero denominators are handled explicitly.

The functional-equation statement excludes s = 0, where the chosen value of
the zeta function requires a separate convention. No zero-density, prime-count,
Stirling asymptotic, or unproved contour estimate is assumed.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Complex

/-- The gamma quotient multiplying zeta(1-s) in the functional equation. -/
noncomputable def zetaGammaFactor (s : Complex) : Complex :=
  (Real.pi : Complex) ^ (s - 1 / 2) * Gamma ((1 - s) / 2) / Gamma (s / 2)

private theorem quarter_shift_not_pole {z : Complex} (k : Nat)
    (hz : z.re = 1 / 4 - (k : Real)) (m : Nat) : Not (z = -(m : Complex)) := by
  intro he
  have hre := congrArg Complex.re he
  simp only [neg_re, natCast_re] at hre
  have hreal : (4 : Real) * k = 4 * m + 1 := by linarith
  have hnat : 4 * k = 4 * m + 1 := by exact_mod_cast hreal
  omega

private theorem ascPochhammer_eval_prod (z : Complex) (n : Nat) :
    (ascPochhammer Complex n).eval z =
      (Finset.range n).prod (fun j => z + (j : Complex)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, ih, Finset.prod_range_succ]
    simp

/-- Exact product for the modulus on Re(s) = 1/2 - 2*k, for every natural k. -/
theorem norm_zetaGammaFactor_quarter_line (k : Nat) {s : Complex}
    (hs : s.re = 1 / 2 - 2 * (k : Real)) :
    norm (zetaGammaFactor s) =
      Real.pi ^ (-(2 * (k : Real))) *
        (Finset.range (2 * k)).prod
          (fun j => norm (star (s / 2) + (j : Complex))) := by
  have hz : (star (s / 2)).re = 1 / 4 - (k : Real) := by
    norm_num [Complex.div_re, hs]
    ring
  have harg : (1 - s) / 2 = star (s / 2) + ((2 * k : Nat) : Complex) := by
    apply Complex.ext
    next =>
      norm_num [Complex.div_re, hs]
      ring
    next =>
      norm_num [Complex.div_im]
  have hgamma := congrArg norm
    (Gamma_add_nat_div_Gamma_eq (n := 2 * k) (star (s / 2))
      (quarter_shift_not_pole k hz))
  rw [ascPochhammer_eval_prod, norm_prod] at hgamma
  have hconj : norm (Gamma (star (s / 2))) = norm (Gamma (s / 2)) := by
    change norm (Gamma ((starRingEnd Complex) (s / 2))) = _
    rw [Gamma_conj, norm_conj]
  simp only [norm_div, hconj] at hgamma
  have hpi : norm ((Real.pi : Complex) ^ (s - 1 / 2)) =
      Real.pi ^ (-(2 * (k : Real))) := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos (s - 1 / 2)]
    congr 1
    norm_num [hs]
  calc
    norm (zetaGammaFactor s) =
        norm ((Real.pi : Complex) ^ (s - 1 / 2)) *
          (norm (Gamma ((1 - s) / 2)) / norm (Gamma (s / 2))) := by
      simp only [zetaGammaFactor, norm_div, norm_mul]
      ring
    _ = _ := by rw [hpi, harg, hgamma]

/-- The gamma factor has modulus one on the critical line. -/
theorem norm_zetaGammaFactor_critical_line {s : Complex} (hs : s.re = 1 / 2) :
    norm (zetaGammaFactor s) = 1 := by
  have h := norm_zetaGammaFactor_quarter_line 0 (s := s) (by simpa using hs)
  simpa using h

/-- A polynomial vertical bound with an explicit constant for every natural k. -/
theorem norm_zetaGammaFactor_quarter_line_le (k : Nat) {s : Complex}
    (hs : s.re = 1 / 2 - 2 * (k : Real)) :
    norm (zetaGammaFactor s) <=
      (((k : Real) + 1) * (1 + abs s.im)) ^ (2 * k) := by
  have hpi : Real.pi ^ (-(2 * (k : Real))) <= 1 := by
    have hp : 1 <= Real.pi := le_trans (by norm_num) Real.two_le_pi
    have he : -(2 * (k : Real)) <= 0 :=
      neg_nonpos.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg k))
    simpa using Real.rpow_le_rpow_of_exponent_le hp he
  have hfactor : forall j : Nat, j < 2 * k ->
      norm (star (s / 2) + (j : Complex)) <=
        ((k : Real) + 1) * (1 + abs s.im) := by
    intro j hj
    have hjr : (j : Real) < 2 * (k : Real) := by exact_mod_cast hj
    have hj0 : (0 : Real) <= j := Nat.cast_nonneg j
    have hk0 : (0 : Real) <= k := Nat.cast_nonneg k
    have hr : abs (star (s / 2) + (j : Complex)).re <= (k : Real) + 1 := by
      apply abs_le.mpr
      norm_num [Complex.div_re, hs]
      constructor <;> linarith
    have hi : abs (star (s / 2) + (j : Complex)).im = abs s.im / 2 := by
      norm_num [Complex.div_im, abs_div]
    calc
      norm (star (s / 2) + (j : Complex)) <=
          abs (star (s / 2) + (j : Complex)).re +
            abs (star (s / 2) + (j : Complex)).im :=
        norm_le_abs_re_add_abs_im _
      _ <= ((k : Real) + 1) + abs s.im / 2 := by
        rw [hi]
        exact _root_.add_le_add hr le_rfl
      _ <= ((k : Real) + 1) * (1 + abs s.im) := by
        nlinarith [abs_nonneg s.im, mul_nonneg hk0 (abs_nonneg s.im)]
  rw [norm_zetaGammaFactor_quarter_line k hs]
  calc
    _ <= 1 * (Finset.range (2 * k)).prod
        (fun j => norm (star (s / 2) + (j : Complex))) :=
      mul_le_mul_of_nonneg_right hpi (Finset.prod_nonneg (by intros; positivity))
    _ <= 1 * (Finset.range (2 * k)).prod
        (fun _ => ((k : Real) + 1) * (1 + abs s.im)) := by
      apply mul_le_mul_of_nonneg_left _ zero_le_one
      exact Finset.prod_le_prod (by intros; positivity)
        (fun j hj => hfactor j (Finset.mem_range.mp hj))
    _ = _ := by simp

private theorem gamma_reflection_numerator_not_pole {s : Complex} (hs : s.re < 1)
    (m : Nat) : Not ((1 - s) / 2 = -(m : Complex)) := by
  intro he
  have hre := congrArg Complex.re he
  norm_num [Complex.div_re] at hre
  have hm : (0 : Real) <= m := Nat.cast_nonneg m
  linarith

/-- The actual zeta functional equation in gamma-quotient form, including trivial zeros. -/
theorem riemannZeta_eq_gammaFactor_mul {s : Complex} (hs : s.re < 1)
    (hs0 : Not (s = 0)) :
    riemannZeta s = zetaGammaFactor s * riemannZeta (1 - s) := by
  have h1 : Not (1 - s = 0) := by
    intro he
    have hre := congrArg Complex.re he
    norm_num at hre
    linarith
  have hp : Not ((Real.pi : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpa : Not ((Real.pi : Complex) ^ (s - 1 / 2) = 0) :=
    cpow_ne_zero_iff.mpr (Or.inl hp)
  have hpb : Not ((Real.pi : Complex) ^ (-s / 2) = 0) :=
    cpow_ne_zero_iff.mpr (Or.inl hp)
  have hg : Not (Gamma ((1 - s) / 2) = 0) :=
    Gamma_ne_zero (gamma_reflection_numerator_not_pole hs)
  have hpower : (Real.pi : Complex) ^ (-(1 - s) / 2) =
      (Real.pi : Complex) ^ (s - 1 / 2) * (Real.pi : Complex) ^ (-s / 2) := by
    rw [<- cpow_add _ _ hp]
    congr 1
    ring
  have hz := riemannZeta_def_of_ne_zero hs0
  have hz1 := riemannZeta_def_of_ne_zero h1
  change riemannZeta s = completedRiemannZeta s /
    ((Real.pi : Complex) ^ (-s / 2) * Gamma (s / 2)) at hz
  change riemannZeta (1 - s) = completedRiemannZeta (1 - s) /
    ((Real.pi : Complex) ^ (-(1 - s) / 2) * Gamma ((1 - s) / 2)) at hz1
  rw [completedRiemannZeta_one_sub, hpower] at hz1
  rw [hz, hz1, zetaGammaFactor]
  by_cases hd : Gamma (s / 2) = 0
  next =>
    simp [hd]
  next =>
    field_simp

/-- Inverse gamma removes denominator poles throughout Re(s) < 1. -/
theorem differentiableAt_zetaGammaFactor {s : Complex} (hs : s.re < 1) :
    DifferentiableAt Complex zetaGammaFactor s := by
  have hp : Not ((Real.pi : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpower : DifferentiableAt Complex
      (fun z : Complex => (Real.pi : Complex) ^ (z - 1 / 2)) s := by
    simp only [cpow_def_of_ne_zero hp]
    fun_prop
  have hnum : DifferentiableAt Complex
      (fun z : Complex => Gamma ((1 - z) / 2)) s :=
    (differentiableAt_Gamma _ (gamma_reflection_numerator_not_pole hs)).comp s
      (by fun_prop)
  have hinv : DifferentiableAt Complex
      (fun z : Complex => Inv.inv (Gamma (z / 2))) s := by
    simpa only [Function.comp_def] using
      differentiable_one_div_Gamma.differentiableAt.comp
        (x := s) (show DifferentiableAt Complex (fun z : Complex => z / 2) s from by
          fun_prop)
  change DifferentiableAt Complex
    (fun z : Complex => (Real.pi : Complex) ^ (z - 1 / 2) *
      Gamma ((1 - z) / 2) / Gamma (z / 2)) s
  convert (hpower.mul hnum).mul hinv using 1 <;> rfl

/-- The full convergent gamma integral is majorized by its real counterpart. -/
theorem norm_Gamma_le_real_Gamma {s : Complex} (hs : 0 < s.re) :
    norm (Gamma s) <= Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) (le_of_eq ?_)
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    norm_cpow_eq_rpow_re_of_pos hx (s - 1)]
  norm_num

/-- An exponential upper bound for the complex sine, with constant one. -/
theorem norm_sin_le_exp_abs_im (z : Complex) :
    norm (sin z) <= Real.exp (abs z.im) := by
  have he1 : Real.exp z.im <= Real.exp (abs z.im) :=
    Real.exp_le_exp.mpr (le_abs_self z.im)
  have he2 : Real.exp (-z.im) <= Real.exp (abs z.im) :=
    Real.exp_le_exp.mpr (neg_le_abs z.im)
  calc
    norm (sin z) = norm (exp (-z * I) - exp (z * I)) / 2 := by
      simp [Complex.sin]
    _ <= (norm (exp (-z * I)) + norm (exp (z * I))) / 2 := by
      exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ = (Real.exp z.im + Real.exp (-z.im)) / 2 := by
      norm_num [norm_exp, Complex.mul_re]
    _ <= Real.exp (abs z.im) := by linarith

/-- Euler reflection expressed without division by sine; zero cases are retained. -/
theorem one_div_Gamma_eq_reflection {z : Complex} (hz : z.re < 1) :
    1 / Gamma z = Gamma (1 - z) * sin ((Real.pi : Complex) * z) / Real.pi := by
  have hp : Not ((Real.pi : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg : Not (Gamma (1 - z) = 0) := by
    apply Gamma_ne_zero
    intro m he
    have hre := congrArg Complex.re he
    norm_num at hre
    have hm : (0 : Real) <= m := Nat.cast_nonneg m
    linarith
  have hprod := Gamma_mul_Gamma_one_sub z
  by_cases hsin : sin ((Real.pi : Complex) * z) = 0
  next =>
    have hzero : Gamma z = 0 := by
      simp only [hsin, div_zero] at hprod
      exact (mul_eq_zero.mp hprod).resolve_right hg
    simp [hsin, hzero]
  next =>
    have hg0 : Not (Gamma z = 0) := by
      intro he
      rw [he, zero_mul] at hprod
      exact (div_ne_zero hp hsin) hprod.symm
    have hcross := (eq_div_iff hsin).mp hprod
    apply (div_eq_div_iff hg0 hp).mpr
    calc
      1 * (Real.pi : Complex) =
          (Gamma z * Gamma (1 - z)) * sin ((Real.pi : Complex) * z) := by
        simpa using hcross.symm
      _ = _ := by ring

/-- An explicit exponential envelope valid at every point of Re(s) < 1. -/
theorem norm_zetaGammaFactor_le_exp (s : Complex) (hs : s.re < 1) :
    norm (zetaGammaFactor s) <=
      Real.pi ^ (s.re - 1 / 2) * Real.Gamma ((1 - s.re) / 2) *
        Real.Gamma (1 - s.re / 2) *
          Real.exp (Real.pi * abs s.im / 2) / Real.pi := by
  have hnum : 0 < ((1 - s) / 2).re := by
    norm_num [Complex.div_re]
    linarith
  have hden : (s / 2).re < 1 := by
    norm_num [Complex.div_re]
    linarith
  have hother : 0 < (1 - s / 2).re := by
    simp only [sub_re, one_re]
    linarith
  have hrepr : zetaGammaFactor s =
      (Real.pi : Complex) ^ (s - 1 / 2) * Gamma ((1 - s) / 2) *
        Gamma (1 - s / 2) * sin ((Real.pi : Complex) * (s / 2)) / Real.pi := by
    unfold zetaGammaFactor
    rw [div_eq_mul_one_div, one_div_Gamma_eq_reflection hden]
    ring
  have hgam1 := norm_Gamma_le_real_Gamma hnum
  have hgam2 := norm_Gamma_le_real_Gamma hother
  have hsin := norm_sin_le_exp_abs_im ((Real.pi : Complex) * (s / 2))
  have hpi : norm ((Real.pi : Complex) ^ (s - 1 / 2)) =
      Real.pi ^ (s.re - 1 / 2) := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos (s - 1 / 2)]
    norm_num
  have hre1 : ((1 - s) / 2).re = (1 - s.re) / 2 := by
    norm_num [Complex.div_re]
  have hre2 : (1 - s / 2).re = 1 - s.re / 2 := by
    norm_num [Complex.div_re]
  have him : abs (((Real.pi : Complex) * (s / 2)).im) =
      Real.pi * abs s.im / 2 := by
    norm_num [Complex.div_im, abs_mul, abs_div, abs_of_pos Real.pi_pos]
    ring
  rw [hre1] at hgam1
  rw [hre2] at hgam2
  rw [him] at hsin
  rw [hrepr, norm_div, norm_mul, norm_mul, norm_mul, hpi,
    Complex.norm_of_nonneg Real.pi_pos.le]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  have hp0 := Real.rpow_nonneg Real.pi_pos.le (s.re - 1 / 2)
  have hg10 : 0 <= Real.Gamma ((1 - s.re) / 2) := le_trans (norm_nonneg _) hgam1
  have hg20 : 0 <= Real.Gamma (1 - s.re / 2) := le_trans (norm_nonneg _) hgam2
  exact mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hgam1 hp0) hgam2
      (norm_nonneg _) (mul_nonneg hp0 hg10))
    hsin (norm_nonneg _) (mul_nonneg (mul_nonneg hp0 hg10) hg20)

end Complex
