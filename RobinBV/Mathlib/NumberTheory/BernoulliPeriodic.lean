/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Normalized periodic Bernoulli kernels

The normalized profiles satisfy an exact integration-by-parts recursion.
Integer-cell endpoints telescope, and the power tails are absolutely
integrable for real part below minus one. The tail norm constant depends
only on the Bernoulli index; it is existential, not numerically evaluated.
The index-one endpoint discontinuity is treated by almost-everywhere
integral equality, not by asserting equality at the discontinuity.
-/

set_option autoImplicit false

namespace Polynomial

/-- The rational Bernoulli polynomial divided by its factorial. -/
noncomputable def bernoulliNormalized (k : Nat) : Polynomial Rat :=
  C (1/(k.factorial : Rat))*bernoulli k

/-- Differentiation lowers the normalized Bernoulli index by one. -/
theorem derivative_bernoulliNormalized (k : Nat) :
    derivative (bernoulliNormalized (k+1)) = bernoulliNormalized k := by
  have hfac : (1/((k+1).factorial : Rat))*((k : Rat)+1) = 1/(k.factorial : Rat) := by
    have hk0 : Not ((k.factorial : Rat) = 0) := by exact_mod_cast Nat.factorial_ne_zero k
    have hk1 : Not ((k : Rat)+1 = 0) := by positivity
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  calc
    _ = (C (1/((k+1).factorial : Rat))*C ((k : Rat)+1))*bernoulli k := by
      simp only [bernoulliNormalized, derivative_mul, derivative_C, zero_mul,
        zero_add, derivative_bernoulli_add_one, map_add, map_natCast, map_one]
      ring
    _ = bernoulliNormalized k := by
      rw [<- C_mul, hfac]
      rfl

/-- For indices other than one, the values at the two unit endpoints agree. -/
theorem bernoulliNormalized_one_eq_zero {k : Nat} (hk : Not (k = 1)) :
    (bernoulliNormalized k).eval 1 = (bernoulliNormalized k).eval 0 := by
  simp only [bernoulliNormalized, eval_mul, eval_C, bernoulli_eval_one,
    bernoulli_eval_zero, bernoulli_eq_bernoulli'_of_ne_one hk]

/-- The normalized Bernoulli polynomial evaluated over the reals. -/
noncomputable def bernoulliNormalizedReal (k : Nat) (u : Real) : Real :=
  ((bernoulliNormalized k).map (Rat.castHom Real)).eval u

/-- The real normalized profiles have the expected successive derivatives. -/
theorem hasDerivAt_bernoulliNormalizedReal (k : Nat) (u : Real) :
    HasDerivAt (bernoulliNormalizedReal (k+1)) (bernoulliNormalizedReal k u) u := by
  change HasDerivAt (fun v : Real =>
    ((bernoulliNormalized (k+1)).map (Rat.castHom Real)).eval v)
    (((bernoulliNormalized k).map (Rat.castHom Real)).eval u) u
  simpa only [derivative_map, derivative_bernoulliNormalized] using!
    (((bernoulliNormalized (k+1)).map (Rat.castHom Real)).hasDerivAt u)

/-- The real profile has equal endpoint values away from index one. -/
theorem bernoulliNormalizedReal_one_eq_zero {k : Nat} (hk : Not (k = 1)) :
    bernoulliNormalizedReal k 1 = bernoulliNormalizedReal k 0 := by
  have h1 := eval_map_apply (p := bernoulliNormalized k) (f := Rat.castHom Real) (1 : Rat)
  have h0 := eval_map_apply (p := bernoulliNormalized k) (f := Rat.castHom Real) (0 : Rat)
  simp only [map_one, map_zero] at h1 h0
  change ((bernoulliNormalized k).map (Rat.castHom Real)).eval 1 =
    ((bernoulliNormalized k).map (Rat.castHom Real)).eval 0
  rw [h1, h0, bernoulliNormalized_one_eq_zero hk]

/-- Each real normalized profile is continuous. -/
theorem continuous_bernoulliNormalizedReal (k : Nat) :
    Continuous (bernoulliNormalizedReal k) := by
  exact (show Differentiable Real (bernoulliNormalizedReal k) from
    fun u => (((bernoulliNormalized k).map (Rat.castHom Real)).hasDerivAt u).differentiableAt).continuous

/-- Exact integration by parts for a normalized profile on one positive cell. -/
theorem bernoulliNormalizedReal_cpow_cell {k : Nat} (hk : 1 <= k)
    {a : Real} (ha : 0 < a) {z : Complex} (hz : z.re < 0) :
    intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal k u)*Complex.ofReal (a+u)^z)
      0 1 MeasureTheory.volume =
    Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (Complex.ofReal (a+1)^z-Complex.ofReal a^z) -
    z*intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal (k+1) u)*Complex.ofReal (a+u)^(z-1))
      0 1 MeasureTheory.volume := by
  have hz0 : Not (z = 0) := by
    intro heq
    rw [heq] at hz
    norm_num at hz
  have hcont (w : Complex) :
      ContinuousOn (fun u : Real => Complex.ofReal (a+u)^w) (Set.Icc (0 : Real) 1) := by
    have hb : Continuous (fun u : Real => Complex.ofReal (a+u)) := by fun_prop
    exact hb.continuousOn.cpow_const (fun u hu =>
      Complex.ofReal_mem_slitPlane.mpr (by linarith [hu.1]))
  have hf (u : Real) (hu : (Set.uIcc (0 : Real) 1) u) :
      HasDerivAt (fun v : Real => Complex.ofReal (a+v)^z)
        (z*Complex.ofReal (a+u)^(z-1)) u := by
    rw [Set.uIcc_of_le (by norm_num : (0 : Real) <= 1)] at hu
    have hau : 0 < a+u := by linarith [hu.1]
    have ht := hasDerivAt_ofReal_cpow_const hau.ne' hz0
    simpa only [Function.comp_def, one_smul] using!
      ht.scomp u ((hasDerivAt_id u).const_add a)
  have hq (u : Real) (_hu : (Set.uIcc (0 : Real) 1) u) :
      HasDerivAt (fun v : Real => Complex.ofReal (bernoulliNormalizedReal (k+1) v))
        (Complex.ofReal (bernoulliNormalizedReal k u)) u :=
    (hasDerivAt_bernoulliNormalizedReal k u).ofReal_comp
  have hfInt : IntervalIntegrable
      (fun u : Real => z*Complex.ofReal (a+u)^(z-1)) MeasureTheory.volume 0 1 :=
    ((hcont (z-1)).const_mul z).intervalIntegrable_of_Icc (by norm_num)
  have hpInt : IntervalIntegrable
      (fun u : Real => Complex.ofReal (bernoulliNormalizedReal k u))
      MeasureTheory.volume 0 1 :=
    (Complex.continuous_ofReal.comp (continuous_bernoulliNormalizedReal k)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf hq hfInt hpInt
  have hleft : intervalIntegral (fun u : Real =>
      Complex.ofReal (a+u)^z*Complex.ofReal (bernoulliNormalizedReal k u))
      0 1 MeasureTheory.volume =
    intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal k u)*Complex.ofReal (a+u)^z)
      0 1 MeasureTheory.volume := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact mul_comm _ _
  have hright : intervalIntegral (fun u : Real =>
      (z*Complex.ofReal (a+u)^(z-1))*Complex.ofReal (bernoulliNormalizedReal (k+1) u))
      0 1 MeasureTheory.volume =
    z*intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal (k+1) u)*Complex.ofReal (a+u)^(z-1))
      0 1 MeasureTheory.volume := by
    calc
      _ = intervalIntegral (fun u : Real => z*
          (Complex.ofReal (bernoulliNormalizedReal (k+1) u)*Complex.ofReal (a+u)^(z-1)))
          0 1 MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro u hu
        ring
      _ = _ := intervalIntegral.integral_const_mul z _
  rw [hleft, hright] at h
  have hend : bernoulliNormalizedReal (k+1) 1 = bernoulliNormalizedReal (k+1) 0 :=
    bernoulliNormalizedReal_one_eq_zero (by omega)
  simp only [hend, add_zero] at h
  calc
    _ = Complex.ofReal (a+1)^z*Complex.ofReal (bernoulliNormalizedReal (k+1) 0) -
        Complex.ofReal a^z*Complex.ofReal (bernoulliNormalizedReal (k+1) 0) -
        z*intervalIntegral (fun u : Real =>
          Complex.ofReal (bernoulliNormalizedReal (k+1) u)*Complex.ofReal (a+u)^(z-1))
          0 1 MeasureTheory.volume := h
    _ = _ := by ring

/-- The normalized profile extended periodically through the fractional part. -/
noncomputable def bernoulliPeriodic (k : Nat) (x : Real) : Real :=
  bernoulliNormalizedReal k (Int.fract x)

/-- The periodic Bernoulli kernel is measurable, including index one. -/
theorem measurable_bernoulliPeriodic (k : Nat) : Measurable (bernoulliPeriodic k) :=
  (continuous_bernoulliNormalizedReal k).measurable.comp measurable_fract

/-- Each periodic kernel has a uniformly bounded, absolutely integrable power tail. -/
theorem bernoulliPeriodic_cpow_tail_bound (k : Nat) :
    Exists fun C : Real => 1 <= C /\
      forall (a : Real) (z : Complex), 0 < a -> z.re < -1 ->
      MeasureTheory.IntegrableOn
        (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
        (Set.Ioi a) /\
      norm (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi a))
        (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)) <=
        C*(-a^(z.re+1)/(z.re+1)) := by
  obtain h := (isCompact_Icc (a := (0 : Real)) (b := 1)).exists_bound_of_continuousOn
    (continuous_bernoulliNormalizedReal k).continuousOn
  let C : Real := max h.choose 1
  have hB (x : Real) : norm (Complex.ofReal (bernoulliPeriodic k x)) <= C := by
    rw [Complex.norm_real]
    exact (h.choose_spec (Int.fract x)
      (And.intro (Int.fract_nonneg x) (Int.fract_lt_one x).le)).trans (le_max_left _ _)
  refine Exists.intro C (And.intro (le_max_right _ _) ?_)
  intro a z ha hz
  let mu : MeasureTheory.Measure Real := MeasureTheory.volume.restrict (Set.Ioi a)
  have hPow : MeasureTheory.Integrable (fun x : Real => Complex.ofReal x^z) mu :=
    integrableOn_Ioi_cpow_of_lt hz ha
  have hMajor : MeasureTheory.Integrable (fun x : Real => C*x^z.re) mu :=
    (integrableOn_Ioi_rpow_of_lt hz ha).const_mul C
  have hBm : Measurable (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)) :=
    Complex.continuous_ofReal.measurable.comp (measurable_bernoulliPeriodic k)
  have hMeas : MeasureTheory.AEStronglyMeasurable
      (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z) mu :=
    hBm.aestronglyMeasurable.mul hPow.aestronglyMeasurable
  have hBound : Filter.Eventually
      (fun x : Real => norm (Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
        <= C*x^z.re) (MeasureTheory.ae mu) := by
    have hmem : Filter.Eventually (fun x : Real => (Set.Ioi a) x)
        (MeasureTheory.ae mu) := MeasureTheory.ae_restrict_mem measurableSet_Ioi
    filter_upwards [hmem] with x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans hx)]
    exact mul_le_mul_of_nonneg_right (hB x)
      (Real.rpow_nonneg (ha.trans hx).le z.re)
  have hInt : MeasureTheory.Integrable
      (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z) mu :=
    hMajor.mono' hMeas hBound
  refine And.intro hInt ?_
  calc
    _ <= MeasureTheory.integral mu
        (fun x : Real => norm (Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)) :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ <= MeasureTheory.integral mu (fun x : Real => C*x^z.re) :=
      MeasureTheory.integral_mono_ae hInt.norm hMajor hBound
    _ = C*(-a^(z.re+1)/(z.re+1)) := by
      dsimp [mu]
      rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt hz ha]

/-- Integer translation identifies a periodic cell integral with its unit profile. -/
theorem bernoulliPeriodic_cpow_unit_shift (k N : Nat) (z : Complex) :
    intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
      (N : Real) ((N : Real)+1) MeasureTheory.volume =
    intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal k u)*Complex.ofReal ((N : Real)+u)^z)
      0 1 MeasureTheory.volume := by
  calc
    _ = intervalIntegral (fun u : Real =>
        Complex.ofReal (bernoulliPeriodic k ((N : Real)+u))*Complex.ofReal ((N : Real)+u)^z)
        0 1 MeasureTheory.volume := by
      simpa only [add_zero] using
        (intervalIntegral.integral_comp_add_left (a := (0 : Real)) (b := 1)
          (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
          (N : Real)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr_ae
      have hne : Filter.Eventually (fun x : Real => Not (x = 1))
          (MeasureTheory.ae MeasureTheory.volume) := by
        simp [MeasureTheory.ae_iff]
      filter_upwards [hne] with u hu
      intro hmem
      rw [Set.uIoc_of_le (by norm_num : (0 : Real) <= 1)] at hmem
      have hu1 : u < 1 := lt_of_le_of_ne hmem.2 hu
      have hfrac : Int.fract ((N : Real)+u) = u := by
        rw [add_comm, Int.fract_add_natCast,
          Int.fract_eq_self.mpr (And.intro hmem.1.le hu1)]
      simp only [bernoulliPeriodic, hfrac]

/-- The periodic power integral satisfies the exact one-cell recursion. -/
theorem bernoulliPeriodic_cpow_cell {k N : Nat} (hk : 1 <= k) (hN : 0 < N)
    {z : Complex} (hz : z.re < 0) :
    intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
      (N : Real) ((N : Real)+1) MeasureTheory.volume =
    Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (Complex.ofReal ((N : Real)+1)^z-Complex.ofReal (N : Real)^z) -
    z*intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))
      (N : Real) ((N : Real)+1) MeasureTheory.volume := by
  rw [bernoulliPeriodic_cpow_unit_shift k N z,
    bernoulliPeriodic_cpow_unit_shift (k+1) N (z-1)]
  exact bernoulliNormalizedReal_cpow_cell hk (by exact_mod_cast hN) hz

/-- Adjacent positive integer cells telescope with both boundary terms retained. -/
theorem bernoulliPeriodic_cpow_finite_recursion {k N : Nat} (hk : 1 <= k)
    (hN : 0 < N) {z : Complex} (hz : z.re < -1) (M : Nat) :
    intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
      (N : Real) ((N : Real)+(M : Real)) MeasureTheory.volume =
    Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (Complex.ofReal ((N : Real)+(M : Real))^z-Complex.ofReal (N : Real)^z) -
    z*intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))
      (N : Real) ((N : Real)+(M : Real)) MeasureTheory.volume := by
  have hN0 : (0 : Real) < N := by exact_mod_cast hN
  have hz1 : (z-1).re < -1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hInt (j : Nat) (w : Complex) (hw : w.re < -1) (a b : Real)
      (ha : (N : Real) <= a) (hab : a <= b) :
      IntervalIntegrable
        (fun x : Real => Complex.ofReal (bernoulliPeriodic j x)*Complex.ofReal x^w)
        MeasureTheory.volume a b := by
    have hsmall := ((bernoulliPeriodic_cpow_tail_bound j).choose_spec.2
      ((N : Real)/2) w (by positivity) hw).1
    have hpart : MeasureTheory.IntegrableOn
        (fun x : Real => Complex.ofReal (bernoulliPeriodic j x)*Complex.ofReal x^w)
        (Set.uIcc a b) := by
      apply hsmall.mono_set
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      change (N : Real)/2 < x
      linarith [hx.1]
    exact hpart.intervalIntegrable
  induction M with
  | zero =>
    simp only [Nat.cast_zero, add_zero, intervalIntegral.integral_same,
      sub_self, mul_zero]
  | succ M ih =>
    have hNM : (N : Real) <= (N : Real)+(M : Real) :=
      le_add_of_nonneg_right (Nat.cast_nonneg M)
    have hF := intervalIntegral.integral_add_adjacent_intervals
      (hInt k z hz (N : Real) ((N : Real)+(M : Real)) (le_refl _) hNM)
      (hInt k z hz ((N : Real)+(M : Real)) ((N : Real)+((M : Real)+1)) hNM (by linarith))
    have hG := intervalIntegral.integral_add_adjacent_intervals
      (hInt (k+1) (z-1) hz1 (N : Real) ((N : Real)+(M : Real)) (le_refl _) hNM)
      (hInt (k+1) (z-1) hz1 ((N : Real)+(M : Real))
        ((N : Real)+((M : Real)+1)) hNM (by linarith))
    have hcell := bernoulliPeriodic_cpow_cell hk
      (show 0 < N+M by omega) (show z.re < 0 by linarith)
    simp only [Nat.cast_add, add_assoc] at hcell
    simp only [Nat.cast_succ]
    rw [<- hF, <- hG, ih, hcell]
    ring

/-- The finite recursion passes to the absolutely convergent infinite tail. -/
theorem bernoulliPeriodic_cpow_tail_recursion {k N : Nat} (hk : 1 <= k)
    (hN : 0 < N) {z : Complex} (hz : z.re < -1) :
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
      (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z) =
    -Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*Complex.ofReal (N : Real)^z -
    z*MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
      (fun x : Real => Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1)) := by
  have hN0 : (0 : Real) < N := by exact_mod_cast hN
  have hz1 : (z-1).re < -1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hFInt := ((bernoulliPeriodic_cpow_tail_bound k).choose_spec.2
    (N : Real) z hN0 hz).1
  have hGInt := ((bernoulliPeriodic_cpow_tail_bound (k+1)).choose_spec.2
    (N : Real) (z-1) hN0 hz1).1
  have ht : Filter.Tendsto (fun m : Nat => (N : Real)+(m : Real))
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono
      (fun m : Nat => le_add_of_nonneg_left hN0.le) tendsto_natCast_atTop_atTop
  have hpow : Filter.Tendsto (fun m : Nat => Complex.ofReal ((N : Real)+(m : Real))^z)
      Filter.atTop (nhds 0) := by
    have hr : Filter.Tendsto (fun m : Nat => ((N : Real)+(m : Real))^z.re)
        Filter.atTop (nhds 0) := by
      simpa only [neg_neg, Function.comp_def] using
        (tendsto_rpow_neg_atTop (by linarith : 0 < -z.re)).comp ht
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have heq : (fun m : Nat => norm (Complex.ofReal ((N : Real)+(m : Real))^z)) =
        (fun m : Nat => ((N : Real)+(m : Real))^z.re) := by
      funext m
      exact Complex.norm_cpow_eq_rpow_re_of_pos
        (by positivity : 0 < (N : Real)+(m : Real)) z
    rw [heq]
    exact hr
  have hlimF := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (N : Real) hFInt ht
  have hlimG := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (N : Real) hGInt ht
  have hlimR := ((hpow.sub_const (Complex.ofReal (N : Real)^z)).const_mul
    (Complex.ofReal (bernoulliNormalizedReal (k+1) 0))).sub (hlimG.const_mul z)
  have hfun : (fun m : Nat =>
      Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
        (Complex.ofReal ((N : Real)+(m : Real))^z-Complex.ofReal (N : Real)^z) -
      z*intervalIntegral (fun x : Real =>
        Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))
        (N : Real) ((N : Real)+(m : Real)) MeasureTheory.volume) =
    (fun m : Nat => intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
      (N : Real) ((N : Real)+(m : Real)) MeasureTheory.volume) := by
    funext m
    exact (bernoulliPeriodic_cpow_finite_recursion hk hN hz m).symm
  change Filter.Tendsto (fun m : Nat =>
    Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (Complex.ofReal ((N : Real)+(m : Real))^z-Complex.ofReal (N : Real)^z) -
    z*intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))
      (N : Real) ((N : Real)+(m : Real)) MeasureTheory.volume)
    Filter.atTop
    (nhds (Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (0-Complex.ofReal (N : Real)^z) -
      z*MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
        (fun x : Real => Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))))
    at hlimR
  rw [hfun] at hlimR
  have heq := tendsto_nhds_unique hlimF hlimR
  simpa only [zero_sub, mul_neg, neg_mul] using heq

end Polynomial
