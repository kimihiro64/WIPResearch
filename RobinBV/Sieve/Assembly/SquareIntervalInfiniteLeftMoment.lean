/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Sieve.Assembly.SquareIntervalLeftZeroMoment
import RobinBV.Sieve.Proof.ZetaWindowSummability

/-!
# The complete left-zero fourth moment for moving square windows

The height-uniform finite-set estimate passes to the actual infinite
left-zero sum using its proved summability and Fatou's lemma. All actual
multiplicities and both signs of the imaginary parts are retained, with
real part at most one half. The bound is uniform for X>=16 and eta>0;
the two absolute constants are existential and the fixed profile's finite
second-derivative fourth mass remains displayed. This does not estimate
the right-zero contribution or prove an almost-all prime-count theorem.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem movingSquareTest_actual_left_zero_moment :
    Exists fun C0 : Real => Exists fun C1 : Real => 1 <= C0 /\ 1 <= C1 /\
      forall X eta : Real, 16 <= X -> 0 < eta ->
      MeasureTheory.IntegrableOn (fun x =>
        norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          if (rho : Complex).re <= 1/2
          then (Zeta23.zeroMult (rho : Complex) : Complex)*
            Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
              (Zeta23.gammaOf (rho : Complex))
          else 0))^4) (Set.Icc X (2*X)) /\
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
        (fun x => norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          if (rho : Complex).re <= 1/2
          then (Zeta23.zeroMult (rho : Complex) : Complex)*
            Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
              (Zeta23.gammaOf (rho : Complex))
          else 0))^4) <=
        (66060288000*C0^4*(Real.log (8*Real.sqrt X))^5+
          1123024896000*C1^4*(MeasureTheory.integral
            (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4))*
            (Real.log (16*Real.sqrt X))^5)*X^2*Real.sqrt X := by
  classical
  let : Countable Zeta23.zetaZeroConfig.carrier := zeta_zero_carrier_countable
  obtain h := movingSquareTest_actual_left_zero_finite_moment
  let C0 : Real := h.choose
  let C1 : Real := h.choose_spec.choose
  have hC0 : 1 <= C0 := h.choose_spec.choose_spec.1
  have hC1 : 1 <= C1 := h.choose_spec.choose_spec.2.1
  refine Exists.intro C0 (Exists.intro C1 (And.intro hC0 (And.intro hC1 ?_)))
  intro X eta hX he
  let mu : MeasureTheory.Measure Real := MeasureTheory.volume.restrict (Set.Icc X (2*X))
  let M : Real := MeasureTheory.integral
    (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
    (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4)
  let B : Real := (66060288000*C0^4*(Real.log (8*Real.sqrt X))^5+
    1123024896000*C1^4*M*(Real.log (16*Real.sqrt X))^5)*X^2*Real.sqrt X
  let k : Real -> Real -> Complex := fun x =>
    scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x)
  let g : Real -> Zeta23.zetaZeroConfig.carrier -> Complex := fun x rho =>
    if (rho : Complex).re <= 1/2
    then (Zeta23.zeroMult (rho : Complex) : Complex)*
      Zeta23.paperFT (k x) (Zeta23.gammaOf (rho : Complex)) else 0
  let F : Finset Zeta23.zetaZeroConfig.carrier -> Real -> Real := fun s x =>
    norm (Finset.sum s (g x))^4
  let G : Real -> Real := fun x => norm (tsum (g x))^4
  have hM0 : 0 <= M := MeasureTheory.integral_nonneg
    (fun v => pow_nonneg (norm_nonneg _) 4)
  have hS1 : 1 <= Real.sqrt X := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (by linarith : (1 : Real) <= X)
  have hl8 : 0 <= Real.log (8*Real.sqrt X) := Real.log_nonneg (by linarith)
  have hl16 : 0 <= Real.log (16*Real.sqrt X) := Real.log_nonneg (by linarith)
  have hB0 : 0 <= B := by
    dsimp [B]
    positivity
  have hF0 (s : Finset Zeta23.zetaZeroConfig.carrier) (x : Real) : 0 <= F s x :=
    pow_nonneg (norm_nonneg _) 4
  have hG0 : Filter.Eventually (fun x => 0 <= G x) (MeasureTheory.ae mu) :=
    Filter.Eventually.of_forall (fun x => pow_nonneg (norm_nonneg _) 4)
  have hfin (s : Finset Zeta23.zetaZeroConfig.carrier) :
      MeasureTheory.Integrable (F s) mu /\ MeasureTheory.integral mu (F s) <= B := by
    let A : Finset Zeta23.zetaZeroConfig.carrier :=
      Finset.filter (fun rho => (rho : Complex).re <= 1/2) s
    let D : Finset Complex := Finset.image
      (fun rho : Zeta23.zetaZeroConfig.carrier => (rho : Complex)) A
    have hD (rho : Complex) (hr : (D : Set Complex) rho) :
        Zeta23.IsNontrivialZero rho := by
      obtain hm := Finset.mem_image.mp hr
      rw [<- hm.choose_spec.2]
      exact hm.choose.property
    have hbeta (rho : Complex) (hr : (D : Set Complex) rho) : rho.re <= 1/2 := by
      obtain hm := Finset.mem_image.mp hr
      rw [<- hm.choose_spec.2]
      exact (Finset.mem_filter.mp hm.choose_spec.1).2
    have hsum (x : Real) :
        Finset.sum D (fun rho => (Zeta23.zeroMult rho : Complex)*
          Zeta23.paperFT (k x) (Zeta23.gammaOf rho)) = Finset.sum s (g x) := by
      calc
        _ = Finset.sum A (fun rho => (Zeta23.zeroMult (rho : Complex) : Complex)*
            Zeta23.paperFT (k x) (Zeta23.gammaOf (rho : Complex))) :=
          Finset.sum_image (by
            intro a ha b hb hab
            exact Subtype.val_injective hab)
        _ = _ := by
          change Finset.sum
            (Finset.filter
              (fun rho : Zeta23.zetaZeroConfig.carrier => (rho : Complex).re <= 1/2) s)
            (fun rho => (Zeta23.zeroMult (rho : Complex) : Complex)*
              Zeta23.paperFT (k x) (Zeta23.gammaOf (rho : Complex))) =
            Finset.sum s (fun rho => if (rho : Complex).re <= 1/2
              then (Zeta23.zeroMult (rho : Complex) : Complex)*
                Zeta23.paperFT (k x) (Zeta23.gammaOf (rho : Complex)) else 0)
          rw [Finset.sum_filter]
    have hb := h.choose_spec.choose_spec.2.2 X eta hX he D hD hbeta
    have hfun : (fun x => norm (Finset.sum D (fun rho =>
        (Zeta23.zeroMult rho : Complex)*
          Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
            (Zeta23.gammaOf rho)))^4) = F s := by
      funext x
      change norm (Finset.sum D (fun rho => (Zeta23.zeroMult rho : Complex)*
        Zeta23.paperFT (k x) (Zeta23.gammaOf rho)))^4 = norm (Finset.sum s (g x))^4
      rw [hsum]
    simp only [hfun] at hb
    exact hb
  have hlim : Filter.Eventually
      (fun x => Filter.Tendsto (fun s : Finset Zeta23.zetaZeroConfig.carrier => F s x)
        Filter.atTop (nhds (G x))) (MeasureTheory.ae mu) := by
    have hmem : Filter.Eventually (fun x => (Set.Icc X (2*X)) x)
        (MeasureTheory.ae mu) := MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem] with x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hs : Summable (g x) := scaledLogWindowTest_left_zero_summable he
      (movingSquareLogWidth_pos hx0) (Real.log x)
    have ht : Filter.Tendsto
        (fun s : Finset Zeta23.zetaZeroConfig.carrier => Finset.sum s (g x))
        Filter.atTop (nhds (tsum (g x))) := hs.hasSum
    exact ht.norm.pow 4
  have hmeas : MeasureTheory.AEStronglyMeasurable G mu :=
    _root_.aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun s => (hfin s).1.aestronglyMeasurable) hlim
  have hLinEach (s : Finset Zeta23.zetaZeroConfig.carrier) :
      MeasureTheory.lintegral mu (fun x => ENNReal.ofReal (F s x)) <= ENNReal.ofReal B := by
    calc
      _ = ENNReal.ofReal (MeasureTheory.integral mu (F s)) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfin s).1
          (Filter.Eventually.of_forall (hF0 s))).symm
      _ <= ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hfin s).2
  have hLin : MeasureTheory.lintegral mu (fun x => ENNReal.ofReal (G x)) <=
      ENNReal.ofReal B := by
    have hFatou := MeasureTheory.lintegral_liminf_le'
      (u := (Filter.atTop : Filter (Finset Zeta23.zetaZeroConfig.carrier)))
      (f := fun s x => ENNReal.ofReal (F s x))
      (fun s => ENNReal.measurable_ofReal.comp_aemeasurable
        (hfin s).1.aestronglyMeasurable.aemeasurable)
    have heq := hlim.mono (fun x hx =>
      ((ENNReal.continuous_ofReal.tendsto (G x)).comp hx).liminf_eq)
    simp only [Function.comp_def] at heq
    have hiEq := MeasureTheory.lintegral_congr_ae heq
    rw [hiEq] at hFatou
    exact hFatou.trans (Filter.liminf_le_of_frequently_le
      (Filter.Eventually.of_forall hLinEach).frequently)
  have hint : MeasureTheory.Integrable G mu := And.intro hmeas
    ((MeasureTheory.hasFiniteIntegral_iff_ofReal hG0).mpr
      (hLin.trans_lt ENNReal.ofReal_lt_top))
  refine And.intro hint ?_
  change MeasureTheory.integral mu G <= B
  apply (ENNReal.ofReal_le_ofReal_iff hB0).mp
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hG0]
  exact hLin

end RobinBV.Sieve
