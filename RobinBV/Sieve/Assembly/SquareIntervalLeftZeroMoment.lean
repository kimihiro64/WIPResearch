/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Sieve.Assembly.SquareIntervalUnitEnergy

/-!
# Height-uniform finite moments for actual left-half zeta zeros

The actual high-height band estimate contracts sufficiently under doubling to
close a finite induction over all heights above a positive cutoff. Every
finite actual zero set is covered, preserving multiplicities and both signs
of the imaginary part. The final theorem chooses the cutoff as the square
root of X and removes it from the bound.

The constants are existential and the taper derivative moment is fixed and
finite. These conclusions are uniform over finite sets; passage to the
infinite zero series and the full almost-all prime-count theorem is separate.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem movingSquareTest_actual_left_zero_tail_moment :
    Exists fun C : Real => 1 <= C /\
      forall X eta T : Real, 16 <= X -> 0 < eta -> 1 <= T ->
      forall A : Finset Complex,
      (forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) ->
      (forall rho, (A : Set Complex) rho -> rho.re <= 1/2) ->
      (forall rho, (A : Set Complex) rho -> T < abs rho.im) ->
      MeasureTheory.IntegrableOn (fun x =>
        norm (Finset.sum A (fun rho => (Zeta23.zeroMult rho : Complex)*
          Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
            (Zeta23.gammaOf rho)))^4) (Set.Icc X (2*X)) /\
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
        (fun x => norm (Finset.sum A (fun rho => (Zeta23.zeroMult rho : Complex)*
          Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
            (Zeta23.gammaOf rho)))^4) <=
        140378112000*C^4*(MeasureTheory.integral
          (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
          (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4))*
          X^5/T^5*(Real.log (16*T))^5 := by
  classical
  obtain h := movingSquareTest_actual_left_zero_high_moment
  let C : Real := h.choose
  have hC1 : 1 <= C := h.choose_spec.1
  have hC0 : 0 <= C := by linarith
  refine Exists.intro C (And.intro hC1 ?_)
  intro X eta T hX he hT A hA hbeta hlow
  let M : Real := MeasureTheory.integral
    (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
    (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4)
  let F : Real -> Real := fun U => C^4*M*X^5/U^5*(Real.log (16*U))^5
  let Z : Finset Complex -> Real -> Complex := fun B x =>
    Finset.sum B (fun rho => (Zeta23.zeroMult rho : Complex)*
      Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
        (Zeta23.gammaOf rho))
  let mass : Finset Complex -> Real := fun B =>
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Z B x)^4)
  have hX0 : 0 <= X := by linarith
  have hM0 : 0 <= M := MeasureTheory.integral_nonneg
    (fun v => pow_nonneg (norm_nonneg _) 4)
  have hF0 (U : Real) (hU : 1 <= U) : 0 <= F U :=
    mul_nonneg (div_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg hC0 4) hM0) (pow_nonneg hX0 5))
      (pow_nonneg (by linarith : 0 <= U) 5))
      (pow_nonneg (Real.log_nonneg (by linarith : 1 <= 16*U)) 5)
  have hcontract (U : Real) (hU : 1 <= U) :
      F (2*U) <= (3125/32768 : Real)*F U := by
    have hU0 : 0 < U := by linarith
    have hUn : Not (U = 0) := ne_of_gt hU0
    have hl16 : Real.log (16 : Real) = 4*Real.log 2 := by
      rw [show (16 : Real) = 2^4 by norm_num, Real.log_pow]
      norm_num
    have hl32 : Real.log (32 : Real) = 5*Real.log 2 := by
      rw [show (32 : Real) = 2^5 by norm_num, Real.log_pow]
      norm_num
    have heq1 : Real.log (16*U) = 4*Real.log 2+Real.log U := by
      rw [Real.log_mul (by norm_num) hUn, hl16]
    have heq2 : Real.log (16*(2*U)) = 5*Real.log 2+Real.log U := by
      rw [show 16*(2*U) = 32*U by ring, Real.log_mul (by norm_num) hUn, hl32]
    have hl : Real.log (16*(2*U)) <= (5/4 : Real)*Real.log (16*U) := by
      rw [heq1, heq2]
      linarith [Real.log_nonneg hU]
    have hl0 : 0 <= Real.log (16*(2*U)) :=
      Real.log_nonneg (by linarith)
    have hb0 : 0 <= (5/4 : Real)*Real.log (16*U) :=
      mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
    have hp2 : (Real.log (16*(2*U)))^2 <=
        ((5/4 : Real)*Real.log (16*U))^2 := by
      simpa only [pow_two] using mul_le_mul hl hl hl0 hb0
    have hp4 : (Real.log (16*(2*U)))^4 <=
        ((5/4 : Real)*Real.log (16*U))^4 := by
      calc
        (Real.log (16*(2*U)))^4 =
            (Real.log (16*(2*U)))^2*(Real.log (16*(2*U)))^2 := by ring
        _ <= ((5/4 : Real)*Real.log (16*U))^2*
            ((5/4 : Real)*Real.log (16*U))^2 :=
          mul_le_mul hp2 hp2 (sq_nonneg _) (sq_nonneg _)
        _ = ((5/4 : Real)*Real.log (16*U))^4 := by ring
    have hp5 : (Real.log (16*(2*U)))^5 <=
        ((5/4 : Real)*Real.log (16*U))^5 := by
      calc
        (Real.log (16*(2*U)))^5 =
            (Real.log (16*(2*U)))^4*Real.log (16*(2*U)) := by ring
        _ <= ((5/4 : Real)*Real.log (16*U))^4*
            ((5/4 : Real)*Real.log (16*U)) :=
          mul_le_mul hp4 hl hl0 (pow_nonneg hb0 4)
        _ = ((5/4 : Real)*Real.log (16*U))^5 := by ring
    calc
      F (2*U) <= (C^4*M*X^5/(2*U)^5)*
          ((5/4 : Real)*Real.log (16*U))^5 :=
        mul_le_mul_of_nonneg_left hp5 (div_nonneg
          (mul_nonneg (mul_nonneg (pow_nonneg hC0 4) hM0) (pow_nonneg hX0 5))
          (pow_nonneg (by linarith : 0 <= 2*U) 5))
      _ = _ := by dsimp [F]; field_simp [hUn]; ring
  have hInt (B : Finset Complex)
      (hB : forall rho, (B : Set Complex) rho -> Zeta23.IsNontrivialZero rho)
      (hb : forall rho, (B : Set Complex) rho -> rho.re <= 1/2) :
      MeasureTheory.IntegrableOn (fun x => norm (Z B x)^4) (Set.Icc X (2*X)) :=
    (movingSquareTest_finite_packet_low_energy B
      (fun rho : Complex => rho) (fun rho => (Zeta23.zeroMult rho : Complex))
      hX he (by norm_num : (1/2 : Real) <= 1)
      (fun rho hr => And.intro (hB rho hr).2.1.le (hb rho hr))).1
  have hband (U : Real) (hU : 1 <= U) (B : Finset Complex)
      (hB : forall rho, (B : Set Complex) rho -> Zeta23.IsNontrivialZero rho)
      (hb : forall rho, (B : Set Complex) rho -> rho.re <= 1/2)
      (hh : forall rho, (B : Set Complex) rho -> U <= abs rho.im /\ abs rho.im <= 2*U) :
      mass B <= 4128768000*F U := by
    have hm := (h.choose_spec.2 X eta U hX he hU B hB hb hh).2
    convert hm using 1
    dsimp [mass, Z, F, C, M]
    ring
  have hbound : forall J : Nat, forall U : Real, 1 <= U ->
      forall B : Finset Complex,
      (forall rho, (B : Set Complex) rho -> Zeta23.IsNontrivialZero rho) ->
      (forall rho, (B : Set Complex) rho -> rho.re <= 1/2) ->
      (forall rho, (B : Set Complex) rho ->
        U < abs rho.im /\ abs rho.im <= (2 : Real)^J*U) ->
      mass B <= (34*4128768000)*F U := by
    intro J
    induction J with
    | zero =>
      intro U hU B hB hb hh
      have hz (x : Real) : Z B x = 0 := by
        apply Finset.sum_eq_zero
        intro rho hr
        have hd := hh rho hr
        simp only [pow_zero, one_mul] at hd
        exact False.elim (not_lt_of_ge hd.2 hd.1)
      have hm : mass B = 0 := by
        simp only [mass, hz, norm_zero]
        norm_num
      rw [hm]
      exact mul_nonneg (by norm_num) (hF0 U hU)
    | succ J IH =>
      intro U hU B hB hb hh
      let B0 : Finset Complex := Finset.filter (fun rho : Complex => abs rho.im <= 2*U) B
      let B1 : Finset Complex := Finset.filter
        (fun rho : Complex => Not (abs rho.im <= 2*U)) B
      have hB0 (rho : Complex) (hr : (B0 : Set Complex) rho) :
          Zeta23.IsNontrivialZero rho := hB rho (Finset.mem_filter.mp hr).1
      have hb0 (rho : Complex) (hr : (B0 : Set Complex) rho) :
          rho.re <= 1/2 := hb rho (Finset.mem_filter.mp hr).1
      have hB1 (rho : Complex) (hr : (B1 : Set Complex) rho) :
          Zeta23.IsNontrivialZero rho := hB rho (Finset.mem_filter.mp hr).1
      have hb1 (rho : Complex) (hr : (B1 : Set Complex) rho) :
          rho.re <= 1/2 := hb rho (Finset.mem_filter.mp hr).1
      have hlo := hband U hU B0 hB0 hb0 (by
        intro rho hr
        have hm := Finset.mem_filter.mp hr
        exact And.intro (hh rho hm.1).1.le hm.2)
      have hhi := IH (2*U) (by linarith) B1 hB1 hb1 (by
        intro rho hr
        have hm := Finset.mem_filter.mp hr
        refine And.intro (lt_of_not_ge hm.2) ?_
        calc
          abs rho.im <= (2 : Real)^(J+1)*U := (hh rho hm.1).2
          _ = (2 : Real)^J*(2*U) := by rw [pow_succ]; ring)
      have hsplit (x : Real) : Z B x = Z B0 x+Z B1 x := by
        dsimp [Z, B0, B1]
        rw [Finset.sum_filter, Finset.sum_filter, <- Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro rho hr
        by_cases hd : abs rho.im <= 2*U
        next =>
          simp only [hd, if_true, not_true_eq_false, if_false, add_zero]
        next =>
          simp only [hd, if_false, not_false_eq_true, if_true, zero_add]
      have hpoint (x : Real) :
          norm (Z B x)^4 <= 8*(norm (Z B0 x)^4+norm (Z B1 x)^4) := by
        rw [hsplit]
        let a : Real := norm (Z B0 x)
        let b : Real := norm (Z B1 x)
        have ha : 0 <= a := norm_nonneg _
        have hb' : 0 <= b := norm_nonneg _
        have hn := norm_add_le (Z B0 x) (Z B1 x)
        have hn2 : norm (Z B0 x+Z B1 x)^2 <= (a+b)^2 := by
          simpa only [pow_two] using mul_le_mul hn hn (norm_nonneg _) (add_nonneg ha hb')
        have hn4 : norm (Z B0 x+Z B1 x)^4 <= (a+b)^4 := by
          calc
            norm (Z B0 x+Z B1 x)^4 =
                norm (Z B0 x+Z B1 x)^2*norm (Z B0 x+Z B1 x)^2 := by ring
            _ <= (a+b)^2*(a+b)^2 := mul_le_mul hn2 hn2 (sq_nonneg _) (sq_nonneg _)
            _ = (a+b)^4 := by ring
        have hp : 0 <= (a-b)^2*(7*a^2+10*a*b+7*b^2) :=
          mul_nonneg (sq_nonneg _) (add_nonneg
            (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
              (mul_nonneg (mul_nonneg (by norm_num) ha) hb'))
            (mul_nonneg (by norm_num) (sq_nonneg _)))
        calc
          _ <= (a+b)^4 := hn4
          _ <= 8*(a^4+b^4) := by nlinarith [hp]
      have hiB := hInt B hB hb
      have hi0 := hInt B0 hB0 hb0
      have hi1 := hInt B1 hB1 hb1
      have htri : mass B <= 8*(mass B0+mass B1) := by
        have hm := MeasureTheory.integral_mono hiB ((hi0.add hi1).const_mul 8) hpoint
        simp only [Pi.add_apply] at hm
        simpa only [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add hi0 hi1] using hm
      calc
        mass B <= 8*(mass B0+mass B1) := htri
        _ <= 8*(4128768000*F U+(34*4128768000)*F (2*U)) :=
          mul_le_mul_of_nonneg_left (add_le_add hlo hhi) (by norm_num)
        _ <= 8*(4128768000*F U+(34*4128768000)*((3125/32768 : Real)*F U)) :=
          mul_le_mul_of_nonneg_left
            (_root_.add_le_add (le_refl (4128768000*F U))
              (mul_le_mul_of_nonneg_left (hcontract U hU)
                (by norm_num : (0 : Real) <= 34*4128768000))) (by norm_num)
        _ <= (34*4128768000)*F U := by nlinarith [hF0 U hU]
  let R : Real := Finset.sum A (fun rho => abs rho.im)
  let J : Nat := Nat.ceil R
  have hR : R <= (J : Real) := Nat.le_ceil R
  have hJ : (J : Real) <= (2 : Real)^J := by
    exact_mod_cast (Nat.lt_two_pow_self (n := J)).le
  have hupper (rho : Complex) (hr : (A : Set Complex) rho) :
      abs rho.im <= (2 : Real)^J*T := by
    calc
      abs rho.im <= R := Finset.single_le_sum (fun rho _ => abs_nonneg rho.im) hr
      _ <= (J : Real) := hR
      _ <= (2 : Real)^J := hJ
      _ <= (2 : Real)^J*T := by
        have hp := pow_nonneg (by norm_num : (0 : Real) <= 2) J
        nlinarith
  have hm := hbound J T hT A hA hbeta
    (fun rho hr => And.intro (hlow rho hr) (hupper rho hr))
  refine And.intro (hInt A hA hbeta) ?_
  convert hm using 1
  dsimp [mass, Z, F, M]
  ring

theorem movingSquareTest_actual_left_zero_finite_moment :
    Exists fun C0 : Real => Exists fun C1 : Real => 1 <= C0 /\ 1 <= C1 /\
      forall X eta : Real, 16 <= X -> 0 < eta ->
      forall A : Finset Complex,
      (forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) ->
      (forall rho, (A : Set Complex) rho -> rho.re <= 1/2) ->
      MeasureTheory.IntegrableOn (fun x =>
        norm (Finset.sum A (fun rho => (Zeta23.zeroMult rho : Complex)*
          Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
            (Zeta23.gammaOf rho)))^4) (Set.Icc X (2*X)) /\
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
        (fun x => norm (Finset.sum A (fun rho => (Zeta23.zeroMult rho : Complex)*
          Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
            (Zeta23.gammaOf rho)))^4) <=
        (66060288000*C0^4*(Real.log (8*Real.sqrt X))^5+
          1123024896000*C1^4*(MeasureTheory.integral
            (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
            (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4))*
            (Real.log (16*Real.sqrt X))^5)*X^2*Real.sqrt X := by
  classical
  obtain lo := movingSquareTest_actual_left_zero_low_moment
  obtain hi := movingSquareTest_actual_left_zero_tail_moment
  let C0 : Real := lo.choose
  let C1 : Real := hi.choose
  refine Exists.intro C0 (Exists.intro C1
    (And.intro lo.choose_spec.1 (And.intro hi.choose_spec.1 ?_)))
  intro X eta hX he A hA hbeta
  let S : Real := Real.sqrt X
  let M : Real := MeasureTheory.integral
    (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1))
    (fun v => norm (deriv (deriv (logWindowProfile eta)) v)^4)
  let Z : Finset Complex -> Real -> Complex := fun B x =>
    Finset.sum B (fun rho => (Zeta23.zeroMult rho : Complex)*
      Zeta23.paperFT (scaledLogWindowTest eta (movingSquareLogWidth x) (Real.log x))
        (Zeta23.gammaOf rho))
  let mass : Finset Complex -> Real := fun B =>
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc X (2*X)))
      (fun x => norm (Z B x)^4)
  have hS1 : 1 <= S := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (by linarith : (1 : Real) <= X)
  have hSn : Not (S = 0) := ne_of_gt (by linarith : 0 < S)
  have hs : S^2 = X := Real.sq_sqrt (by linarith)
  have hlowScale : X*S^3 = X^2*S := by
    calc
      X*S^3 = X*S^2*S := by ring
      _ = X*X*S := by rw [hs]
      _ = _ := by ring
  have hhighScale : X^5/S^5 = X^2*S := by
    calc
      X^5/S^5 = (S^2)^5/S^5 := by rw [hs]
      _ = S^5 := by field_simp [hSn]
      _ = (S^2)^2*S := by ring
      _ = _ := by rw [hs]
  let A0 : Finset Complex := Finset.filter (fun rho : Complex => abs rho.im <= S) A
  let A1 : Finset Complex := Finset.filter (fun rho : Complex => Not (abs rho.im <= S)) A
  have hA0 (rho : Complex) (hr : (A0 : Set Complex) rho) :
      Zeta23.IsNontrivialZero rho := hA rho (Finset.mem_filter.mp hr).1
  have hb0 (rho : Complex) (hr : (A0 : Set Complex) rho) :
      rho.re <= 1/2 := hbeta rho (Finset.mem_filter.mp hr).1
  have hA1 (rho : Complex) (hr : (A1 : Set Complex) rho) :
      Zeta23.IsNontrivialZero rho := hA rho (Finset.mem_filter.mp hr).1
  have hb1 (rho : Complex) (hr : (A1 : Set Complex) rho) :
      rho.re <= 1/2 := hbeta rho (Finset.mem_filter.mp hr).1
  have h0 := lo.choose_spec.2 X eta S hX he hS1 A0 hA0 hb0
    (fun rho hr => (Finset.mem_filter.mp hr).2)
  have h1 := hi.choose_spec.2 X eta S hX he hS1 A1 hA1 hb1
    (fun rho hr => lt_of_not_ge (Finset.mem_filter.mp hr).2)
  have hfull : MeasureTheory.IntegrableOn
      (fun x => norm (Z A x)^4) (Set.Icc X (2*X)) :=
    (movingSquareTest_finite_packet_low_energy A
      (fun rho : Complex => rho) (fun rho => (Zeta23.zeroMult rho : Complex))
      hX he (by norm_num : (1/2 : Real) <= 1)
      (fun rho hr => And.intro (hA rho hr).2.1.le (hbeta rho hr))).1
  have hsplit (x : Real) : Z A x = Z A0 x+Z A1 x := by
    dsimp [Z, A0, A1]
    rw [Finset.sum_filter, Finset.sum_filter, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro rho hr
    by_cases hd : abs rho.im <= S
    next =>
      simp only [hd, if_true, not_true_eq_false, if_false, add_zero]
    next =>
      simp only [hd, if_false, not_false_eq_true, if_true, zero_add]
  have hpoint (x : Real) :
      norm (Z A x)^4 <= 8*(norm (Z A0 x)^4+norm (Z A1 x)^4) := by
    rw [hsplit]
    let a : Real := norm (Z A0 x)
    let b : Real := norm (Z A1 x)
    have ha : 0 <= a := norm_nonneg _
    have hb : 0 <= b := norm_nonneg _
    have hn := norm_add_le (Z A0 x) (Z A1 x)
    have hn2 : norm (Z A0 x+Z A1 x)^2 <= (a+b)^2 := by
      simpa only [pow_two] using mul_le_mul hn hn (norm_nonneg _) (add_nonneg ha hb)
    have hn4 : norm (Z A0 x+Z A1 x)^4 <= (a+b)^4 := by
      calc
        norm (Z A0 x+Z A1 x)^4 =
            norm (Z A0 x+Z A1 x)^2*norm (Z A0 x+Z A1 x)^2 := by ring
        _ <= (a+b)^2*(a+b)^2 := mul_le_mul hn2 hn2 (sq_nonneg _) (sq_nonneg _)
        _ = (a+b)^4 := by ring
    have hp : 0 <= (a-b)^2*(7*a^2+10*a*b+7*b^2) :=
      mul_nonneg (sq_nonneg _) (add_nonneg
        (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (mul_nonneg (mul_nonneg (by norm_num) ha) hb))
        (mul_nonneg (by norm_num) (sq_nonneg _)))
    calc
      _ <= (a+b)^4 := hn4
      _ <= 8*(a^4+b^4) := by nlinarith [hp]
  have htri : mass A <= 8*(mass A0+mass A1) := by
    have hm := MeasureTheory.integral_mono hfull ((h0.1.add h1.1).const_mul 8) hpoint
    simp only [Pi.add_apply] at hm
    simpa only [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add h0.1 h1.1] using hm
  refine And.intro hfull ?_
  calc
    mass A <= 8*(mass A0+mass A1) := htri
    _ <= 8*(8257536000*C0^4*X*S^3*(Real.log (8*S))^5+
        140378112000*C1^4*M*X^5/S^5*(Real.log (16*S))^5) :=
      mul_le_mul_of_nonneg_left (_root_.add_le_add h0.2 h1.2) (by norm_num)
    _ = 8*(8257536000*C0^4*(X*S^3)*(Real.log (8*S))^5+
        140378112000*C1^4*M*(X^5/S^5)*(Real.log (16*S))^5) := by ring
    _ = _ := by rw [hlowScale, hhighScale]; ring

end RobinBV.Sieve
