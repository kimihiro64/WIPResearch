/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.SelbergSieve.IntervalSetup

/-!
# A finite two-coordinate Selberg upper sieve

The actual normalized finite Selberg weights are applied to both coordinates
of a finite pair set. The complete signed divisor matrix is expanded before
its remainder is bounded; no optimizer or product-independence assumption
is inserted. Every supported divisor is at most the square of the cutoff.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat

theorem sum_divisors_restricted_eq_gcd {P : Nat} (hP : Not (P = 0))
    (m : Nat) (mu : Nat -> Real) :
    P.divisors.sum (fun d => if Dvd.dvd d m then mu d else 0) =
      (Nat.gcd P m).divisors.sum mu := by
  rw [<- Finset.sum_filter]
  have he : P.divisors.filter (fun d => Dvd.dvd d m) = (Nat.gcd P m).divisors := by
    rw [<- Nat.divisors_filter_dvd_of_dvd hP (Nat.gcd_dvd_left P m)]
    ext d
    simp only [Finset.mem_filter, Nat.dvd_gcd_iff]
    constructor
    next => exact fun h => And.intro h.1 (And.intro (Nat.dvd_of_mem_divisors h.1) h.2)
    next => exact fun h => And.intro h.1 h.2.2
  rw [he]

def tensorDivisorCount (A : Finset (Prod Nat Nat)) (a b : Nat) : Nat :=
  (A.filter (fun x => Dvd.dvd a x.1 /\ Dvd.dvd b x.2)).card

theorem tensorDivisorCount_eq_sum (A : Finset (Prod Nat Nat)) (a b : Nat) :
    (tensorDivisorCount A a b : Real) =
      A.sum (fun x => if Dvd.dvd a x.1 /\ Dvd.dvd b x.2 then (1 : Real) else 0) := by
  unfold tensorDivisorCount
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]

theorem tensor_sifted_card_le_divisor_sum (A : Finset (Prod Nat Nat))
    {P : Nat} (hP : Not (P = 0)) (mu : Nat -> Real)
    (hmu : BoundingSieve.IsUpperMoebius mu) :
    ((A.filter (fun x => Nat.Coprime P x.1 /\ Nat.Coprime P x.2)).card : Real) <=
      P.divisors.sum (fun a => P.divisors.sum (fun b =>
        mu a*mu b*(tensorDivisorCount A a b : Real))) := by
  let v := fun m => P.divisors.sum (fun d => if Dvd.dvd d m then mu d else 0)
  have hv : forall m, (if Nat.Coprime P m then (1 : Real) else 0) <= v m := by
    intro m
    dsimp [v]
    rw [sum_divisors_restricted_eq_gcd hP]
    exact hmu (Nat.gcd P m)
  have hv0 : forall m, (0 : Real) <= v m := by
    intro m
    have h := hv m
    split_ifs at h <;> linarith
  have hpoint : forall x : Prod Nat Nat,
      (if Nat.Coprime P x.1 /\ Nat.Coprime P x.2 then (1 : Real) else 0) <=
        v x.1*v x.2 := by
    intro x
    by_cases h1 : Nat.Coprime P x.1
    next =>
      by_cases h2 : Nat.Coprime P x.2
      next =>
        have ha := hv x.1
        have hb := hv x.2
        simp only [if_pos h1] at ha
        simp only [if_pos h2] at hb
        rw [if_pos (And.intro h1 h2)]
        nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
      next => simpa only [h2, and_false, if_false] using mul_nonneg (hv0 x.1) (hv0 x.2)
    next => simpa only [h1, false_and, if_false] using mul_nonneg (hv0 x.1) (hv0 x.2)
  have hexpand :
      A.sum (fun x => v x.1*v x.2) =
        P.divisors.sum (fun a => P.divisors.sum (fun b =>
          A.sum (fun x => (if Dvd.dvd a x.1 then mu a else 0)*
            (if Dvd.dvd b x.2 then mu b else 0)))) := by
    dsimp [v]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  calc
    _ = A.sum (fun x =>
        if Nat.Coprime P x.1 /\ Nat.Coprime P x.2 then (1 : Real) else 0) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one, Finset.sum_filter]
    _ <= A.sum (fun x => v x.1*v x.2) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := by
      rw [hexpand]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [tensorDivisorCount_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases ha : Dvd.dvd a x.1 <;> by_cases hb : Dvd.dvd b x.2 <;> simp [ha, hb]

theorem tensor_sifted_card_le_main_error (A : Finset (Prod Nat Nat))
    {P : Nat} (hP : Not (P = 0)) (mu : Nat -> Real)
    (hmu : BoundingSieve.IsUpperMoebius mu) (M E : Real)
    (hR : forall a, Membership.mem P.divisors a ->
      forall b, Membership.mem P.divisors b ->
      Not (mu a = 0) -> Not (mu b = 0) ->
      abs ((tensorDivisorCount A a b : Real)-M/((a : Real)*b)) <= E) :
    ((A.filter (fun x => Nat.Coprime P x.1 /\ Nat.Coprime P x.2)).card : Real) <=
      M*(P.divisors.sum (fun a => mu a/(a : Real)))^2+
        E*(P.divisors.sum (fun a => abs (mu a)))^2 := by
  have hpoint : forall a, Membership.mem P.divisors a ->
      forall b, Membership.mem P.divisors b ->
      mu a*mu b*(tensorDivisorCount A a b : Real) <=
        mu a*mu b*(M/((a : Real)*b))+abs (mu a)*abs (mu b)*E := by
    intro a ha b hb
    by_cases haz : mu a = 0
    next => simp [haz]
    next =>
      by_cases hbz : mu b = 0
      next => simp [hbz]
      next =>
        have h := hR a ha b hb haz hbz
        have hmul := _root_.mul_le_mul_of_nonneg_left h (abs_nonneg (mu a*mu b))
        have habs := le_abs_self
          ((mu a*mu b)*((tensorDivisorCount A a b : Real)-M/((a : Real)*b)))
        rw [abs_mul, abs_mul] at habs
        rw [abs_mul] at hmul
        nlinarith only [hmul, habs]
  have hmain :
      P.divisors.sum (fun a => P.divisors.sum (fun b =>
        mu a*mu b*(M/((a : Real)*b)))) =
          M*(P.divisors.sum (fun a => mu a/(a : Real)))^2 := by
    rw [pow_two]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have herr :
      P.divisors.sum (fun a => P.divisors.sum (fun b =>
        abs (mu a)*abs (mu b)*E)) =
          E*(P.divisors.sum (fun a => abs (mu a)))^2 := by
    rw [pow_two]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  calc
    _ <= P.divisors.sum (fun a => P.divisors.sum (fun b =>
        mu a*mu b*(tensorDivisorCount A a b : Real))) :=
      tensor_sifted_card_le_divisor_sum A hP mu hmu
    _ <= P.divisors.sum (fun a => P.divisors.sum (fun b =>
        mu a*mu b*(M/((a : Real)*b))+abs (mu a)*abs (mu b)*E)) :=
      Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hpoint a ha b hb))
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [hmain, herr]

theorem lambdaSquared_support_le_square {P Q d : Nat} (w : Nat -> Real)
    (hd : Dvd.dvd d P)
    (hw : forall a, Dvd.dvd a P -> Q < a -> w a = 0)
    (hne : Not (BoundingSieve.lambdaSquared w d = 0)) : d <= Q*Q := by
  by_contra hbad
  apply hne
  unfold BoundingSieve.lambdaSquared
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  by_cases he : d = Nat.lcm a b
  next =>
    rw [if_pos he]
    by_cases haQ : a <= Q
    next =>
      by_cases hbQ : b <= Q
      next =>
        have hle : d <= Q*Q := by
          rw [he]
          exact (Nat.lcm_le_mul (Nat.pos_of_mem_divisors ha)
            (Nat.pos_of_mem_divisors hb)).trans (Nat.mul_le_mul haQ hbQ)
        exact False.elim (hbad hle)
      next =>
        rw [hw b ((Nat.dvd_of_mem_divisors hb).trans hd) (by omega), mul_zero]
    next =>
      rw [hw a ((Nat.dvd_of_mem_divisors ha).trans hd) (by omega), zero_mul]
  next => exact if_neg he

set_option maxHeartbeats 400000 in
theorem tensor_sifted_card_le_log_sieve (A : Finset (Prod Nat Nat))
    {Q : Nat} (hQ : 1 <= Q) (M E : Real) (hM : 0 <= M) (hE : 0 <= E)
    (hR : forall a, 0 < a -> a <= Q*Q -> forall b, 0 < b -> b <= Q*Q ->
      abs ((tensorDivisorCount A a b : Real)-M/((a : Real)*b)) <= E) :
    ((A.filter (fun x => Nat.Coprime (selbergPrimeProduct Q) x.1 /\
      Nat.Coprime (selbergPrimeProduct Q) x.2)).card : Real) <=
        M/(Real.log ((Q : Real)+1))^2+E*(Q : Real)^4 := by
  let s := intervalReciprocalSieve 0 0 Q
  let D := selbergDivisorSupport Q
  let P := selbergPrimeProduct Q
  let w := s.finiteSelbergWeights D
  let mu := BoundingSieve.lambdaSquared w
  let H := squarefreeReciprocalTotientSum Q
  have hP : Not (P = 0) := (selbergPrimeProduct_squarefree Q).ne_zero
  have hD : forall d, Membership.mem D d -> Dvd.dvd d s.prodPrimes :=
    fun d hd => selbergDivisorSupport_dvd hd
  have hdown : forall d, Membership.mem D d -> forall k, Dvd.dvd k d -> Membership.mem D k :=
    fun d hd k hk => selbergDivisorSupport_down hd hk
  have h1 : Membership.mem D 1 := one_mem_selbergDivisorSupport hQ
  have hw1 : w 1 = 1 := s.finiteSelbergWeights_one D hD h1
  have hmu : BoundingSieve.IsUpperMoebius mu :=
    BoundingSieve.upperMoebius_lambdaSquared w hw1
  have hwzero : forall a, Dvd.dvd a P -> Q < a -> w a = 0 := by
    intro a ha hQa
    apply s.finiteSelbergWeights_eq_zero_of_not_mem D hD hdown ha
    intro hmem
    have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1
    omega
  have hmusupport : forall a, Membership.mem P.divisors a -> Not (mu a = 0) -> a <= Q*Q := by
    intro a ha hne
    exact lambdaSquared_support_le_square w (Nat.dvd_of_mem_divisors ha) hwzero hne
  have hrows : forall a, Membership.mem P.divisors a ->
      forall b, Membership.mem P.divisors b -> Not (mu a = 0) -> Not (mu b = 0) ->
      abs ((tensorDivisorCount A a b : Real)-M/((a : Real)*b)) <= E := by
    intro a ha b hb hma hmb
    exact hR a (Nat.pos_of_mem_divisors ha) (hmusupport a ha hma)
      b (Nat.pos_of_mem_divisors hb) (hmusupport b hb hmb)
  have hmain : P.divisors.sum (fun a => mu a/(a : Real)) = Inv.inv H := by
    have h := s.finiteSelbergWeights_main D hD h1
    have hden : s.finiteSelbergDenominator D = H :=
      intervalReciprocalSieve_denominator 0 0 Q
    rw [hden] at h
    change P.divisors.sum (fun a => mu a*Inv.inv (a : Real)) = Inv.inv H at h
    simpa only [div_eq_mul_inv] using h
  have hwL1 : P.divisors.sum (fun a => abs (w a)) <= (Q : Real) := by
    have h := s.sum_abs_finiteSelbergWeights_le_card D hD hdown h1
    have hc : (D.card : Real) <= Q := by exact_mod_cast card_selbergDivisorSupport_le Q
    exact h.trans hc
  have hmuL1 : P.divisors.sum (fun a => abs (mu a)) <= (Q : Real)^2 := by
    calc
      _ <= P.divisors.sum (BoundingSieve.lambdaSquared (fun a => abs (w a))) :=
        Finset.sum_le_sum (fun a _ => BoundingSieve.abs_lambdaSquared_le w a)
      _ = (P.divisors.sum (fun a => abs (w a)))^2 :=
        BoundingSieve.sum_lambdaSquared_eq_square P (fun a => abs (w a))
      _ <= (Q : Real)^2 := by
        have h := _root_.mul_le_mul hwL1 hwL1
          (Finset.sum_nonneg (fun a _ => abs_nonneg (w a))) (Nat.cast_nonneg Q)
        simpa only [pow_two] using h
  have hmuSq : (P.divisors.sum (fun a => abs (mu a)))^2 <= (Q : Real)^4 := by
    have h := _root_.mul_le_mul hmuL1 hmuL1
      (Finset.sum_nonneg (fun a _ => abs_nonneg (mu a))) (sq_nonneg (Q : Real))
    nlinarith only [h]
  have hlog : 0 < Real.log ((Q : Real)+1) := by
    apply Real.log_pos
    have hQr : (1 : Real) <= Q := by exact_mod_cast hQ
    linarith
  have hden : Real.log ((Q : Real)+1) <= H := log_succ_le_squarefreeReciprocalTotientSum Q
  have hH : 0 < H := hlog.trans_le hden
  have hdenSq : (Real.log ((Q : Real)+1))^2 <= H^2 := by
    have h := mul_nonneg (sub_nonneg.mpr hden) (add_nonneg hH.le hlog.le)
    nlinarith only [h]
  have hratio : M*(Inv.inv H)^2 <= M/(Real.log ((Q : Real)+1))^2 := by
    calc
      _ = M/H^2 := by simp only [div_eq_mul_inv, inv_pow]
      _ <= _ := _root_.div_le_div_of_nonneg_left hM (by positivity) hdenSq
  have herr : E*(P.divisors.sum (fun a => abs (mu a)))^2 <= E*(Q : Real)^4 :=
    _root_.mul_le_mul_of_nonneg_left hmuSq hE
  have h := tensor_sifted_card_le_main_error A hP mu hmu M E hrows
  rw [hmain] at h
  exact h.trans (_root_.add_le_add hratio herr)

end Nat
