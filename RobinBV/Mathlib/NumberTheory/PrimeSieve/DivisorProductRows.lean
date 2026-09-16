/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Finset.Sigma
import RobinBV.Mathlib.Analysis.Complex.ReciprocalFloorError
import RobinBV.Mathlib.Analysis.SpecialFunctions.Log.DyadicHarmonic

/-!
# Divisor-product row counts

A finite set of actual products is identified with its paired floor count.
Reciprocal-phase estimates give a two-sided logarithmic main-term bound,
with all row-length, modulus and phase hypotheses explicit.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

def divisorProductRows (A B a b P N : Nat) : Finset (Prod Nat Nat) :=
  ((Finset.range N).sigma (fun i =>
    Finset.Ioc (A/(a*b*(P+i))) (B/(a*b*(P+i))))).image
      (fun x => Prod.mk (a*(P+x.1)) (b*x.2))

theorem divisorProductRows_card {A B a b P N : Nat} (ha : 0<a) (hb : 0<b) :
    (divisorProductRows A B a b P N).card =
      (Finset.range N).sum (fun i => B/(a*b*(P+i))-A/(a*b*(P+i))) := by
  have hinj : Function.Injective
      (fun x : Sigma (fun _ : Nat => Nat) => Prod.mk (a*(P+x.1)) (b*x.2)) := by
    intro x y h
    have h1 : a*(P+x.1)=a*(P+y.1) := congrArg Prod.fst h
    have h2 : b*x.2=b*y.2 := congrArg Prod.snd h
    have hi : x.1=y.1 := Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_left ha h1)
    have hj : x.2=y.2 := Nat.eq_of_mul_eq_mul_left hb h2
    exact Sigma.ext hi (heq_of_eq hj)
  unfold divisorProductRows
  rw [Finset.card_image_of_injective _ hinj, Finset.card_sigma]
  simp only [Nat.card_Ioc]

theorem floor_nat_ratio (a b : Nat) :
    Int.floor ((a:Real)/b) = ((a/b:Nat):Int) := by
  rw [Int.floor_div_natCast, Int.floor_natCast]
  norm_cast

theorem divisorProductRows_card_floor {A B a b P N : Nat}
    (hAB : A<=B) (ha : 0<a) (hb : 0<b) :
    ((divisorProductRows A B a b P N).card:Real) =
      (Finset.range N).sum (fun i =>
        ((Int.floor (((B:Real)/((a:Real)*b))/((P:Real)+i)):Int):Real) -
        ((Int.floor (((A:Real)/((a:Real)*b))/((P:Real)+i)):Int):Real)) := by
  rw [divisorProductRows_card ha hb, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hquot : A/(a*b*(P+i)) <= B/(a*b*(P+i)) := Nat.div_le_div_right hAB
  rw [Nat.cast_sub hquot]
  have heq (X : Nat) :
      ((X:Real)/((a:Real)*b))/((P:Real)+i) = (X:Real)/(a*b*(P+i):Nat) := by
    simp only [Nat.cast_mul, Nat.cast_add]
    rw [div_div]
  rw [heq B, heq A, floor_nat_ratio, floor_nat_ratio]
  norm_cast

theorem paired_floor_log_error {Xa Xb : Real} {P N t : Nat}
    (hP : 1<=P) (hNP : N<=P) (hPN : P<=N+1)
    (ht : 2<=t) (hscale : (t:Real)^15<=P)
    (hlow : (P:Real)^2<=2*Real.pi*Xa) (horder : Xa<=Xb)
    (hfreq : 4*Xb*(t:Real)^14<=(P:Real)^3) :
    abs ((Finset.range N).sum (fun i : Nat =>
        ((Int.floor (Xb/((P:Real)+i)):Int):Real) -
        ((Int.floor (Xa/((P:Real)+i)):Int):Real)) -
      (Xb-Xa)*Real.log 2) <= 40*(P:Real)/t + (Xb-Xa)/(P:Real) := by
  have hrow := Complex.reciprocal_floor_interval_error_power ht
    (show (N:Real)<=P by exact_mod_cast hNP) hscale hlow horder hfreq
  have hh := Real.dyadic_harmonic_abs_error hP hNP hPN
  have hnon : 0<=Xb-Xa := sub_nonneg.mpr horder
  have he : abs ((Xb-Xa)*
      ((Finset.range N).sum (fun i => 1/((P:Real)+i))-Real.log 2)) <=
      (Xb-Xa)/(P:Real) := by
    rw [abs_mul, abs_of_nonneg hnon]
    calc
      (Xb-Xa)*abs ((Finset.range N).sum (fun i => 1/((P:Real)+i))-Real.log 2)
          <= (Xb-Xa)*(1/(P:Real)) := mul_le_mul_of_nonneg_left hh hnon
      _ = _ := by ring
  calc
    _ = abs (((Finset.range N).sum (fun i : Nat =>
          ((Int.floor (Xb/((P:Real)+i)):Int):Real) -
          ((Int.floor (Xa/((P:Real)+i)):Int):Real)) -
        (Xb-Xa)*(Finset.range N).sum (fun i => 1/((P:Real)+i))) +
        (Xb-Xa)*((Finset.range N).sum (fun i => 1/((P:Real)+i))-Real.log 2)) := by
          congr 1
          ring
    _ <= _ := (abs_add_le _ _).trans (_root_.add_le_add hrow he)

theorem mem_divisorProductRows_iff {A B a b P N p q : Nat}
    (ha : 0<a) (hb : 0<b) (hP : 0<P) :
    Membership.mem (divisorProductRows A B a b P N) (Prod.mk p q) <->
      exists i, i<N /\ exists v, p=a*(P+i) /\ q=b*v /\ A<p*q /\ p*q<=B := by
  constructor
  case mp =>
    intro h
    choose x hx using (Finset.mem_image.mp h)
    have hs := Finset.mem_sigma.mp hx.1
    have hv := Finset.mem_Ioc.mp hs.2
    have hp : a*(P+x.1)=p := congrArg Prod.fst hx.2
    have hq : b*x.2=q := congrArg Prod.snd hx.2
    have hd : 0<a*b*(P+x.1) := by positivity
    have heq : x.2*(a*b*(P+x.1))=p*q := by
      rw [<- hp, <- hq]
      ring
    have hlo : A<p*q := by
      have hh := (Nat.div_lt_iff_lt_mul hd).mp hv.1
      simpa only [heq] using hh
    have hhi : p*q<=B := by
      have hh := (Nat.le_div_iff_mul_le hd).mp hv.2
      simpa only [heq] using hh
    exact Exists.intro x.1 (And.intro (Finset.mem_range.mp hs.1)
      (Exists.intro x.2 (And.intro hp.symm
        (And.intro hq.symm (And.intro hlo hhi)))))
  case mpr =>
    intro h
    choose i hi using h
    choose v hv using hi.2
    have hd : 0<a*b*(P+i) := by positivity
    have heq : v*(a*b*(P+i))=p*q := by
      rw [hv.1, hv.2.1]
      ring
    apply Finset.mem_image.mpr
    refine Exists.intro (Sigma.mk i v) (And.intro ?_ ?_)
    exact Finset.mem_sigma.mpr (And.intro (Finset.mem_range.mpr hi.1)
      (Finset.mem_Ioc.mpr (And.intro
        ((Nat.div_lt_iff_lt_mul hd).mpr (by simpa only [heq] using hv.2.2.1))
        ((Nat.le_div_iff_mul_le hd).mpr (by simpa only [heq] using hv.2.2.2)))))
    exact Prod.ext hv.1.symm hv.2.1.symm

theorem divisorProductRows_log_error {A B a b P N t : Nat}
    (hAB : A<=B) (ha : 0<a) (hb : 0<b)
    (hP : 1<=P) (hNP : N<=P) (hPN : P<=N+1)
    (ht : 2<=t) (hscale : (t:Real)^15<=P)
    (hlow : (P:Real)^2<=2*Real.pi*((A:Real)/((a:Real)*b)))
    (hfreq : 4*((B:Real)/((a:Real)*b))*(t:Real)^14<=(P:Real)^3) :
    abs (((divisorProductRows A B a b P N).card:Real) -
      (((B:Real)-A)/((a:Real)*b))*Real.log 2) <=
      40*(P:Real)/t + (((B:Real)-A)/((a:Real)*b))/(P:Real) := by
  rw [divisorProductRows_card_floor hAB ha hb, sub_div]
  apply paired_floor_log_error hP hNP hPN ht hscale hlow
  exact div_le_div_of_nonneg_right (by exact_mod_cast hAB) (by positivity)
  exact hfreq

end Nat.PrimeSieve
