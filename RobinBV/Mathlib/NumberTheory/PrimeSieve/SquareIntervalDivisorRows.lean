/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.DivisorProductRows
import RobinBV.Mathlib.NumberTheory.PrimeSieve.HalfDivisorPhase

/-!
# Divisor pairs in the balanced square-interval band

The finite row set is exactly the set of products with the prescribed two
divisibilities and n/2 < p <= n, n^2 < p*q <= n^2+2*n. Its logarithmic
main term has an explicit two-sided error under polynomial size conditions.
This is a composite-count input, not a prime-existence theorem.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

def balancedDivisorRows (n a b : Nat) : Finset (Prod Nat Nat) :=
  divisorProductRows (n*n) (n*n+2*n) a b
    (n/(2*a)+1) (n/a-n/(2*a))

theorem mem_balancedDivisorRows_iff {n a b p q : Nat}
    (ha : 0<a) (hb : 0<b) :
    Membership.mem (balancedDivisorRows n a b) (Prod.mk p q) <->
      Dvd.dvd a p /\ Dvd.dvd b q /\ n<2*p /\ p<=n /\ n*n<p*q /\ p*q<=n*n+2*n := by
  have h2a : 0<2*a := by omega
  have he : (n/a)/2=n/(2*a) := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    ring
  have hsub : n/(2*a)<=n/a := by
    rw [<- he]
    exact Nat.div_le_self (n/a) 2
  unfold balancedDivisorRows
  rw [mem_divisorProductRows_iff ha hb (Nat.zero_lt_succ (n/(2*a)))]
  constructor
  case mp =>
    intro h
    choose i hi using h
    choose v hv using hi.2
    have hrowlo : n/(2*a)<n/(2*a)+1+i := by omega
    have hrowhi : n/(2*a)+1+i<=n/a := by omega
    have hlo := (Nat.div_lt_iff_lt_mul h2a).mp hrowlo
    have hhi := (Nat.le_div_iff_mul_le ha).mp hrowhi
    have hpn : n<2*p := by nlinarith [hv.1]
    have hnp : p<=n := by nlinarith [hv.1]
    exact And.intro (Exists.intro (n/(2*a)+1+i) hv.1)
      (And.intro (Exists.intro v hv.2.1)
        (And.intro hpn (And.intro hnp hv.2.2)))
  case mpr =>
    intro h
    choose u hu using h.1
    choose v hv using h.2.1
    have hrowlo : n/(2*a)<u := by
      apply (Nat.div_lt_iff_lt_mul h2a).mpr
      nlinarith [h.2.2.1]
    have hrowhi : u<=n/a := by
      apply (Nat.le_div_iff_mul_le ha).mpr
      nlinarith [h.2.2.2.1]
    let i := u-(n/(2*a)+1)
    have hi : i<n/a-n/(2*a) := by dsimp [i]; omega
    have heq : n/(2*a)+1+i=u := by dsimp [i]; omega
    exact Exists.intro i (And.intro hi (Exists.intro v
      (And.intro (by simpa only [heq] using hu)
        (And.intro hv h.2.2.2.2))))

theorem balancedDivisorRows_abs_error {n a b t : Nat}
    (hn : 2<=n) (ha : 0<a) (hb : 0<b) (hba : b<=a) (ht : 2<=t)
    (hnscale : 2*a*t^15<=n) (hbudget : 64*a^2*t^14<=n*b) :
    abs (((balancedDivisorRows n a b).card:Real) -
      (2*(n:Real)/((a:Real)*b))*Real.log 2) <=
      40*(n:Real)/((a:Real)*t)+4/(b:Real) := by
  let P : Nat := n/(2*a)+1
  let N : Nat := n/a-n/(2*a)
  have hshape := half_divisor_row_shape n a
  have hphase := half_divisor_phase_conditions hn ha hb hba ht hnscale hbudget
  have hP : 1<=P := Nat.succ_le_succ (Nat.zero_le _)
  have hraw := divisorProductRows_log_error (A:=n*n) (B:=n*n+2*n)
    (a:=a) (b:=b) (P:=P) (N:=N) (t:=t)
    (by omega) ha hb hP hshape.1 hshape.2 ht hphase.1
    (by simpa only [Nat.cast_mul, pow_two] using hphase.2.1)
    (by simpa only [P, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_two]
      using hphase.2.2)
  have hdelta : (((n*n+2*n:Nat):Real)-((n*n:Nat):Real)) = 2*(n:Real) := by
    push_cast
    ring
  rw [hdelta] at hraw
  have htpos : 0<t := by omega
  have ht15 := pow_pos htpos 15
  have hna : 2*a<=n := by nlinarith
  have hr := half_divisor_row_real_bounds ha hna
  have haR : (0:Real)<a := by exact_mod_cast ha
  have hbR : (0:Real)<b := by exact_mod_cast hb
  have htR : (0:Real)<t := by exact_mod_cast htpos
  have hpR : (0:Real)<P := by exact_mod_cast (show 0<P by omega)
  have han : Not ((a:Real)=0) := ne_of_gt haR
  have hbn : Not ((b:Real)=0) := ne_of_gt hbR
  have htn : Not ((t:Real)=0) := ne_of_gt htR
  have hpn : Not ((P:Real)=0) := ne_of_gt hpR
  have hmain : 40*(P:Real)/t<=40*(n:Real)/((a:Real)*t) := by
    calc
      40*(P:Real)/t = (40*((P:Real)*a))/((a:Real)*t) := by
        field_simp
        <;> ring
      _ <= _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr.2 (by norm_num))
        (by positivity)
  have herr : (2*(n:Real)/((a:Real)*b))/(P:Real)<=4/(b:Real) := by
    calc
      _ = (2*(n:Real))/((a:Real)*b*P) := by rw [div_div]
      _ <= (4*(a:Real)*P)/((a:Real)*b*P) :=
        div_le_div_of_nonneg_right (by nlinarith [hr.1]) (by positivity)
      _ = 4/(b:Real) := by field_simp <;> ring
  exact hraw.trans (_root_.add_le_add hmain herr)

end Nat.PrimeSieve
