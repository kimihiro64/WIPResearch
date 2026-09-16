/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalJointRemainder

/-!
# Same-divisor transport through all quadratic factor layers

An old factor pair (d,r) above the diagonal transports to (d,r+2).
The lower endpoint is automatic; at each fixed quadratic center at most
one old pair fails the upper endpoint. The exact signed paired floor is
computed without imposing a sign on its arithmetic coefficient.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- An old live factor pair above the successor diagonal has cofactor at most n. -/
theorem old_large_pair_cofactor_le {n d r : Nat}
    (hd : n+1 < d) (hupper : d*r <= n*n+2*n) : r <= n := by
  by_contra h
  have hdge : n+2 <= d := by omega
  have hrge : n+1 <= r := by omega
  have hp := Nat.mul_le_mul hdge hrge
  nlinarith

/-- Adding two to the old odd cofactor always passes the next lower-square endpoint. -/
theorem old_pair_transport_lower {n d r : Nat}
    (hd : n+1 < d) (hlower : n*n < d*r) :
    (n+1)*(n+1) < d*(r+2) := by nlinarith

/-- In one quadratic center, any larger odd divisor than an old pair passes the new upper endpoint. -/
theorem same_center_larger_pair_transports {n d r e t : Nat}
    (hd : n+1 < d) (hdodd : d % 2 = 1) (heodd : e % 2 = 1)
    (hde : d < e) (hcenter : d+r = e+t)
    (hupper : d*r <= n*n+2*n) : e*(t+2) < (n+2)*(n+2) := by
  have hr := old_large_pair_cofactor_le hd hupper
  have hgap : d+2 <= e := by omega
  let u := e-(d+2)
  have heu : d+2+u = e := by dsimp [u]; omega
  have hru : t+u+2 = r := by omega
  have hmul := Nat.mul_le_mul_left u (show r <= e by omega)
  have hleft := congrArg (fun z : Nat => e*z) hru
  have hright := congrArg (fun z : Nat => z*r) heu
  have hcross : e*(t+2) <= (d+2)*r := by nlinarith
  nlinarith

/-- At most one old pair per quadratic center fails transport to the successor interval. -/
theorem failed_old_transport_center_unique {n d r e t : Nat}
    (hd : n+1 < d) (he : n+1 < e)
    (hdodd : d % 2 = 1) (heodd : e % 2 = 1)
    (hcenter : d+r = e+t)
    (hdtop : d*r <= n*n+2*n) (hetop : e*t <= n*n+2*n)
    (hdfail : (n+2)*(n+2) <= d*(r+2))
    (hefail : (n+2)*(n+2) <= e*(t+2)) : d = e /\ r = t := by
  have hde : d = e := by
    rcases lt_trichotomy d e with h | h | h
    next =>
      have ht := same_center_larger_pair_transports hd hdodd heodd h hcenter hdtop
      omega
    next => exact h
    next =>
      have ht := same_center_larger_pair_transports he heodd hdodd h hcenter.symm hetop
      omega
  exact And.intro hde (by omega)

/-- A failed upper-endpoint transport excludes every new odd multiple of the same divisor. -/
theorem old_pair_failed_transport_new_floor_zero {n d r : Nat}
    (hd : n+1 < d) (hdodd : d % 2 = 1) (hrodd : r % 2 = 1)
    (hupper : d*r <= n*n+2*n) (hfail : (n+2)*(n+2) <= d*(r+2)) :
    oddSquareFloor (n+1) d = 0 := by
  rw [oddSquareFloor_large_divisor n (by omega) hd hdodd]
  apply Finset.sum_eq_zero
  intro q hq
  apply if_neg
  intro h
  have hrq : r < q := by
    by_contra hbad
    have hle : q <= r := by omega
    have hp := Nat.mul_le_mul_left d hle
    nlinarith [h.2.1]
  have hrq2 : r+2 <= q := by omega
  have hp := Nat.mul_le_mul_left d hrq2
  nlinarith [h.2.2]

/-- Exact same-divisor paired-floor cancellation in every old quadratic layer, not only the first. -/
theorem paired_floor_of_old_pair {n d r : Nat}
    (hd : n+1 < d) (hdodd : d % 2 = 1) (hrodd : r % 2 = 1)
    (hlower : n*n < d*r) (hupper : d*r <= n*n+2*n) :
    2 * oddSquareFloor (n+1) d - oddSquareFloor n d =
      if d*(r+2) < (n+2)*(n+2) then (1 : Int) else -1 := by
  rw [oddSquareFloor_eq_one_of_odd_cofactor (by omega) hdodd hrodd hlower
    (show d*r < (n+1)*(n+1) by nlinarith)]
  by_cases hnext : d*(r+2) < (n+2)*(n+2)
  next =>
    have hfloor := oddSquareFloor_eq_one_of_odd_cofactor hd hdodd
      (show (r+2) % 2 = 1 by omega) (old_pair_transport_lower hd hlower)
      (show d*(r+2) < ((n+1)+1)*((n+1)+1) by nlinarith)
    simp [hnext, hfloor]
  next =>
    have hfloor := old_pair_failed_transport_new_floor_zero hd hdodd hrodd hupper
      (show (n+2)*(n+2) <= d*(r+2) by omega)
    simp [hnext, hfloor]

/-- Subtracting two from a new cofactor passes the old upper-square endpoint. -/
theorem new_pair_transport_upper {n d r : Nat}
    (hd : n+1 < d) (hr : 2 <= r)
    (hupper : d*r <= (n+1)*(n+1)+2*(n+1)) :
    d*(r-2) < (n+1)*(n+1) := by
  have he : r-2+2 = r := by omega
  have hp := congrArg (fun z : Nat => d*z) he
  nlinarith

/-- In one new quadratic center, every smaller odd divisor than a new pair passes the old lower endpoint. -/
theorem same_center_smaller_new_pair_transports {n d r e t : Nat}
    (hd : n+1 < d) (hdodd : d % 2 = 1) (heodd : e % 2 = 1)
    (hde : d < e) (hcenter : d+r = e+t)
    (hlower : (n+1)*(n+1) < e*t)
    (hupper : e*t <= (n+1)*(n+1)+2*(n+1)) :
    n*n < d*(r-2) := by
  have hgap : d+2 <= e := by omega
  have ht := large_divisor_cofactor_bound (n := n) (x := n+1) (by omega)
    (show n+1 < e by omega) hupper
  let u := e-(d+2)
  let v := r-2
  have heu : d+2+u = e := by dsimp [u]; omega
  have hrv : v = t+u := by dsimp [v]; omega
  have hp := Nat.mul_le_mul_left u (show t <= d by omega)
  have hleft := congrArg (fun z : Nat => d*z) hrv
  have hright := congrArg (fun z : Nat => z*t) heu
  have hcompare : e*t <= d*v+2*t := by nlinarith
  change n*n < d*v
  by_contra hbad
  have hsmall : d*v <= n*n := by omega
  have htge : n+1 <= t := by nlinarith
  have hteq : t = n+1 := by omega
  have hege : n+4 <= e := by omega
  have hprod := Nat.mul_le_mul_right (n+1) hege
  rw [hteq] at hcompare
  nlinarith

/-- At most one new pair per quadratic center fails reverse transport to the old interval. -/
theorem failed_new_transport_center_unique {n d r e t : Nat}
    (hd : n+1 < d) (he : n+1 < e)
    (hdodd : d % 2 = 1) (heodd : e % 2 = 1)
    (hcenter : d+r = e+t)
    (hdlower : (n+1)*(n+1) < d*r) (helower : (n+1)*(n+1) < e*t)
    (hdtop : d*r <= (n+1)*(n+1)+2*(n+1))
    (hetop : e*t <= (n+1)*(n+1)+2*(n+1))
    (hdfail : d*(r-2) <= n*n) (hefail : e*(t-2) <= n*n) : d = e /\ r = t := by
  have hde : d = e := by
    rcases lt_trichotomy d e with h | h | h
    next =>
      have ht := same_center_smaller_new_pair_transports hd hdodd heodd h hcenter helower hetop
      omega
    next => exact h
    next =>
      have ht := same_center_smaller_new_pair_transports he heodd hdodd h hcenter.symm hdlower hdtop
      omega
  exact And.intro hde (by omega)

/-- A failed reverse lower-endpoint transport excludes every old odd multiple of the divisor. -/
theorem new_pair_failed_transport_old_floor_zero {n d r : Nat}
    (hd : n+1 < d) (hdodd : d % 2 = 1) (hrodd : r % 2 = 1)
    (hlower : (n+1)*(n+1) < d*r) (hfail : d*(r-2) <= n*n) :
    oddSquareFloor n d = 0 := by
  rw [oddSquareFloor_large_divisor n (by omega) hd hdodd]
  apply Finset.sum_eq_zero
  intro q hq
  apply if_neg
  intro h
  have hqr : q < r := by
    by_contra hbad
    have hle : r <= q := by omega
    have hp := Nat.mul_le_mul_left d hle
    nlinarith [h.2.2]
  have hqr2 : q <= r-2 := by omega
  have hp := Nat.mul_le_mul_left d hqr2
  nlinarith [h.2.1]

/-- Exact same-divisor paired-floor cancellation in every new quadratic layer, including new-only pairs. -/
theorem paired_floor_of_new_pair {n d r : Nat}
    (hd : n+1 < d) (hdodd : d % 2 = 1) (hrodd : r % 2 = 1)
    (hlower : (n+1)*(n+1) < d*r)
    (hupper : d*r <= (n+1)*(n+1)+2*(n+1)) :
    2 * oddSquareFloor (n+1) d - oddSquareFloor n d =
      if n*n < d*(r-2) then (1 : Int) else 2 := by
  rw [oddSquareFloor_eq_one_of_odd_cofactor hd hdodd hrodd hlower
    (show d*r < ((n+1)+1)*((n+1)+1) by nlinarith)]
  by_cases hprev : n*n < d*(r-2)
  next =>
    have hr2 : 2 <= r := by
      by_contra h
      have hz : r-2 = 0 := by omega
      simp [hz] at hprev
    have hfloor := oddSquareFloor_eq_one_of_odd_cofactor (show n < d by omega) hdodd
      (show (r-2) % 2 = 1 by omega) hprev (new_pair_transport_upper hd hr2 hupper)
    simp [hprev, hfloor]
  next =>
    have hfloor := new_pair_failed_transport_old_floor_zero hd hdodd hrodd hlower
      (show d*(r-2) <= n*n by omega)
    simp [hprev, hfloor]

/-- The actual supported odd-divisor row at the specified quadratic factor center. -/
noncomputable def quadraticDivisorLayer (n h : Nat) (s : Finset Nat) : Finset Nat :=
  s.filter (fun d => exists r : Nat, r % 2 = 1 /\ d+r = 2*(n+h) /\
    n*n < d*r /\ d*r <= n*n+2*n)

/-- An old row divisor has paired weight one exactly when it also belongs to the aligned new row. -/
theorem quadraticLayer_old_paired_floor {n h d : Nat} {s : Finset Nat}
    (hd : n+1 < d) (hdodd : d % 2 = 1)
    (hold : Membership.mem (quadraticDivisorLayer n h s) d) :
    2 * oddSquareFloor (n+1) d - oddSquareFloor n d =
      if Membership.mem (quadraticDivisorLayer (n+1) h s) d then (1 : Int) else -1 := by
  have hm := Finset.mem_filter.mp hold
  choose r hr using hm.2
  have he : d*(r+2) < (n+2)*(n+2) <->
      Membership.mem (quadraticDivisorLayer (n+1) h s) d := by
    constructor
    next =>
      intro hnext
      apply Finset.mem_filter.mpr
      exact And.intro hm.1 (Exists.intro (r+2) (And.intro (by omega)
        (And.intro (by omega) (And.intro (old_pair_transport_lower hd hr.2.2.1)
          (by nlinarith)))))
    next =>
      intro hnew
      choose q hq using (Finset.mem_filter.mp hnew).2
      have hqr : q = r+2 := by omega
      rw [hqr] at hq
      nlinarith [hq.2.2.2]
  rw [paired_floor_of_old_pair hd hdodd hr.1 hr.2.2.1 hr.2.2.2]
  simp only [he]

/-- A new row divisor has paired weight one exactly when it also belongs to the aligned old row. -/
theorem quadraticLayer_new_paired_floor {n h d : Nat} {s : Finset Nat}
    (hd : n+1 < d) (hdodd : d % 2 = 1)
    (hnew : Membership.mem (quadraticDivisorLayer (n+1) h s) d) :
    2 * oddSquareFloor (n+1) d - oddSquareFloor n d =
      if Membership.mem (quadraticDivisorLayer n h s) d then (1 : Int) else 2 := by
  have hm := Finset.mem_filter.mp hnew
  choose r hr using hm.2
  have he : n*n < d*(r-2) <-> Membership.mem (quadraticDivisorLayer n h s) d := by
    constructor
    next =>
      intro hprev
      have hr2 : 2 <= r := by
        by_contra h
        have hz : r-2 = 0 := by omega
        simp [hz] at hprev
      apply Finset.mem_filter.mpr
      exact And.intro hm.1 (Exists.intro (r-2) (And.intro (by omega)
        (And.intro (by omega) (And.intro hprev (by
          have ht := new_pair_transport_upper hd hr2 hr.2.2.2
          nlinarith)))))
    next =>
      intro hold
      choose q hq using (Finset.mem_filter.mp hold).2
      have hqr : r-2 = q := by omega
      rw [hqr]
      exact hq.2.2.1
  rw [paired_floor_of_new_pair hd hdodd hr.1 hr.2.2.1 hr.2.2.2]
  simp only [he]

/-- Every actual quadratic row has at most one old-only divisor, after all support restrictions. -/
theorem quadraticLayer_old_only_card_le_one (n h : Nat) {s : Finset Nat}
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1) :
    ((quadraticDivisorLayer n h s).filter (fun d =>
      Not (Membership.mem (quadraticDivisorLayer (n+1) h s) d))).card <= 1 := by
  apply Finset.card_le_one.mpr
  intro d hd e he
  have hdm := Finset.mem_filter.mp hd
  have hem := Finset.mem_filter.mp he
  have hds := Finset.mem_filter.mp hdm.1
  have hes := Finset.mem_filter.mp hem.1
  choose r hr using hds.2
  choose t ht using hes.2
  have hddata := hs d hds.1
  have hedata := hs e hes.1
  have hdf := quadraticLayer_old_paired_floor hddata.1 hddata.2 hdm.1
  have hef := quadraticLayer_old_paired_floor hedata.1 hedata.2 hem.1
  rw [if_neg hdm.2] at hdf
  rw [if_neg hem.2] at hef
  have hdpf := paired_floor_of_old_pair hddata.1 hddata.2 hr.1 hr.2.2.1 hr.2.2.2
  have hepf := paired_floor_of_old_pair hedata.1 hedata.2 ht.1 ht.2.2.1 ht.2.2.2
  have hdfail : (n+2)*(n+2) <= d*(r+2) := by split_ifs at hdpf <;> omega
  have hefail : (n+2)*(n+2) <= e*(t+2) := by split_ifs at hepf <;> omega
  exact (failed_old_transport_center_unique hddata.1 hedata.1 hddata.2 hedata.2
    (by omega) hr.2.2.2 ht.2.2.2 hdfail hefail).1

/-- Every actual quadratic row has at most one new-only divisor, after all support restrictions. -/
theorem quadraticLayer_new_only_card_le_one (n h : Nat) {s : Finset Nat}
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1) :
    ((quadraticDivisorLayer (n+1) h s).filter (fun d =>
      Not (Membership.mem (quadraticDivisorLayer n h s) d))).card <= 1 := by
  apply Finset.card_le_one.mpr
  intro d hd e he
  have hdm := Finset.mem_filter.mp hd
  have hem := Finset.mem_filter.mp he
  have hds := Finset.mem_filter.mp hdm.1
  have hes := Finset.mem_filter.mp hem.1
  choose r hr using hds.2
  choose t ht using hes.2
  have hddata := hs d hds.1
  have hedata := hs e hes.1
  have hdf := quadraticLayer_new_paired_floor hddata.1 hddata.2 hdm.1
  have hef := quadraticLayer_new_paired_floor hedata.1 hedata.2 hem.1
  rw [if_neg hdm.2] at hdf
  rw [if_neg hem.2] at hef
  have hdpf := paired_floor_of_new_pair hddata.1 hddata.2 hr.1 hr.2.2.1 hr.2.2.2
  have hepf := paired_floor_of_new_pair hedata.1 hedata.2 ht.1 ht.2.2.1 ht.2.2.2
  have hdfail : d*(r-2) <= n*n := by split_ifs at hdpf <;> omega
  have hefail : e*(t-2) <= n*n := by split_ifs at hepf <;> omega
  exact (failed_new_transport_center_unique hddata.1 hedata.1 hddata.2 hedata.2
    (by omega) hr.2.2.1 ht.2.2.1 hr.2.2.2 ht.2.2.2 hdfail hefail).1

end Nat.PrimeSieve
