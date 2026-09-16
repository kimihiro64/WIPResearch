/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalEndpointWeights

/-!
# Signed unit-class quadratic fringes

Exact actual-row bijections retain both modulus-six unit classes. The signed
fringe kernel equals a difference of odd-multiple counts at the two next
unit points; above the cube cutoff these counts differ by at most two.
Both edge strips lie outside this interior bound. No bound for a weighted
prime correlation follows from pointwise kernel boundedness alone.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- Every admissible odd multiple of three times a unit factor belongs to an actual quadratic row. -/
theorem oddMultiple_has_squareThirdRow {n p m : Nat}
    (hpodd : p%2 = 1) (hpunit : Not (p%3 = 0))
    (hpY : Nat.nthRoot 3 (n*n+2*n) < p) (hpn : p <= n)
    (hm : Membership.mem (oddMultiplesInSquare n (3*p)) m) :
    exists h : Nat, Membership.mem (squareThirdFixedFactorRows n p) h /\
      m = p*(p+2*(n+h-p)) := by
  have hd := hm
  simp only [oddMultiplesInSquare, oddMultiplesUpTo, Finset.mem_filter, Finset.mem_range] at hd
  have hp0 : 0 < p := by omega
  choose s hs using hd.1.2.2
  let q := 3*s
  have hmprod : m = p*q := by dsimp [q]; nlinarith only [hs]
  have hqodd : q%2 = 1 := by
    have hm2 := hd.1.2.1
    rw [hmprod, Nat.mul_mod, hpodd] at hm2
    omega
  have hqn : n < q := by
    by_contra hnot
    have hmul := Nat.mul_le_mul hpn (show q <= n by omega)
    nlinarith only [hmprod, hmul, hd.2]
  let t := (q-p)/2
  have heq : q = p+2*t := by dsimp [t]; omega
  have hcell : OddFactorGapCell n p t := {
    odd_left := hpodd
    gap_pos := by dsimp [t]; omega
    interval_lower := by rw [<- heq, <- hmprod]; exact hd.2
    interval_upper := by rw [<- heq, <- hmprod]; nlinarith only [hd.1.1]
  }
  let h := p+t-n
  have hc := hcell.center_gt
  have hrecover : n+h-p = t := by dsimp [h]; omega
  have hhpos : 1 <= h := by dsimp [h]; omega
  have hqm : q <= m := by nlinarith only [hmprod, hp0]
  have hhupper : h <= n*n+2*n := by dsimp [h] at *; omega
  have hpRow : Membership.mem (squareThirdCofactorRow n h) p := by
    apply (mem_squareThirdCofactorRow n h p).mpr
    rw [hrecover]
    exact And.intro (And.intro (by omega) hpn)
      (And.intro hpY (And.intro hpunit (And.intro hcell
        (by rw [<- heq]; simp [q]))))
  have hhCenter : Membership.mem (squareThirdCenters n) h :=
    Finset.mem_filter.mpr (And.intro (Finset.mem_Icc.mpr (And.intro hhpos hhupper))
      (Exists.intro p hpRow))
  refine Exists.intro h (And.intro (Finset.mem_filter.mpr (And.intro hhCenter hpRow)) ?_)
  rw [hrecover, <- heq]
  exact hmprod

/-- The fixed-factor row count equals the exact odd-multiple count, with no density substitution. -/
theorem card_squareThirdFixedFactorRows_eq {n p : Nat}
    (hpodd : p%2 = 1) (hpunit : Not (p%3 = 0))
    (hpY : Nat.nthRoot 3 (n*n+2*n) < p) (hpn : p <= n) :
    (squareThirdFixedFactorRows n p).card = (oddMultiplesInSquare n (3*p)).card := by
  apply Nat.le_antisymm (card_squareThirdFixedFactorRows_le hpodd)
  let g : Nat -> Nat := fun h => p*(p+2*(n+h-p))
  have hsub : oddMultiplesInSquare n (3*p) <= (squareThirdFixedFactorRows n p).image g := by
    intro m hm
    choose h hh using oddMultiple_has_squareThirdRow hpodd hpunit hpY hpn hm
    exact Finset.mem_image.mpr (Exists.intro h (And.intro hh.1 hh.2.symm))
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-- Actual rounded-fringe rows having the specified unit class. -/
noncomputable def squareThirdClassFringeRows (n r a : Nat) : Finset Nat :=
  (squareThirdFringeRows n r).filter (fun h => squareThirdFirst n h%6 = a)

/-- A class-fringe set equals the fixed-factor rows at its unique next class point. -/
theorem squareThirdClassFringeRows_eq_fixed {n r a p : Nat} (hn : 100 <= n)
    (hpclass : p%6 = a) (hrp : r <= p) (hpr : p < r+6) :
    squareThirdClassFringeRows n r a = squareThirdFixedFactorRows n p := by
  apply Finset.ext
  intro h
  constructor
  next =>
    intro hh
    have hd := Finset.mem_filter.mp hh
    have hf := Finset.mem_filter.mp hd.1
    have H := (Finset.mem_filter.mp hf.1).2
    choose u hu using squareThirdRoundedFringe_point hn H hf.2.1 hf.2.2
    have huclass := squareThirdCofactorRow_mod_six hu.1 (squareThirdFirst_mem H)
    have hueq : u = p := by omega
    rw [hueq] at hu
    exact Finset.mem_filter.mpr (And.intro hf.1 hu.1)
  next =>
    intro hh
    have hd := Finset.mem_filter.mp hh
    have H := (Finset.mem_filter.mp hd.1).2
    have hL : squareThirdFirst n h <= p := by
      rw [squareThirdFirst, dif_pos H]
      exact Finset.min'_le _ _ hd.2
    have hR : p <= squareThirdLast n h := by
      rw [squareThirdLast, dif_pos H]
      exact Finset.le_max' _ _ hd.2
    have hL7 := squareThirdCofactorRow_ge_seven hn (squareThirdFirst_mem H)
    have hclass := squareThirdCofactorRow_mod_six (squareThirdFirst_mem H) hd.2
    apply Finset.mem_filter.mpr
    refine And.intro ?_ (hclass.trans hpclass)
    exact Finset.mem_filter.mpr (And.intro hd.1 (And.intro (by omega) (by omega)))

/-- Exact lower interval capacity for odd multiples of an odd divisor. -/
theorem div_le_card_oddMultiplesInSquare {d : Nat} (n : Nat) (hd : d%2 = 1) :
    n/d <= (oddMultiplesInSquare n d).card := by
  have hd0 : 0 < d := by omega
  have hdiv := Nat.div_mul_le_self n d
  have hlo : n*n+d*(2*(n/d)) <= n*n+2*n := by nlinarith only [hdiv]
  have hfirst : (n*n+d*(2*(n/d)))/d <= (n*n+2*n)/d := Nat.div_le_div_right hlo
  have hhalf : ((n*n+d*(2*(n/d)))/d+1)/2 <= ((n*n+2*n)/d+1)/2 :=
    Nat.div_le_div_right (Nat.add_le_add_right hfirst 1)
  rw [odd_multiple_floor_shift _ _ hd0] at hhalf
  have hcount := card_oddMultiplesInSquare n hd
  omega

/-- Above the cube cutoff the squared factor exceeds twice the square-interval index. -/
theorem square_cube_cutoff_sq_gt_twice {n p : Nat} (hn : 100 <= n)
    (hpY : Nat.nthRoot 3 (n*n+2*n) < p) : 2*n < p*p := by
  have hpow := (Nat.nthRoot_lt_iff (by decide : Not (3 = 0))).mp hpY
  have hp7 : 7 <= p := by
    by_contra hnot
    have hp6 : p <= 6 := by omega
    have hsq := Nat.mul_le_mul hp6 hp6
    have hcube := Nat.mul_le_mul hsq hp6
    nlinarith only [hn, hpow, hcube]
  by_contra hnot
  have hsmall : p*p <= 2*n := by omega
  have hfour := Nat.mul_le_mul hsmall hsmall
  have hbase : n*n < p^3 := by nlinarith only [hpow]
  have hmult := Nat.mul_lt_mul_of_pos_left hbase (show 0 < p by omega)
  have hseven := Nat.mul_le_mul_right (n*n) hp7
  nlinarith only [hfour, hmult, hseven, Nat.zero_le (n*n)]

/-- Adjacent denominators have integer quotient counts differing by at most one in this regime. -/
theorem div_three_le_div_three_add_one {n p q : Nat}
    (hp : 0 < p) (hq : 0 < q) (hsize : 4*n <= 3*p*p) (hnear : q <= p+4) :
    n/(3*p) <= n/(3*q)+1 := by
  let a := n/(3*p)
  have ha := Nat.div_mul_le_self n (3*p)
  change a*(3*p) <= n at ha
  have hcap : 4*a <= p := by
    by_contra hnot
    have ht := Nat.mul_le_mul_left (3*p) (show p+1 <= 4*a by omega)
    nlinarith only [ht, ha, hsize, hp]
  by_cases ha0 : a = 0
  next =>
    change a <= n/(3*q)+1
    rw [ha0]
    exact Nat.zero_le _
  next =>
    have hae : a-1+1 = a := by omega
    have ht := Nat.mul_le_mul_left (3*(a-1)) hnear
    have hprod : (a-1)*(3*q) <= n := by
      nlinarith only [ht, hae, ha, hcap]
    have hdiv : a-1 <= n/(3*q) :=
      (Nat.le_div_iff_mul_le (show 0 < 3*q by omega)).mpr hprod
    change a <= _
    omega

/-- Exact odd-multiple counts at the two nearby unit factors differ by at most two. -/
theorem abs_card_oddMultiples_three_sub_le_two {n p q : Nat}
    (hn : 100 <= n) (hpodd : p%2 = 1) (hqodd : q%2 = 1)
    (hpY : Nat.nthRoot 3 (n*n+2*n) < p)
    (hqY : Nat.nthRoot 3 (n*n+2*n) < q)
    (hpq : p <= q+4) (hqp : q <= p+4) :
    abs (((oddMultiplesInSquare n (3*p)).card : Int) -
      ((oddMultiplesInSquare n (3*q)).card : Int)) <= 2 := by
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  have hp3 : (3*p)%2 = 1 := by omega
  have hq3 : (3*q)%2 = 1 := by omega
  have hpSq := square_cube_cutoff_sq_gt_twice hn hpY
  have hqSq := square_cube_cutoff_sq_gt_twice hn hqY
  have hpLower := div_le_card_oddMultiplesInSquare n hp3
  have hqLower := div_le_card_oddMultiplesInSquare n hq3
  have hpUpper := card_oddMultiplesInSquare_le_div_add_one n hp3
  have hqUpper := card_oddMultiplesInSquare_le_div_add_one n hq3
  have hdivpq := div_three_le_div_three_add_one (n := n) hp0 hq0 (by nlinarith only [hpSq]) hqp
  have hdivqp := div_three_le_div_three_add_one (n := n) hq0 hp0 (by nlinarith only [hqSq]) hpq
  apply abs_le.mpr
  constructor <;> omega


/-- The next representative of a residue class in the six-integer block starting at r. -/
def nextModSixPoint (r a : Nat) : Nat := r+(a+6-r%6)%6

/-- The next class representative lies in its exact block and has the required residue. -/
theorem nextModSixPoint_spec (r : Nat) {a : Nat} (ha : a < 6) :
    r <= nextModSixPoint r a /\ nextModSixPoint r a < r+6 /\ nextModSixPoint r a%6 = a := by
  unfold nextModSixPoint
  omega

/-- The complete signed difference of the two actual reduced-class fringe counts. -/
noncomputable def squareThirdSignedFringeKernel (n r : Nat) : Int :=
  ((squareThirdClassFringeRows n r 1).card : Int) -
    ((squareThirdClassFringeRows n r 5).card : Int)

/-- The actual interior kernel is the difference of the two exact next-factor odd-multiple counts. -/
theorem squareThirdSignedFringeKernel_eq_counts {n r : Nat}
    (hn : 100 <= n) (hrY : Nat.nthRoot 3 (n*n+2*n) < r) (hrn : r+5 <= n) :
    squareThirdSignedFringeKernel n r =
      ((oddMultiplesInSquare n (3*nextModSixPoint r 1)).card : Int) -
        ((oddMultiplesInSquare n (3*nextModSixPoint r 5)).card : Int) := by
  have h1 := nextModSixPoint_spec r (by decide : 1 < 6)
  have h5 := nextModSixPoint_spec r (by decide : 5 < 6)
  rw [squareThirdSignedFringeKernel,
    squareThirdClassFringeRows_eq_fixed hn h1.2.2 h1.1 h1.2.1,
    squareThirdClassFringeRows_eq_fixed hn h5.2.2 h5.1 h5.2.1]
  have hp1 : (nextModSixPoint r 1)%2 = 1 := by omega
  have hp5 : (nextModSixPoint r 5)%2 = 1 := by omega
  have hu1 : Not ((nextModSixPoint r 1)%3 = 0) := by omega
  have hu5 : Not ((nextModSixPoint r 5)%3 = 0) := by omega
  rw [card_squareThirdFixedFactorRows_eq hp1 hu1 (by omega) (by omega),
    card_squareThirdFixedFactorRows_eq hp5 hu5 (by omega) (by omega)]

/-- The full actual signed fringe kernel is bounded by two away from both edge strips. -/
theorem abs_squareThirdSignedFringeKernel_le_two {n r : Nat}
    (hn : 100 <= n) (hrY : Nat.nthRoot 3 (n*n+2*n) < r) (hrn : r+5 <= n) :
    abs (squareThirdSignedFringeKernel n r) <= 2 := by
  rw [squareThirdSignedFringeKernel_eq_counts hn hrY hrn]
  have h1 := nextModSixPoint_spec r (by decide : 1 < 6)
  have h5 := nextModSixPoint_spec r (by decide : 5 < 6)
  apply abs_card_oddMultiples_three_sub_le_two hn
  all_goals omega


/-- Finite weighted interchange retains arbitrary signed coefficients on every actual row. -/
theorem sum_squareThirdWeightedPrefix_eq_fringe (n : Nat) (c F : Nat -> Real) :
    Finset.sum (squareThirdCenters n) (fun h => c h*
      (squarePrefix F (squareThirdLast n h)-squarePrefix F (squareThirdFirst n h-6))) =
      Finset.sum (Finset.range (n+1)) (fun r =>
        (Finset.sum (squareThirdFringeRows n r) c)*F r) := by
  calc
    _ = Finset.sum (squareThirdCenters n) (fun h =>
        Finset.sum (Finset.range (n+1)) (fun r => c h*
          (if squareThirdFirst n h-6 < r /\ r <= squareThirdLast n h then F r else 0))) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [squareThirdPrefix_sub_eq_fringe (Finset.mem_filter.mp hh).2, Finset.mul_sum]
    _ = Finset.sum (Finset.range (n+1)) (fun r =>
        Finset.sum (squareThirdCenters n) (fun h => c h*
          (if squareThirdFirst n h-6 < r /\ r <= squareThirdLast n h then F r else 0))) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_mul]
      simp only [squareThirdFringeRows, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro h hh
      by_cases H : squareThirdFirst n h-6 < r /\ r <= squareThirdLast n h
      all_goals simp [H]

/-- The real sign of the two reduced residue classes modulo six, zero elsewhere. -/
noncomputable def modSixSign (a : Nat) : Real :=
  (if a = 1 then 1 else 0)-(if a = 5 then 1 else 0)

/-- An arbitrary real weight multiplied by the exact reduced-class sign. -/
noncomputable def modSixSignedWeight (F : Nat -> Real) (r : Nat) : Real :=
  modSixSign (r%6)*F r

/-- The full sum of row class signs equals the signed fringe kernel. -/
theorem sum_modSixSign_fringe (n r : Nat) :
    Finset.sum (squareThirdFringeRows n r) (fun h => modSixSign (squareThirdFirst n h%6)) =
      (squareThirdSignedFringeKernel n r : Real) := by
  simp [modSixSign, Finset.sum_sub_distrib, squareThirdSignedFringeKernel, squareThirdClassFringeRows]

/-- The ordinary signed-unit prefix equals the difference of the two progression prefixes. -/
theorem squarePrefix_modSixSignedWeight (F : Nat -> Real) (X : Nat) :
    squarePrefix (modSixSignedWeight F) X =
      modSixWeightedPrefix F 1 X-modSixWeightedPrefix F 5 X := by
  unfold squarePrefix modSixSignedWeight modSixSign modSixWeightedPrefix
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_filter]

/-- The exact mean of the two reduced-class weighted prefixes. -/
noncomputable def modSixUnitAveragePrefix (F : Nat -> Real) (X : Nat) : Real :=
  (modSixWeightedPrefix F 1 X+modSixWeightedPrefix F 5 X)/2

/-- Subtracting the exact unit mean leaves half the signed class-prefix difference. -/
theorem modSixPrefix_sub_unitAverage (F : Nat -> Real) (X : Nat) {a : Nat}
    (ha : a = 1 \/ a = 5) :
    modSixWeightedPrefix F a X-modSixUnitAveragePrefix F X =
      modSixSign a/2*squarePrefix (modSixSignedWeight F) X := by
  rw [squarePrefix_modSixSignedWeight]
  rcases ha with h1 | h5
  all_goals subst a; norm_num [modSixUnitAveragePrefix, modSixSign] <;> ring

/-- Actual weighted row mass centered by the full two-class prefix mean. -/
noncomputable def squareThirdUnitCenteredMass (n : Nat) (F : Nat -> Real) : Real :=
  Finset.sum (squareThirdCenters n) (fun h =>
    Finset.sum (squareThirdCofactorRow n h) F -
      (modSixUnitAveragePrefix F (squareThirdLast n h) -
        modSixUnitAveragePrefix F (squareThirdFirst n h-6)))

/-- The full centered mass equals its exact signed-kernel correlation on all indices zero through n. -/
theorem squareThirdUnitCenteredMass_eq_kernel {n : Nat} (hn : 100 <= n) (F : Nat -> Real) :
    squareThirdUnitCenteredMass n F =
      (1/2:Real)*Finset.sum (Finset.range (n+1)) (fun r =>
        (squareThirdSignedFringeKernel n r : Real)*modSixSignedWeight F r) := by
  let G := modSixSignedWeight F
  have hrow (h : Nat) (hh : Membership.mem (squareThirdCenters n) h) :
      Finset.sum (squareThirdCofactorRow n h) F -
        (modSixUnitAveragePrefix F (squareThirdLast n h) -
          modSixUnitAveragePrefix F (squareThirdFirst n h-6)) =
        (1/2:Real)*(modSixSign (squareThirdFirst n h%6)*
          (squarePrefix G (squareThirdLast n h)-squarePrefix G (squareThirdFirst n h-6))) := by
    have H := (Finset.mem_filter.mp hh).2
    have hd := (mem_squareThirdCofactorRow n h _).mp (squareThirdFirst_mem H)
    have hpodd := hd.2.2.2.1.odd_left
    have ha : squareThirdFirst n h%6 = 1 \/ squareThirdFirst n h%6 = 5 := by omega
    have hclass := squareThirdCofactorRow_mod_six (squareThirdLast_mem H) (squareThirdFirst_mem H)
    have heq := sum_squareThirdRow_eq_prefix_difference hn H F
    rw [hclass] at heq
    have hR := modSixPrefix_sub_unitAverage F (squareThirdLast n h) ha
    have hL := modSixPrefix_sub_unitAverage F (squareThirdFirst n h-6) ha
    dsimp [G]
    rw [heq]
    nlinarith only [hR, hL]
  calc
    _ = (1/2:Real)*Finset.sum (squareThirdCenters n) (fun h =>
        modSixSign (squareThirdFirst n h%6)*
          (squarePrefix G (squareThirdLast n h)-squarePrefix G (squareThirdFirst n h-6))) := by
      unfold squareThirdUnitCenteredMass
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hrow
    _ = (1/2:Real)*Finset.sum (Finset.range (n+1)) (fun r =>
        (Finset.sum (squareThirdFringeRows n r) (fun h => modSixSign (squareThirdFirst n h%6)))*G r) := by
      rw [sum_squareThirdWeightedPrefix_eq_fringe]
    _ = _ := by simp only [sum_modSixSign_fringe]; rfl

/-- A large odd divisor has at most one odd multiple across the two adjacent open square intervals. -/
theorem card_oddMultiples_successor_le_one {n d : Nat}
    (hd : d%2 = 1) (hcut : 2*n+2 <= d) :
    (oddMultiplesInSquare n d).card+(oddMultiplesInSquare (n+1) d).card <= 1 := by
  have hd0 : 0 < d := by omega
  have hOld := card_oddMultiplesInSquare n hd
  have hNew := card_oddMultiplesInSquare (n+1) hd
  have hgap : n*n+2*n <= (n+1)*(n+1) := by nlinarith
  have hgapDiv : (n*n+2*n)/d <= ((n+1)*(n+1))/d := Nat.div_le_div_right hgap
  have hgapHalf : ((n*n+2*n)/d+1)/2 <= (((n+1)*(n+1))/d+1)/2 :=
    Nat.div_le_div_right (Nat.add_le_add_right hgapDiv 1)
  have hupper : (n+1)*(n+1)+2*(n+1) <= n*n+d*(2*1) := by nlinarith only [hcut]
  have hupperDiv : ((n+1)*(n+1)+2*(n+1))/d <= (n*n+d*(2*1))/d :=
    Nat.div_le_div_right hupper
  have hupperHalf : (((n+1)*(n+1)+2*(n+1))/d+1)/2 <= ((n*n+d*(2*1))/d+1)/2 :=
    Nat.div_le_div_right (Nat.add_le_add_right hupperDiv 1)
  rw [odd_multiple_floor_shift _ _ hd0] at hupperHalf
  omega

/-- Shared two-interval capacity bounds the actual high successor kernel by three, not the independent six. -/
theorem abs_squareThirdSignedFringeKernel_successor_le_three {n r : Nat}
    (hn : 100 <= n)
    (hrOld : Nat.nthRoot 3 (n*n+2*n) < r)
    (hrNew : Nat.nthRoot 3 ((n+1)*(n+1)+2*(n+1)) < r)
    (hrUpper : r+5 <= n) (hrHigh : 2*n+2 <= 3*r) :
    abs (2*squareThirdSignedFringeKernel (n+1) r-squareThirdSignedFringeKernel n r) <= 3 := by
  rw [squareThirdSignedFringeKernel_eq_counts hn hrOld hrUpper,
    squareThirdSignedFringeKernel_eq_counts (n := n+1) (by omega) hrNew (by omega)]
  have h1 := nextModSixPoint_spec r (by decide : 1 < 6)
  have h5 := nextModSixPoint_spec r (by decide : 5 < 6)
  have hsum1 := card_oddMultiples_successor_le_one (n := n) (d := 3*nextModSixPoint r 1)
    (by omega) (by omega)
  have hsum5 := card_oddMultiples_successor_le_one (n := n) (d := 3*nextModSixPoint r 5)
    (by omega) (by omega)
  apply abs_le.mpr
  constructor <;> omega

end Nat.PrimeSieve
