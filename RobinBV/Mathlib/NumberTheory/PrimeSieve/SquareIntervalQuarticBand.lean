/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalBandOwner

/-!
# Fourth-power band for exact owner cancellation

Fourth-power product bounds control both the number of rough factors in a
supported divisor and the order of its complementary factor. The scale is
stated by integer inequalities, without an asymptotic cutoff substitution.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- Three factors above the square-root cutoff cannot divide a modulus inside the fourth-power band. -/
theorem three_rough_factors_exceed_quartic_cutoff {n p q r d : Nat}
    (hp : n < p*p) (hq : n < q*q) (hr : n < r*r)
    (hprod : p*q*r <= d) (hcut : d^4 <= n^5) : False := by
  have hsq : (n+1)^3 <= (p*q*r)^2 := by
    calc
      _ = (n+1)*(n+1)*(n+1) := by ring
      _ <= (p*p)*(q*q)*(r*r) := Nat.mul_le_mul
        (Nat.mul_le_mul (show n+1 <= p*p by omega) (show n+1 <= q*q by omega))
        (show n+1 <= r*r by omega)
      _ = _ := by ring
  have hfour : (n+1)^6 <= d^4 := by
    calc
      _ = ((n+1)^3)^2 := by ring
      _ <= ((p*q*r)^2)^2 := Nat.pow_le_pow_left hsq 2
      _ = (p*q*r)^4 := by ring
      _ <= _ := Nat.pow_le_pow_left hprod 4
  have hstrict : n^5 < (n+1)^6 := lt_of_lt_of_le
    (Nat.pow_lt_pow_left (show n < n+1 by omega) (by decide : Not (5 = 0)))
    (Nat.pow_le_pow_right (show 0 < n+1 by omega) (by decide : 5 <= 6))
  omega

/-- A product in the fourth-power band below an interval integer forces the cofactor above the opposite factor. -/
theorem quartic_pair_cofactor_right {n p q r : Nat}
    (hpsq : n < p*p) (hcut : (p*q)^4 <= n^5) (hlo : n*n < p*q*r) : q < r := by
  by_contra h
  have hrq : r <= q := by omega
  have hlt : n*n < p*q*q := lt_of_lt_of_le hlo (Nat.mul_le_mul_left (p*q) hrq)
  have hsq := Nat.mul_self_lt_mul_self hlt
  have hmul := Nat.mul_lt_mul_of_pos_right hsq (show 0 < p*p by omega)
  have hbase := Nat.mul_le_mul_left ((n*n)*(n*n)) (show n <= p*p by omega)
  have he0 : ((n*n)*(n*n))*n = n^5 := by ring
  have he1 : ((p*q*q)*(p*q*q))*(p*p) = (p*q)^4 := by ring
  rw [he0] at hbase
  rw [he1] at hmul
  omega

/-- A rough finite product inside the fourth-power band with two distinct selected factors contains exactly that pair. -/
theorem roughProduct_eq_pair_of_quartic_cutoff {n p q : Nat} {s : Finset Nat}
    (hs : forall t, Membership.mem s t -> n < t*t)
    (hp : Membership.mem s p) (hq : Membership.mem s q) (hpq : Not (p = q))
    (hcut : (s.prod (fun t => t))^4 <= n^5) : s = {p,q} := by
  have hpos (t : Nat) (ht : Membership.mem s t) : 1 <= t := by
    by_contra h
    have hz : t = 0 := by omega
    have hsq := hs t ht
    rw [hz] at hsq
    omega
  ext r
  constructor
  next =>
    intro hr
    by_cases hrp : r = p
    next => simp [hrp]
    next =>
      by_cases hrq : r = q
      next => simp [hrq]
      next =>
        have hsub : forall t, Membership.mem ({p,q,r} : Finset Nat) t -> Membership.mem s t := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with ht | ht | ht <;> subst t <;> assumption
        have hprod := Finset.prod_le_prod_of_subset_of_one_le hsub
          (fun t _ => Nat.zero_le t) (fun t ht _ => hpos t ht)
        have hpr : Not (p = r) := Ne.symm hrp
        have hqr : Not (q = r) := Ne.symm hrq
        have hsmall : p*q*r <= s.prod (fun t => t) := by
          simpa [Finset.prod_insert, hpq, hpr, hqr, mul_assoc] using hprod
        exact False.elim (three_rough_factors_exceed_quartic_cutoff
          (hs p hp) (hs q hq) (hs r hr) hsmall hcut)
  next =>
    intro hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with hr | hr <;> subst r <;> assumption

/-- A rough supported divisor inside the fourth-power band is a product of two distinct actual medium primes. -/
theorem rough_supported_quartic_pair {n d : Nat}
    (hd : Membership.mem (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d)
    (hlo : n+1 < d) (hcut : d^4 <= n^5)
    (hrough : forall p, Nat.Prime p -> Dvd.dvd p d -> n < p*p) :
    exists p q : Nat, Membership.mem (squareMediumOddPrimes n) p /\
      Membership.mem (squareMediumOddPrimes n) q /\ Not (p = q) /\ d = p*q := by
  choose x hx using Finset.mem_image.mp hd
  have hu := Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).1
  have hv := Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).2
  have hs : forall p, Membership.mem (Union.union x.1 x.2) p -> Nat.Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    next => exact (Finset.mem_filter.mp (hu hp)).2.1
    next => exact (Finset.mem_filter.mp (hv hp)).2.1
  have hdiv : Dvd.dvd ((Union.union x.1 x.2).prod (fun p => p)) d :=
    Exists.intro 1 (by simpa only [Nat.mul_one] using hx.2.symm)
  have hue : x.1 = {} := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hpa := (Finset.mem_filter.mp (hu hp)).2
    have hpd := (prod_primes_dvd_iff hs d).mp hdiv p (Finset.mem_union_left x.2 hp)
    have hlarge := hrough p hpa.1 hpd
    omega
  have hdEq : x.2.prod (fun p => p) = d := by simpa only [hue, Finset.empty_union] using hx.2
  have hcard : 1 < x.2.card := by
    by_contra h
    have hcases : x.2.card = 0 \/ x.2.card = 1 := by omega
    rcases hcases with hz | ho
    next =>
      have he := Finset.card_eq_zero.mp hz
      rw [he, Finset.prod_empty] at hdEq
      omega
    next =>
      choose p hp using Finset.card_eq_one.mp ho
      have hpm : Membership.mem x.2 p := by rw [hp]; simp
      have hple := Finset.mem_range.mp (Finset.mem_filter.mp (hv hpm)).1
      rw [hp, Finset.prod_singleton] at hdEq
      omega
  choose p hp q hq hpq using Finset.one_lt_card.mp hcard
  have hvdata (t : Nat) (ht : Membership.mem x.2 t) :
      Nat.Prime t /\ t % 2 = 1 /\ n < t*t := (Finset.mem_filter.mp (hv ht)).2
  have hset := roughProduct_eq_pair_of_quartic_cutoff
    (fun t ht => (hvdata t ht).2.2) hp hq hpq
    (show (x.2.prod (fun t => t))^4 <= n^5 by rw [hdEq]; exact hcut)
  have he : d = p*q := by rw [<- hdEq, hset]; simp [hpq]
  exact Exists.intro p (Exists.intro q (And.intro (hv hp) (And.intro (hv hq) (And.intro hpq he))))

/-- A rough integer in the two-window range with a supported fourth-power-band divisor has three distinct medium prime factors. -/
theorem rough_quartic_divisible_three_distinct {n m d : Nat}
    (hmlo : n*n < m) (hmhi : m <= (n+1)*(n+1)+2*(n+1))
    (hd : Membership.mem (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d)
    (hdlo : n+1 < d) (hdcut : d^4 <= n^5) (hdm : Dvd.dvd d m)
    (hrough : forall t, Nat.Prime t -> Dvd.dvd t m -> n < t*t) :
    exists p q r : Nat, Membership.mem (squareMediumOddPrimes n) p /\
      Membership.mem (squareMediumOddPrimes n) q /\ Membership.mem (squareMediumOddPrimes n) r /\
      Not (p = q) /\ Not (p = r) /\ Not (q = r) /\ m = p*q*r := by
  choose p q hp hq hpq hdEq using rough_supported_quartic_pair hd hdlo hdcut
    (fun t ht htd => hrough t ht (dvd_trans htd hdm))
  choose r hr using hdm
  have hmEq : m = p*q*r := by rw [hr, hdEq]
  have hpdata := (Finset.mem_filter.mp hp).2
  have hqdata := (Finset.mem_filter.mp hq).2
  have hcutPQ : (p*q)^4 <= n^5 := by rw [<- hdEq]; exact hdcut
  have hmloPQ : n*n < p*q*r := by rw [<- hmEq]; exact hmlo
  have hrq := quartic_pair_cofactor_right hpdata.2.2 hcutPQ hmloPQ
  have hrp : p < r := quartic_pair_cofactor_right hqdata.2.2
    (by simpa only [Nat.mul_comm q p] using hcutPQ)
    (by simpa only [Nat.mul_comm q p] using hmloPQ)
  have hp3 : 3 <= p := by have htwo := hpdata.1.two_le; have ho := hpdata.2.1; omega
  have hq3 : 3 <= q := by have htwo := hqdata.1.two_le; have ho := hqdata.2.1; omega
  have hdgt := distinct_large_odd_pair_gt_base_add_three hp3 hq3
    hpdata.2.1 hqdata.2.1 hpq hpdata.2.2 hqdata.2.2
  have hrn : r <= n := by
    by_contra h
    have hmul := Nat.mul_le_mul_left (p*q) (show n+1 <= r by omega)
    have hmul2 := Nat.mul_lt_mul_of_pos_right hdgt (show 0 < n+1 by omega)
    rw [hmEq] at hmhi
    nlinarith
  have hb : p < r /\ q < r /\ r <= n := And.intro hrp (And.intro hrq hrn)
  have hrd : Dvd.dvd r m := by rw [hmEq]; exact dvd_mul_left r (p*q)
  have hrprime := rough_le_index_prime (show 2 <= r by have htwo := hpdata.1.two_le; omega)
    hb.2.2 (fun t ht htr => hrough t ht (dvd_trans htr hrd))
  have hrsq := hrough r hrprime hrd
  have hrodd : r % 2 = 1 := by
    rcases hrprime.eq_two_or_odd with he | he
    next => have hpr := hb.1; have htwo := hpdata.1.two_le; rw [he] at hpr; omega
    next => exact he
  have hrmem : Membership.mem (squareMediumOddPrimes n) r :=
    Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
      (And.intro hrprime (And.intro hrodd hrsq)))
  exact Exists.intro p (Exists.intro q (Exists.intro r (And.intro hp
    (And.intro hq (And.intro hrmem (And.intro hpq (And.intro (by omega)
      (And.intro (by omega) hmEq))))))))

/-- The full joint incidence weight is zero on every rough integer having a supported fourth-power-band divisor. -/
theorem quartic_divisible_rough_joint_weight_zero {n m d : Nat}
    (hmlo : n*n < m) (hmhi : m <= (n+1)*(n+1)+2*(n+1))
    (hd : Membership.mem (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d)
    (hdlo : n+1 < d) (hdcut : d^4 <= n^5) (hdm : Dvd.dvd d m)
    (hrough : forall t, Nat.Prime t -> Dvd.dvd t m -> n < t*t) :
    jointIncidenceWeight (((squareMediumOddPrimes n).filter (fun p => Dvd.dvd p m)).card) = 0 := by
  choose p q r hp hq hr hpq hpr hqr hmEq using
    rough_quartic_divisible_three_distinct hmlo hmhi hd hdlo hdcut hdm hrough
  have hpprime := (Finset.mem_filter.mp hp).2.1
  have hqprime := (Finset.mem_filter.mp hq).2.1
  have hrprime := (Finset.mem_filter.mp hr).2.1
  have heq : (squareMediumOddPrimes n).filter (fun t => Dvd.dvd t m) = {p,q,r} := by
    ext t
    constructor
    next =>
      intro ht
      have hdata := Finset.mem_filter.mp ht
      have htprime := (Finset.mem_filter.mp hdata.1).2.1
      have htd := hdata.2
      rw [hmEq, htprime.dvd_mul, htprime.dvd_mul] at htd
      have hcases : t = p \/ t = q \/ t = r := by
        rcases htd with ht | ht
        next =>
          rcases ht with htp | htq
          next => exact Or.inl ((Nat.dvd_prime hpprime).mp htp |>.resolve_left htprime.ne_one)
          next => exact Or.inr (Or.inl ((Nat.dvd_prime hqprime).mp htq |>.resolve_left htprime.ne_one))
        next => exact Or.inr (Or.inr ((Nat.dvd_prime hrprime).mp ht |>.resolve_left htprime.ne_one))
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hcases
    next =>
      intro ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with ht | ht | ht <;> subst t
      next => exact Finset.mem_filter.mpr (And.intro hp (by rw [hmEq]; exact Exists.intro (q*r) (by ring)))
      next => exact Finset.mem_filter.mpr (And.intro hq (by rw [hmEq]; exact Exists.intro (p*r) (by ring)))
      next => exact Finset.mem_filter.mpr (And.intro hr (by rw [hmEq]; exact dvd_mul_left r (p*q)))
  rw [heq]
  norm_num [jointIncidenceWeight, hpq, hpr, hqr]

/-- An integer has an actual supported divisor strictly above the index inside the fourth-power band. -/
def squareQuarticBandDivisible (n m : Nat) : Prop :=
  exists d : Nat, Membership.mem
    (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d /\
      n+1 < d /\ d^4 <= n^5 /\ Dvd.dvd d m

/-- The complete jointly weighted rough sum is unchanged after removing full integer cells detected by the fourth-power band. -/
theorem sum_jointIncidenceWeight_erase_quartic_band {n : Nat} (s : Finset Nat)
    (hs : forall m, Membership.mem s m ->
      m % 2 = 1 /\ n*n < m /\ m <= (n+1)*(n+1)+2*(n+1)) :
    let t := s.filter (fun m => forall p, Membership.mem (squareSmallOddPrimes n) p -> Not (Dvd.dvd p m))
    t.sum (fun m => jointIncidenceWeight (((squareMediumOddPrimes n).filter (fun p => Dvd.dvd p m)).card)) =
      (t.filter (fun m => Not (squareQuarticBandDivisible n m))).sum
        (fun m => jointIncidenceWeight (((squareMediumOddPrimes n).filter (fun p => Dvd.dvd p m)).card)) := by
  let t := s.filter (fun m => forall p, Membership.mem (squareSmallOddPrimes n) p -> Not (Dvd.dvd p m))
  let w := fun m => jointIncidenceWeight (((squareMediumOddPrimes n).filter (fun p => Dvd.dvd p m)).card)
  change t.sum w = (t.filter (fun m => Not (squareQuarticBandDivisible n m))).sum w
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hb : squareQuarticBandDivisible n m
  next =>
    simp only [hb, not_true_eq_false, if_false]
    have hmt := Finset.mem_filter.mp hm
    have hmd := hs m hmt.1
    have hrough := squareSmallSieve_rough_of_odd hmd.1 hmt.2
    choose d hd hdlo hdcut hdm using hb
    exact quartic_divisible_rough_joint_weight_zero hmd.2.1 hmd.2.2 hd hdlo hdcut hdm hrough
  next => simp only [hb, not_false_eq_true, if_true]; rfl

/-- Either original frozen-clock square-window packet admits exact fourth-power-band null-cell removal. -/
theorem squareJointPacket_erase_quartic_band {n x : Nat} (hx : x = n \/ x = n+1) :
    squareJointPacket x (squareSmallOddPrimes n) (squareMediumOddPrimes n) =
      (((oddMultiplesInSquare x 1).filter (fun m =>
        forall p, Membership.mem (squareSmallOddPrimes n) p -> Not (Dvd.dvd p m))).filter
          (fun m => Not (squareQuarticBandDivisible n m))).sum
            (fun m => jointIncidenceWeight
              (((squareMediumOddPrimes n).filter (fun p => Dvd.dvd p m)).card)) := by
  have hs : forall m, Membership.mem (oddMultiplesInSquare x 1) m ->
      m % 2 = 1 /\ n*n < m /\ m <= (n+1)*(n+1)+2*(n+1) := by
    intro m hm
    have h0 := Finset.mem_filter.mp hm
    have h1 := Finset.mem_filter.mp h0.1
    have hupper := Finset.mem_range.mp h1.1
    have hodd := h1.2.1
    rcases hx with he | he <;> subst x
    all_goals exact And.intro hodd (And.intro (by nlinarith [h0.2]) (by nlinarith))
  exact sum_jointIncidenceWeight_erase_quartic_band (oddMultiplesInSquare x 1) hs

/-- A repeated-factor triple above the lower square has its pair product strictly outside the fourth-power band. -/
theorem repeatedPair_quartic_lower {n p q : Nat}
    (hq : n < q*q) (hlo : n*n < p*p*q) : n^5 < (p*q)^4 := by
  by_contra h
  have hcut : (q*p)^4 <= n^5 := by
    rw [Nat.mul_comm q p]
    omega
  have hlow : n*n < q*p*p := by nlinarith
  have hbad := quartic_pair_cofactor_right hq hcut hlow
  omega

/-- Every actual rough repeated-prime cell lies beyond the exact fourth-power pair cutoff. -/
theorem repeatedPrimeCell_pair_quartic_lower {n p q : Nat}
    (h : RepeatedPrimeCell n (Nat.sqrt n+1) p q) : n^5 < (p*q)^4 := by
  have hq : n < q*q := by
    by_contra hbad
    have hroot : q <= Nat.sqrt n := Nat.le_sqrt.mpr (show q*q <= n by omega)
    have hlower := h.lower_right
    omega
  exact repeatedPair_quartic_lower hq h.interval_lower

end Nat.PrimeSieve
