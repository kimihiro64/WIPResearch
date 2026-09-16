/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalBandArithmetic
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalRepeatedHyperbola

/-!
# Quadratic band factors and exact owner cancellation

The band restrictions are applied to actual integers in both square windows.
After the small-owner exclusions, the complementary factor is forced to be
a distinct prime. No independent sign is assigned to a selected modulus sum.
The balanced-pair subtraction has an explicit odd-slot allowance, connected
to the complete arithmetic-band comparison with its complement retained.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- A nontrivial integer at most the index that avoids every small prime divisor is prime. -/
theorem rough_le_index_prime {n r : Nat} (hr : 2 <= r) (hrn : r <= n)
    (hrough : forall p, Nat.Prime p -> Dvd.dvd p r -> n < p*p) : Nat.Prime r := by
  by_contra hc
  choose a ha using exists_minFac_mul hr hc
  have hp : Nat.Prime r.minFac := Nat.minFac_prime (by omega)
  have hpsq := hrough r.minFac hp (Nat.minFac_dvd r)
  have had : Dvd.dvd a r := by rw [ha.2]; exact dvd_mul_left a r.minFac
  have hpa := Nat.minFac_le_of_dvd ha.1 had
  have hmul := Nat.mul_le_mul_left r.minFac hpa
  nlinarith [ha.2]

/-- Two distinct odd factors above the square-root cutoff have product strictly beyond the base plus three. -/
theorem distinct_large_odd_pair_gt_base_add_three {n p q : Nat}
    (hp : 3 <= p) (hq : 3 <= q) (hpo : p % 2 = 1) (hqo : q % 2 = 1)
    (hpq : Not (p = q)) (hpsq : n < p*p) (hqsq : n < q*q) : n+3 < p*q := by
  by_cases horder : p < q
  next =>
    have hgap : p+2 <= q := by omega
    have hmul := Nat.mul_le_mul_left p hgap
    nlinarith
  next =>
    have hgap : q+2 <= p := by omega
    have hmul := Nat.mul_le_mul_left q hgap
    nlinarith

/-- Across both adjacent square windows a doubled-band pair has a cofactor at most the base and larger than both factors. -/
theorem bandPair_cofactor_bounds {n p q r : Nat}
    (hn : 17 <= n)
    (hpo : p % 2 = 1) (hqo : q % 2 = 1) (hpq : Not (p = q))
    (hpsq : n < p*p) (hqsq : n < q*q) (hband : p*q <= 2*n+1)
    (hlo : n*n < p*q*r) (hhi : p*q*r <= (n+1)*(n+1)+2*(n+1)) :
    p < r /\ q < r /\ r <= n := by
  have hp5 : 5 <= p := by
    by_contra h
    have hs := Nat.mul_le_mul (show p <= 4 by omega) (show p <= 4 by omega)
    omega
  have hq5 : 5 <= q := by
    by_contra h
    have hs := Nat.mul_le_mul (show q <= 4 by omega) (show q <= 4 by omega)
    omega
  have hdgt := distinct_large_odd_pair_gt_base_add_three (by omega : 3 <= p)
    (by omega : 3 <= q) hpo hqo hpq hpsq hqsq
  have hrn1 := cofactor_le_index (show n+1 < p*q by omega)
    (show p*q*r < ((n+1)+1)*((n+1)+1) by nlinarith)
  have hrn : r <= n := by
    by_contra h
    have he : r = n+1 := by omega
    rw [he] at hhi
    have hmul := Nat.mul_le_mul_right (n+1) (show n+4 <= p*q by omega)
    nlinarith
  have hqmul := Nat.mul_le_mul_right q hp5
  have hpmul := Nat.mul_le_mul_left p hq5
  have hp2 : 2*p+2 <= n := by omega
  have hq2 : 2*q+2 <= n := by omega
  have hrgt (t : Nat) (ht : 2*t+2 <= n) : t < r := by
    by_contra h
    have hrle : r <= t := by omega
    have hmul := Nat.mul_le_mul_right r hband
    have hmul2 := Nat.mul_le_mul_left n (show 2*r+2 <= n by omega)
    nlinarith
  exact And.intro (hrgt p hp2) (And.intro (hrgt q hq2) hrn)

/-- A supported band divisor of a rough integer consists of two distinct actual medium primes. -/
theorem rough_supported_band_pair {n d : Nat}
    (hd : Membership.mem (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d)
    (hlo : n+1 < d) (hhi : d <= 2*n+1)
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
  have hset := oddPrimeProduct_eq_pair_of_band
    (fun t ht => And.intro (hvdata t ht).1 (hvdata t ht).2.1) hp hq hpq
    (hvdata p hp).2.2 (hvdata q hq).2.2 (show x.2.prod (fun t => t) <= 2*n+1 by rw [hdEq]; exact hhi)
  have he : d = p*q := by rw [<- hdEq, hset]; simp [hpq]
  exact Exists.intro p (Exists.intro q (And.intro (hv hp) (And.intro (hv hq) (And.intro hpq he))))

/-- A rough integer in the two-window range with a supported band divisor has three distinct medium prime factors. -/
theorem rough_band_divisible_three_distinct {n m d : Nat}
    (hn : 17 <= n) (hmlo : n*n < m) (hmhi : m <= (n+1)*(n+1)+2*(n+1))
    (hd : Membership.mem (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d)
    (hdlo : n+1 < d) (hdhi : d <= 2*n+1) (hdm : Dvd.dvd d m)
    (hrough : forall t, Nat.Prime t -> Dvd.dvd t m -> n < t*t) :
    exists p q r : Nat, Membership.mem (squareMediumOddPrimes n) p /\
      Membership.mem (squareMediumOddPrimes n) q /\ Membership.mem (squareMediumOddPrimes n) r /\
      Not (p = q) /\ Not (p = r) /\ Not (q = r) /\ m = p*q*r := by
  choose p q hp hq hpq hdEq using rough_supported_band_pair hd hdlo hdhi
    (fun t ht htd => hrough t ht (dvd_trans htd hdm))
  choose r hr using hdm
  have hmEq : m = p*q*r := by rw [hr, hdEq]
  have hpdata := (Finset.mem_filter.mp hp).2
  have hqdata := (Finset.mem_filter.mp hq).2
  have hb := bandPair_cofactor_bounds hn hpdata.2.1 hqdata.2.1 hpq hpdata.2.2 hqdata.2.2
    (show p*q <= 2*n+1 by rw [<- hdEq]; exact hdhi)
    (show n*n < p*q*r by rw [<- hmEq]; exact hmlo)
    (show p*q*r <= (n+1)*(n+1)+2*(n+1) by rw [<- hmEq]; exact hmhi)
  have hrd : Dvd.dvd r m := by rw [hmEq]; exact dvd_mul_left r (p*q)
  have hrprime := rough_le_index_prime (show 2 <= r by have htwo := hpdata.1.two_le; omega)
    hb.2.2 (fun t ht htr => hrough t ht (dvd_trans htr hrd))
  have hrsq := hrough r hrprime hrd
  have hrodd : r % 2 = 1 := by
    rcases hrprime.eq_two_or_odd with he | he
    next => rw [he] at hrsq; omega
    next => exact he
  have hrmem : Membership.mem (squareMediumOddPrimes n) r :=
    Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
      (And.intro hrprime (And.intro hrodd hrsq)))
  exact Exists.intro p (Exists.intro q (Exists.intro r (And.intro hp
    (And.intro hq (And.intro hrmem (And.intro hpq (And.intro (by omega)
      (And.intro (by omega) hmEq))))))))

/-- The complete joint incidence weight vanishes on every rough integer having such a supported band divisor. -/
theorem band_divisible_rough_joint_weight_zero {n m d : Nat}
    (hn : 17 <= n) (hmlo : n*n < m) (hmhi : m <= (n+1)*(n+1)+2*(n+1))
    (hd : Membership.mem (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d)
    (hdlo : n+1 < d) (hdhi : d <= 2*n+1) (hdm : Dvd.dvd d m)
    (hrough : forall t, Nat.Prime t -> Dvd.dvd t m -> n < t*t) :
    jointIncidenceWeight (((squareMediumOddPrimes n).filter (fun p => Dvd.dvd p m)).card) = 0 := by
  choose p q r hp hq hr hpq hpr hqr hmEq using
    rough_band_divisible_three_distinct hn hmlo hmhi hd hdlo hdhi hdm hrough
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

/-- An integer has an actual supported divisor in the near-diagonal doubled band. -/
def squareBandDivisible (n m : Nat) : Prop :=
  exists d : Nat, Membership.mem
    (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d /\
      n+1 < d /\ d <= 2*n+1 /\ Dvd.dvd d m

/-- The actual small-owner exclusion on an odd integer gives the exact prime-square roughness predicate. -/
theorem squareSmallSieve_rough_of_odd {n m : Nat} (hodd : m % 2 = 1)
    (hs : forall p, Membership.mem (squareSmallOddPrimes n) p -> Not (Dvd.dvd p m)) :
    forall p, Nat.Prime p -> Dvd.dvd p m -> n < p*p := by
  intro p hp hpd
  by_contra h
  have hsq : p*p <= n := by omega
  have hpo : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with he | he
    next =>
      rw [he] at hpd
      have hz := Nat.mod_eq_zero_of_dvd hpd
      omega
    next => exact he
  have hmem : Membership.mem (squareSmallOddPrimes n) p :=
    Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by nlinarith [hp.two_le]))
      (And.intro hp (And.intro hpo hsq)))
  exact hs p hmem hpd

/-- Removing all full integer cells with a supported band divisor leaves the complete jointly weighted rough sum unchanged. -/
theorem sum_jointIncidenceWeight_erase_band {n : Nat} (hn : 17 <= n) (s : Finset Nat)
    (hs : forall m, Membership.mem s m ->
      m % 2 = 1 /\ n*n < m /\ m <= (n+1)*(n+1)+2*(n+1)) :
    let t := s.filter (fun m => forall p, Membership.mem (squareSmallOddPrimes n) p -> Not (Dvd.dvd p m))
    t.sum (fun m => jointIncidenceWeight (((squareMediumOddPrimes n).filter (fun p => Dvd.dvd p m)).card)) =
      (t.filter (fun m => Not (squareBandDivisible n m))).sum
        (fun m => jointIncidenceWeight (((squareMediumOddPrimes n).filter (fun p => Dvd.dvd p m)).card)) := by
  let t := s.filter (fun m => forall p, Membership.mem (squareSmallOddPrimes n) p -> Not (Dvd.dvd p m))
  let w := fun m => jointIncidenceWeight (((squareMediumOddPrimes n).filter (fun p => Dvd.dvd p m)).card)
  change t.sum w = (t.filter (fun m => Not (squareBandDivisible n m))).sum w
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hb : squareBandDivisible n m
  next =>
    simp only [hb, not_true_eq_false, if_false]
    have hmt := Finset.mem_filter.mp hm
    have hmd := hs m hmt.1
    have hrough := squareSmallSieve_rough_of_odd hmd.1 hmt.2
    choose d hd hdlo hdhi hdm using hb
    exact band_divisible_rough_joint_weight_zero hn hmd.2.1 hmd.2.2 hd hdlo hdhi hdm hrough
  next => simp only [hb, not_false_eq_true, if_true]; rfl

/-- Either original adjacent-window packet is unchanged after the proved zero-weight integer cells are removed. -/
theorem squareJointPacket_erase_band {n x : Nat} (hn : 17 <= n)
    (hx : x = n \/ x = n+1) :
    squareJointPacket x (squareSmallOddPrimes n) (squareMediumOddPrimes n) =
      (((oddMultiplesInSquare x 1).filter (fun m =>
        forall p, Membership.mem (squareSmallOddPrimes n) p -> Not (Dvd.dvd p m))).filter
          (fun m => Not (squareBandDivisible n m))).sum
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
  exact sum_jointIncidenceWeight_erase_band hn (oddMultiplesInSquare x 1) hs

/-- The supported two-medium-factor correction consists of exactly one distinct prime pair. -/
theorem supported_two_medium_eq_pair {n d : Nat}
    (hd : Membership.mem (squareModulusSupport (squareSmallOddPrimes n)
      (squareMediumOddPrimes n)) d)
    (hc : (Inter.inter d.primeFactors (squareMediumOddPrimes n)).card = 2)
    (hbnd : d <= 2*n+1) :
    exists p q : Nat, Membership.mem (squareMediumOddPrimes n) p /\
      Membership.mem (squareMediumOddPrimes n) q /\ Not (p = q) /\ d = p*q := by
  choose x hx using Finset.mem_image.mp hd
  have hu := Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).1
  have hv := Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).2
  have hs : forall r, Membership.mem (Union.union x.1 x.2) r -> Nat.Prime r /\ r%2 = 1 := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    next =>
      exact And.intro (Finset.mem_filter.mp (hu hr)).2.1
        (Finset.mem_filter.mp (hu hr)).2.2.1
    next =>
      exact And.intro (Finset.mem_filter.mp (hv hr)).2.1
        (Finset.mem_filter.mp (hv hr)).2.2.1
  have hab : Disjoint (squareSmallOddPrimes n) (squareMediumOddPrimes n) := by
    apply Finset.disjoint_left.mpr
    intro r hr hq
    have hsmall := (Finset.mem_filter.mp hr).2.2.2
    have hbig := (Finset.mem_filter.mp hq).2.2.2
    omega
  have hprime := Nat.primeFactors_prod (fun r hr => (hs r hr).1)
  rw [hx.2] at hprime
  rw [hprime, (disjoint_subsets_union_inter hab (fun r hr => hu hr)
    (fun r hr => hv hr)).2] at hc
  choose p hp q hq hpq using Finset.one_lt_card.mp (show 1 < x.2.card by omega)
  have hpbig := (Finset.mem_filter.mp (hv hp)).2.2.2
  have hqbig := (Finset.mem_filter.mp (hv hq)).2.2.2
  have he := oddPrimeProduct_eq_pair_of_band hs
    (Finset.mem_union_right x.1 hp) (Finset.mem_union_right x.1 hq) hpq hpbig hqbig
    (by rw [hx.2]; exact hbnd)
  have hdeq : d = p*q := by rw [<- hx.2, he]; simp [hpq]
  exact Exists.intro p (Exists.intro q
    (And.intro (hv hp) (And.intro (hv hq) (And.intro hpq hdeq))))

/-- Actual balanced-pair correction moduli in the finite arithmetic band. -/
noncomputable def squareBandPairModuli (n D : Nat) : Finset Nat :=
  (((Finset.Icc (n+2) D).filter (fun d => d%2 = 1)).filter (fun d =>
    Membership.mem (squareModulusSupport (squareSmallOddPrimes n)
      (squareMediumOddPrimes n)) d /\
      (Inter.inter d.primeFactors (squareMediumOddPrimes n)).card = 2))

/-- A prime-independent pair allowance from the exact available odd factor slots. -/
def squareBandPairCapacity (n D : Nat) : Nat :=
  Nat.choose (((D/(Nat.sqrt n+1)+1)/2)-(Nat.sqrt n+1)/2) 2

/-- Both factors lie in the short reciprocal window, retaining their distinctness. -/
theorem squareBandPairModuli_subset_pair_products {n D : Nat} (hD : D <= 2*n+1) :
    squareBandPairModuli n D <=
      ((oddPrimesBetween (Nat.sqrt n+1) (D/(Nat.sqrt n+1))).powersetCard 2).image
        (fun t => t.prod (fun p => p)) := by
  intro d hd
  have hdata := Finset.mem_filter.mp hd
  have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hdata.1).1
  choose p q hp hq hpq he using supported_two_medium_eq_pair hdata.2.1 hdata.2.2
    (hi.2.trans hD)
  have hlow (r : Nat) (hr : Membership.mem (squareMediumOddPrimes n) r) :
      Nat.sqrt n+1 <= r := by
    have hh := (Finset.mem_filter.mp hr).2.2.2
    exact Nat.succ_le_iff.mpr (Nat.sqrt_lt.mpr hh)
  have hple : p <= D/(Nat.sqrt n+1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by
    have hh := Nat.mul_le_mul_left p (hlow q hq)
    rw [he] at hi
    omega)
  have hqle : q <= D/(Nat.sqrt n+1) := (Nat.le_div_iff_mul_le (by omega)).mpr (by
    have hh := Nat.mul_le_mul_left q (hlow p hp)
    rw [he] at hi
    nlinarith only [hh, hi.2])
  have hmem (r : Nat) (hr : Membership.mem (squareMediumOddPrimes n) r)
      (hle : r <= D/(Nat.sqrt n+1)) :
      Membership.mem (oddPrimesBetween (Nat.sqrt n+1) (D/(Nat.sqrt n+1))) r := by
    have hh := (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
      (And.intro hh.1 (And.intro hh.2.1 (hlow r hr))))
  apply Finset.mem_image.mpr
  refine Exists.intro ({p,q} : Finset Nat) (And.intro ?_ ?_)
  next =>
    apply Finset.mem_powersetCard.mpr
    constructor
    next =>
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with hr | hr <;> subst r
      next => exact hmem p hp hple
      next => exact hmem q hq hqle
    next => simp [hpq]
  next => simpa [hpq] using he.symm

/-- The full balanced-pair correction is bounded by an explicit binomial slot allowance. -/
theorem card_squareBandPairModuli_le_capacity {n D : Nat} (hD : D <= 2*n+1) :
    (squareBandPairModuli n D).card <= squareBandPairCapacity n D := by
  have hs := Finset.card_le_card (squareBandPairModuli_subset_pair_products hD)
  have hi := Finset.card_image_le (s :=
    (oddPrimesBetween (Nat.sqrt n+1) (D/(Nat.sqrt n+1))).powersetCard 2)
    (f := fun t : Finset Nat => t.prod (fun p => p))
  rw [Finset.card_powersetCard] at hi
  have hc := Nat.choose_le_choose 2
    (oddPrimesBetween_card_le (Nat.sqrt n+1) (D/(Nat.sqrt n+1)))
  exact hs.trans (hi.trans hc)

/-- Insert the geometric allowance into the existing band bound, preserving its full complement. -/
theorem squareJointPacket_arithmeticBand_capacity_lower {n J : Nat}
    (hJ : 1 <= J) (hcut : 4*J <= n) :
    let a := squareSmallOddPrimes n
    let b := squareMediumOddPrimes n
    let s := (squareModulusSupport a b).filter (fun d => n+1 < d)
    let p := quadraticLayerUnionPrefix n J s
    let t := (Finset.Icc (n+2) (quadraticPrefixBandEnd n J)).filter (fun d => d%2 = 1)
    3*t.sum ArithmeticFunction.moebius + 3*((t.filter Nat.Prime).card : Int) -
      (min t.card (squareBandPairCapacity n (quadraticPrefixBandEnd n J)) : Nat) -
      (9*(J : Int)+3) +
      ((squareModulusSupport a b).filter (fun d => Not (Membership.mem p d))).sum
        (fun d => squareModulusCoefficient a b d *
          (2*oddSquareFloor (n+1) d-oddSquareFloor n d)) <=
      2*squareJointPacket (n+1) a b-squareJointPacket n a b := by
  have h := squareJointPacket_arithmeticBand_lower hJ hcut
  have hc := card_squareBandPairModuli_le_capacity
    (show quadraticPrefixBandEnd n J <= 2*n+1 from
      (quadraticPrefixBandEnd_le_twice hcut).trans (by omega))
  have ht : (squareBandPairModuli n (quadraticPrefixBandEnd n J)).card <=
      (((Finset.Icc (n+2) (quadraticPrefixBandEnd n J)).filter (fun d => d%2 = 1)).card) :=
    Finset.card_filter_le _ _
  have hmin := le_min ht hc
  dsimp only [squareBandPairModuli] at hmin
  dsimp only at h
  dsimp only
  omega

end Nat.PrimeSieve
