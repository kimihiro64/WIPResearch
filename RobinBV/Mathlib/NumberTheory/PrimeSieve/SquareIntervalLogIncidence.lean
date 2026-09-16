/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Chebyshev
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalIncidence

/-!
# Logarithmic incidence and the exact repeated-prime remainder

The weight equals log m on primes, zero on semiprimes, cubes and squarefree
triples, and minus log p on p squared times r with distinct primes p and r.
The canonical repeated-prime quotient is injective on the correction class.
This gives an exact weighted capacity and an explicit Chebyshev root envelope,
without assuming a distribution estimate or positivity of the incidence sum.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- Logarithms of the distinct medium prime divisors. -/
noncomputable def mediumLogSum (n m : Nat) : Real :=
  (mediumPrimeDivisors n m).sum (fun p => Real.log p)

/-- The exact logarithmic incidence minorant, before its repeated-prime correction. -/
noncomputable def logIncidenceWeight (n m : Nat) : Real :=
  (1 - (mediumPrimeCount n m : Real)) * Real.log m +
    ((mediumPrimeCount n m : Real) - 1) * mediumLogSum n m

/-- The retained logarithmic correction on two-distinct-prime survivors. -/
noncomputable def logIncidenceCorrection (n m : Nat) : Real :=
  if mediumPrimeCount n m = 2 then Real.log m - mediumLogSum n m else 0

/-- Three distinct medium divisors account for the entire logarithm of a rough survivor. -/
theorem mediumLogSum_eq_log_of_count_three {n m : Nat}
    (hm : Membership.mem (squareRoughSurvivors n) m) (hthree : mediumPrimeCount n m = 3) :
    mediumLogSum n m = Real.log m := by
  have hd := Finset.mem_filter.mp hm
  have hhi := Finset.mem_range.mp hd.1
  rcases rough_prime_or_two_or_three hd.2.1 hhi hd.2.2.2.2 with hprime | htwo | htriple
  next => have hz := (mediumPrimeCount_eq_zero_iff hm).mpr hprime; omega
  next =>
    choose p q h using htwo
    have hlo : n * n < p * q := by rw [<- h.2.2.2]; exact hd.2.2.1
    have hhi' : p * q < (n + 1) * (n + 1) := by rw [<- h.2.2.2]; exact hhi
    rw [h.2.2.2, mediumPrimeCount,
      mediumPrimeDivisors_two h.1 h.2.1 h.2.2.1 hlo hhi'] at hthree
    simp at hthree
  next =>
    choose p q r h using htriple
    have hcutp : n < p * p := hd.2.2.2.2 p h.1
      (by rw [h.2.2.2.2.2]; exact Exists.intro (q * r) (by ac_rfl))
    have hcutq : n < q * q := hd.2.2.2.2 q h.2.1
      (by rw [h.2.2.2.2.2]; exact Exists.intro (p * r) (by ac_rfl))
    have hhi' : p * q * r < (n + 1) * (n + 1) := by rw [<- h.2.2.2.2.2]; exact hhi
    have hdiv : mediumPrimeDivisors n m = {p, q, r} := by
      rw [h.2.2.2.2.2]
      exact mediumPrimeDivisors_three h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hhi' hcutp hcutq
    have hcard : ({p, q, r} : Finset Nat).card = 3 := by
      rw [mediumPrimeCount, hdiv] at hthree
      exact hthree
    have hneq : Not (p = q) /\ Not (p = r) /\ Not (q = r) := by
      by_cases hpq : p = q <;> by_cases hpr : p = r <;> by_cases hqr : q = r <;>
        simp_all
    have hpR : Not ((p : Real) = 0) := by exact_mod_cast h.1.ne_zero
    have hqR : Not ((q : Real) = 0) := by exact_mod_cast h.2.1.ne_zero
    have hrR : Not ((r : Real) = 0) := by exact_mod_cast h.2.2.1.ne_zero
    rw [mediumLogSum, hdiv]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      hneq.1, hneq.2.1, hneq.2.2, or_self, not_false_eq_true, Finset.sum_singleton]
    rw [h.2.2.2.2.2, Nat.cast_mul, Nat.cast_mul,
      Real.log_mul (mul_ne_zero hpR hqR) hrR, Real.log_mul hpR hqR]
    ring

/-- Exact logarithmic prime indicator with its full repeated-prime correction. -/
theorem log_incidence_indicator {n m : Nat}
    (hm : Membership.mem (squareRoughSurvivors n) m) :
    (if Nat.Prime m then Real.log m else 0) =
      logIncidenceWeight n m + logIncidenceCorrection n m := by
  have hle := mediumPrimeCount_le_three hm
  have hiff := mediumPrimeCount_eq_zero_iff hm
  by_cases h0 : mediumPrimeCount n m = 0
  next =>
    have hp := hiff.mp h0
    have hdiv := Finset.card_eq_zero.mp h0
    have hD : mediumLogSum n m = 0 := by simp [mediumLogSum, hdiv]
    simp [logIncidenceWeight, logIncidenceCorrection, h0, hp, hD]
  next =>
    have hnp : Not (Nat.Prime m) := fun hp => h0 (hiff.mpr hp)
    have hcases : mediumPrimeCount n m = 1 \/ mediumPrimeCount n m = 2 \/
        mediumPrimeCount n m = 3 := by omega
    rcases hcases with h1 | h2 | h3
    next => simp [logIncidenceWeight, logIncidenceCorrection, h1, hnp]
    next => simp [logIncidenceWeight, logIncidenceCorrection, h2, hnp]; ring
    next =>
      have hD := mediumLogSum_eq_log_of_count_three hm h3
      simp [logIncidenceWeight, logIncidenceCorrection, h3, hnp, hD]
      ring

/-- The product of distinct selected prime divisors divides the positive integer. -/
theorem mediumLogSum_le_log {n m : Nat} (hm : 0 < m) :
    mediumLogSum n m <= Real.log m := by
  let b := mediumPrimeDivisors n m
  have hb : forall p, Membership.mem b p -> Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1
  have hdiv : Dvd.dvd (b.prod (fun p => p)) m :=
    (prod_primes_dvd_iff hb m).mpr (fun p hp => (Finset.mem_filter.mp hp).2.2)
  have hpos : 0 < b.prod (fun p => p) := Finset.prod_pos (fun p hp => (hb p hp).pos)
  have hlog : Real.log ((b.prod (fun p => p) : Nat) : Real) = mediumLogSum n m := by
    rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hb p hp).ne_zero)]
    rfl
  rw [<- hlog]
  apply Real.log_le_log (by exact_mod_cast hpos)
  exact_mod_cast Nat.le_of_dvd hm hdiv

/-- The logarithmic correction is nonnegative; its sign is proved from divisibility. -/
theorem logIncidenceCorrection_nonneg {n m : Nat} (hm : 0 < m) :
    0 <= logIncidenceCorrection n m := by
  unfold logIncidenceCorrection
  split_ifs
  next => exact sub_nonneg.mpr (mediumLogSum_le_log hm)
  next => exact le_rfl

/-- Actual square-interval prime logarithms equal the incidence sum plus its correction. -/
theorem prime_theta_log_incidence_identity {n : Nat} (hn : 2 <= n) :
    (squareIntervalPrimes n).sum (fun m => Real.log m) =
      (squareRoughSurvivors n).sum (logIncidenceWeight n) +
        (squareRoughSurvivors n).sum (logIncidenceCorrection n) := by
  rw [<- squareRoughSurvivors_filter_prime hn, Finset.sum_filter, <- Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m hm => log_incidence_indicator hm)

/-- The retained logarithmic incidence sum is a pointwise minorant for prime supply. -/
theorem prime_theta_log_incidence_lower_bound {n : Nat} (hn : 2 <= n) :
    (squareRoughSurvivors n).sum (logIncidenceWeight n) <=
      (squareIntervalPrimes n).sum (fun m => Real.log m) := by
  rw [prime_theta_log_incidence_identity hn]
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro m hm
  have hmdata := Finset.mem_filter.mp hm
  exact logIncidenceCorrection_nonneg (by omega)

/-- The medium divisor set of a repeated-prime product, with no ordering assumption. -/
theorem mediumPrimeDivisors_repeated {n p r : Nat}
    (hp : Nat.Prime p) (hr : Nat.Prime r) (hpn : p <= n) (hrn : r <= n) :
    mediumPrimeDivisors n (p * p * r) = {p, r} := by
  ext t
  simp only [mediumPrimeDivisors, Finset.mem_filter, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  next =>
    intro h
    rcases h.2.1.dvd_mul.mp h.2.2 with htpp | htr
    next =>
      have htp := (h.2.1.dvd_mul.mp htpp).elim id id
      exact Or.inl ((hp.eq_one_or_self_of_dvd t htp).resolve_left h.2.1.ne_one)
    next => exact Or.inr ((hr.eq_one_or_self_of_dvd t htr).resolve_left h.2.1.ne_one)
  next =>
    intro h
    rcases h with htp | htr
    next =>
      subst t
      exact And.intro (by omega) (And.intro hp (Exists.intro (p * r) (by ac_rfl)))
    next =>
      subst t
      exact And.intro (by omega) (And.intro hr (dvd_mul_left r (p * p)))

/-- Each two-distinct-prime correction is exactly the logarithm of the repeated prime. -/
theorem logIncidenceCorrection_eq_repeated_log {n m p r : Nat}
    (hm : Membership.mem (twoDistinctSurvivors n) m)
    (hcell : RepeatedPrimeCell n (Nat.sqrt n + 1) p r) (heq : m = p * p * r) :
    logIncidenceCorrection n m = Real.log p := by
  have hmdata := Finset.mem_filter.mp hm
  have hrange := Finset.mem_product.mp (Finset.mem_filter.mp hcell.mem_cells).1
  have hpn : p <= n := by have := Finset.mem_range.mp hrange.1; omega
  have hrn : r <= n := by have := Finset.mem_range.mp hrange.2; omega
  have hdiv : mediumPrimeDivisors n m = {p, r} := by
    rw [heq]
    exact mediumPrimeDivisors_repeated hcell.prime_left hcell.prime_right hpn hrn
  have hpr : Not (p = r) := by
    intro h
    have hc := hmdata.2
    rw [mediumPrimeCount, hdiv, h] at hc
    simp at hc
  have hpR : Not ((p : Real) = 0) := by exact_mod_cast hcell.prime_left.ne_zero
  have hrR : Not ((r : Real) = 0) := by exact_mod_cast hcell.prime_right.ne_zero
  rw [logIncidenceCorrection, if_pos hmdata.2, mediumLogSum, hdiv]
  simp only [Finset.sum_insert, Finset.mem_singleton, hpr, not_false_eq_true,
    Finset.sum_singleton]
  rw [heq, Nat.cast_mul, Nat.cast_mul,
    Real.log_mul (mul_ne_zero hpR hpR) hrR, Real.log_mul hpR hpR]
  ring

/-- An individual repeated-prime correction is at most the logarithm of the index. -/
theorem logIncidenceCorrection_le_log_index {n m : Nat}
    (hm : Membership.mem (twoDistinctSurvivors n) m) :
    logIncidenceCorrection n m <= Real.log n := by
  choose p r h using twoDistinctSurvivor_has_repeated_cell hm
  rw [logIncidenceCorrection_eq_repeated_log hm h.1 h.2]
  have hrange := Finset.mem_product.mp (Finset.mem_filter.mp h.1.mem_cells).1
  have hp : p <= n := by have := Finset.mem_range.mp hrange.1; omega
  apply Real.log_le_log (by exact_mod_cast h.1.prime_left.pos)
  exact_mod_cast hp

/-- The full correction is supported exactly on the two-distinct survivor class. -/
theorem sum_logIncidenceCorrection_eq_twoDistinct (n : Nat) :
    (squareRoughSurvivors n).sum (logIncidenceCorrection n) =
      (twoDistinctSurvivors n).sum (logIncidenceCorrection n) := by
  rw [twoDistinctSurvivors, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h : mediumPrimeCount n m = 2 <;> simp [logIncidenceCorrection, h]

/-- The cardinal capacity gives a coarse explicit logarithmic remainder bound. -/
theorem sum_logIncidenceCorrection_le_capacity {n : Nat} (hn : 2 <= n) :
    (squareRoughSurvivors n).sum (logIncidenceCorrection n) <=
      ((repeatedPrimeCapacity n (Nat.sqrt n + 1)).card : Real) * Real.log n := by
  rw [sum_logIncidenceCorrection_eq_twoDistinct]
  apply le_trans (Finset.sum_le_sum (fun m hm => logIncidenceCorrection_le_log_index hm))
  simp only [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right
  next => exact_mod_cast card_twoDistinctSurvivors_le_capacity n
  next => exact Real.log_nonneg (by exact_mod_cast (show 1 <= n by omega))

/-- A first two-sided estimate with the cardinal-capacity logarithmic remainder. -/
theorem prime_theta_log_incidence_upper_bound {n : Nat} (hn : 2 <= n) :
    (squareIntervalPrimes n).sum (fun m => Real.log m) <=
      (squareRoughSurvivors n).sum (logIncidenceWeight n) +
        ((repeatedPrimeCapacity n (Nat.sqrt n + 1)).card : Real) * Real.log n := by
  rw [prime_theta_log_incidence_identity hn]
  exact _root_.add_le_add (le_refl _) (sum_logIncidenceCorrection_le_capacity hn)

/-- Canonical repeated-prime quotient on the two-distinct survivor class. -/
def repeatedPrimeQuotient (n m : Nat) : Nat :=
  m / (mediumPrimeDivisors n m).prod (fun p => p)

/-- The canonical quotient equals the repeated prime, not an arbitrary chosen factor. -/
theorem repeatedPrimeQuotient_eq {n m p r : Nat}
    (hm : Membership.mem (twoDistinctSurvivors n) m)
    (hcell : RepeatedPrimeCell n (Nat.sqrt n + 1) p r) (heq : m = p * p * r) :
    repeatedPrimeQuotient n m = p := by
  have hrange := Finset.mem_product.mp (Finset.mem_filter.mp hcell.mem_cells).1
  have hpn : p <= n := by have := Finset.mem_range.mp hrange.1; omega
  have hrn : r <= n := by have := Finset.mem_range.mp hrange.2; omega
  have hdiv : mediumPrimeDivisors n m = {p, r} := by
    rw [heq]
    exact mediumPrimeDivisors_repeated hcell.prime_left hcell.prime_right hpn hrn
  have hpr : Not (p = r) := by
    intro h
    have hc := (Finset.mem_filter.mp hm).2
    rw [mediumPrimeCount, hdiv, h] at hc
    simp at hc
  rw [repeatedPrimeQuotient, hdiv]
  simp only [Finset.prod_insert, Finset.mem_singleton, hpr, not_false_eq_true,
    Finset.prod_singleton]
  rw [heq, Nat.mul_assoc]
  exact Nat.mul_div_cancel p (Nat.mul_pos hcell.prime_left.pos hcell.prime_right.pos)

/-- The repeated-prime quotient lies in the exact quadratic prime capacity. -/
theorem repeatedPrimeQuotient_mem_capacity {n m : Nat}
    (hm : Membership.mem (twoDistinctSurvivors n) m) :
    Membership.mem (repeatedPrimeCapacity n (Nat.sqrt n + 1)) (repeatedPrimeQuotient n m) := by
  choose p r h using twoDistinctSurvivor_has_repeated_cell hm
  rw [repeatedPrimeQuotient_eq hm h.1 h.2]
  have hrange := Finset.mem_product.mp (Finset.mem_filter.mp h.1.mem_cells).1
  have hbound := Nat.mul_le_mul_left (p * p) h.1.lower_right
  exact Finset.mem_filter.mpr (And.intro hrange.1 (And.intro h.1.prime_left
    (And.intro h.1.lower_left (lt_of_le_of_lt hbound h.1.interval_upper))))

/-- Different two-distinct survivors have different repeated-prime quotients. -/
theorem repeatedPrimeQuotient_injOn (n : Nat) :
    Set.InjOn (repeatedPrimeQuotient n) (twoDistinctSurvivors n) := by
  intro m hm k hk heq
  choose p r hp using twoDistinctSurvivor_has_repeated_cell hm
  choose q s hq using twoDistinctSurvivor_has_repeated_cell hk
  have hpq : p = q := by
    rw [repeatedPrimeQuotient_eq hm hp.1 hp.2, repeatedPrimeQuotient_eq hk hq.1 hq.2] at heq
    exact heq
  have hpair := repeatedPrimeCells_fst_injOn n (Nat.sqrt n + 1)
    hp.1.mem_cells hq.1.mem_cells hpq
  have hrs : r = s := congrArg Prod.snd hpair
  rw [hp.2, hq.2, hpq, hrs]

/-- The correction is the logarithm of the canonical repeated-prime quotient. -/
theorem logIncidenceCorrection_eq_log_quotient {n m : Nat}
    (hm : Membership.mem (twoDistinctSurvivors n) m) :
    logIncidenceCorrection n m = Real.log (repeatedPrimeQuotient n m) := by
  choose p r h using twoDistinctSurvivor_has_repeated_cell hm
  rw [logIncidenceCorrection_eq_repeated_log hm h.1 h.2, repeatedPrimeQuotient_eq hm h.1 h.2]

/-- Injectivity retains the sharper sum of logarithms over admissible repeated primes. -/
theorem sum_logIncidenceCorrection_le_weighted_capacity (n : Nat) :
    (squareRoughSurvivors n).sum (logIncidenceCorrection n) <=
      (repeatedPrimeCapacity n (Nat.sqrt n + 1)).sum (fun p => Real.log p) := by
  rw [sum_logIncidenceCorrection_eq_twoDistinct]
  have heq : (twoDistinctSurvivors n).sum (logIncidenceCorrection n) =
      ((twoDistinctSurvivors n).image (repeatedPrimeQuotient n)).sum (fun p => Real.log p) := by
    rw [Finset.sum_image (repeatedPrimeQuotient_injOn n)]
    exact Finset.sum_congr rfl (fun m hm => logIncidenceCorrection_eq_log_quotient hm)
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  next =>
    intro p hp
    choose m hm using Finset.mem_image.mp hp
    rw [<- hm.2]
    exact repeatedPrimeQuotient_mem_capacity hm.1
  next =>
    intro p hp hnot
    have hprime := (Finset.mem_filter.mp hp).2.1
    exact Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)

/-- The exact weighted prime capacity bounds the prime-logarithm remainder. -/
theorem prime_theta_log_incidence_weighted_upper_bound {n : Nat} (hn : 2 <= n) :
    (squareIntervalPrimes n).sum (fun m => Real.log m) <=
      (squareRoughSurvivors n).sum (logIncidenceWeight n) +
        (repeatedPrimeCapacity n (Nat.sqrt n + 1)).sum (fun p => Real.log p) := by
  rw [prime_theta_log_incidence_identity hn]
  exact _root_.add_le_add (le_refl _) (sum_logIncidenceCorrection_le_weighted_capacity n)

/-- The exact integer upper endpoint for an admissible repeated prime. -/
def repeatedPrimeUpper (n : Nat) : Nat :=
  Nat.sqrt ((n * n + 2 * n) / (Nat.sqrt n + 1))

/-- The weighted capacity is bounded by the Chebyshev function at its exact integer endpoint. -/
theorem repeatedPrimeCapacity_le_theta (n : Nat) :
    (repeatedPrimeCapacity n (Nat.sqrt n + 1)).sum (fun p => Real.log p) <=
      Chebyshev.theta (repeatedPrimeUpper n) := by
  simp only [Chebyshev.theta, Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  next =>
    intro p hp
    have hd := Finset.mem_filter.mp hp
    have hprod : p * p * (Nat.sqrt n + 1) <= n * n + 2 * n := by
      nlinarith [hd.2.2.2]
    have hsq : p * p <= (n * n + 2 * n) / (Nat.sqrt n + 1) :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr hprod
    have hpY : p <= repeatedPrimeUpper n := Nat.le_sqrt.mpr hsq
    exact Finset.mem_filter.mpr
      (And.intro (Finset.mem_Ioc.mpr (And.intro hd.2.1.pos hpY)) hd.2.1)
  next =>
    intro p hp hnot
    have hprime := (Finset.mem_filter.mp hp).2
    exact Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)

/-- Mathlib's Chebyshev bound gives an explicit logarithm-of-four root envelope. -/
theorem sum_logIncidenceCorrection_le_explicit_root (n : Nat) :
    (squareRoughSurvivors n).sum (logIncidenceCorrection n) <=
      Real.log 4 * (repeatedPrimeUpper n : Real) := by
  exact le_trans (sum_logIncidenceCorrection_le_weighted_capacity n)
    (le_trans (repeatedPrimeCapacity_le_theta n)
      (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)))

/-- A pointwise prime-logarithm estimate with a fully explicit root remainder. -/
theorem prime_theta_log_incidence_explicit_upper_bound {n : Nat} (hn : 2 <= n) :
    (squareIntervalPrimes n).sum (fun m => Real.log m) <=
      (squareRoughSurvivors n).sum (logIncidenceWeight n) +
        Real.log 4 * (repeatedPrimeUpper n : Real) := by
  rw [prime_theta_log_incidence_identity hn]
  exact _root_.add_le_add (le_refl _) (sum_logIncidenceCorrection_le_explicit_root n)

/-- The exact repeated-prime endpoint has fourth power strictly below the index successor cubed. -/
theorem repeatedPrimeUpper_fourth_lt_cube (n : Nat) :
    (repeatedPrimeUpper n) ^ 4 < (n + 1) ^ 3 := by
  let s := Nat.sqrt n + 1
  let U := n * n + 2 * n
  let Y := repeatedPrimeUpper n
  have hs : n + 1 <= s * s := by
    have h := Nat.lt_succ_sqrt n
    dsimp [s]
    nlinarith
  have hY : Y * Y <= U / s := Nat.sqrt_le _
  have hprod : Y * Y * s <= U := (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mp hY
  have hsq := Nat.mul_le_mul hprod hprod
  by_contra hnot
  have hbad : (n + 1) ^ 3 <= Y ^ 4 := Nat.le_of_not_gt hnot
  have hmul := Nat.mul_le_mul hbad hs
  have hid : (Y * Y * s) * (Y * Y * s) = Y ^ 4 * (s * s) := by ring
  rw [hid] at hsq
  dsimp [U] at hsq
  nlinarith only [hsq, hmul]

end Nat.PrimeSieve
