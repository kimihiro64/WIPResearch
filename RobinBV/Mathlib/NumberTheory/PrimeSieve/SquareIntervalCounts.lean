/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Data.Finset.Prod
import RobinBV.Mathlib.NumberTheory.PrimeSieve.InclusionExclusion
import RobinBV.Mathlib.NumberTheory.PrimeSieve.Owner
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalFactorization

/-!
# Exact finite counts in square intervals

Repeated factors are not discarded as an error: their actual cells inject into
the primes satisfying the exact quadratic capacity bound.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

/-- An odd repeated-prime triple in the open square interval. -/
structure RepeatedPrimeCell (n s p r : Nat) : Prop where
  prime_left : Nat.Prime p
  prime_right : Nat.Prime r
  lower_left : s <= p
  lower_right : s <= r
  cutoff : n < p * p
  odd_left : p % 2 = 1
  odd_right : r % 2 = 1
  interval_lower : n * n < p * p * r
  interval_upper : p * p * r < (n + 1) * (n + 1)

/-- The actual finite cells, including prime cubes when they occur. -/
noncomputable def repeatedPrimeCells (n s : Nat) : Finset (Prod Nat Nat) := by
  classical
  exact ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    (fun x => RepeatedPrimeCell n s x.1 x.2)

/-- Prime capacity with the exact lower cofactor retained. -/
def repeatedPrimeCapacity (n s : Nat) : Finset Nat :=
  (Finset.range (n + 1)).filter
    (fun p => Nat.Prime p /\ s <= p /\ p * p * s < (n + 1) * (n + 1))

/-- The defining finite range omits no repeated-prime cell. -/
theorem RepeatedPrimeCell.mem_cells {n s p r : Nat} (h : RepeatedPrimeCell n s p r) :
    Membership.mem (repeatedPrimeCells n s) (Prod.mk p r) := by
  classical
  have hr : r <= n := cofactor_le_index h.cutoff h.interval_upper
  have hp : p <= n := by
    have hmul := Nat.mul_le_mul_left (p * p) (show 1 <= r from h.prime_right.one_lt.le)
    have hsq : p * p < (n + 1) * (n + 1) := by nlinarith [h.interval_upper]
    nlinarith
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_product.mpr (And.intro (Finset.mem_range.mpr (by omega))
      (Finset.mem_range.mpr (by omega)))) h)

/-- Projection to the repeated prime is injective, even when cubes are admitted. -/
theorem repeatedPrimeCells_fst_injOn (n s : Nat) :
    Set.InjOn (fun x : Prod Nat Nat => x.1) (repeatedPrimeCells n s) := by
  classical
  intro x hx y hy hxy
  change x.1 = y.1 at hxy
  have hx' : RepeatedPrimeCell n s x.1 x.2 := (Finset.mem_filter.mp hx).2
  have hy' : RepeatedPrimeCell n s y.1 y.2 := (Finset.mem_filter.mp hy).2
  apply Prod.ext hxy
  have hylo : n * n < x.1 * x.1 * y.2 := by rw [hxy]; exact hy'.interval_lower
  have hyhi : x.1 * x.1 * y.2 < (n + 1) * (n + 1) := by
    rw [hxy]
    exact hy'.interval_upper
  exact odd_cofactor_unique hx'.cutoff hx'.odd_right hy'.odd_right
    hx'.interval_lower hx'.interval_upper hylo hyhi

/-- A pointwise upper bound by the exact available repeated-prime capacity. -/
theorem card_repeatedPrimeCells_le_capacity (n s : Nat) :
    (repeatedPrimeCells n s).card <= (repeatedPrimeCapacity n s).card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  next =>
    intro x hx
    have hx' : RepeatedPrimeCell n s x.1 x.2 := (Finset.mem_filter.mp hx).2
    have hxrange := (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
    have hbound := Nat.mul_le_mul_left (x.1 * x.1) hx'.lower_right
    apply Finset.mem_filter.mpr
    exact And.intro hxrange (And.intro hx'.prime_left (And.intro hx'.lower_left
      (lt_of_le_of_lt hbound hx'.interval_upper)))
  next => exact repeatedPrimeCells_fst_injOn n s

/-- Odd integers between consecutive squares with every small owner excluded. -/
noncomputable def squareRoughSurvivors (n : Nat) : Finset Nat := by
  classical
  exact (Finset.range ((n + 1) * (n + 1))).filter (fun m =>
    2 <= m /\ n * n < m /\ m % 2 = 1 /\
      forall p : Nat, Nat.Prime p -> Dvd.dvd p m -> n < p * p)

attribute [local instance] Classical.propDecidable

/-- Exact disjoint counting identity, with both composite multiplicities retained. -/
theorem card_squareRoughSurvivors (n : Nat) :
    (squareRoughSurvivors n).card =
      ((squareRoughSurvivors n).filter Nat.Prime).card +
      ((squareRoughSurvivors n).filter IsTwoPrime).card +
      ((squareRoughSurvivors n).filter IsThreePrime).card := by
  classical
  let S := squareRoughSurvivors n
  have htwo : (S.filter (fun m => Not (Nat.Prime m))).filter IsTwoPrime =
      S.filter IsTwoPrime := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    next => intro h; exact And.intro h.1.1 h.2
    next => intro h; exact And.intro (And.intro h.1 h.2.not_prime) h.2
  have hthree : (S.filter (fun m => Not (Nat.Prime m))).filter
      (fun m => Not (IsTwoPrime m)) = S.filter IsThreePrime := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    next =>
      intro h
      have hm := Finset.mem_filter.mp h.1.1
      have hhi := Finset.mem_range.mp hm.1
      have hcases := rough_prime_or_two_or_three hm.2.1 hhi hm.2.2.2.2
      rcases hcases with hp | h2 | h3
      next => exact False.elim (h.1.2 hp)
      next => exact False.elim (h.2 h2)
      next => exact And.intro h.1.1 h3
    next =>
      intro h
      exact And.intro (And.intro h.1 h.2.not_prime)
        (fun h2 => h2.not_threePrime h.2)
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) Nat.Prime
  have hsplit2 := Finset.card_filter_add_card_filter_not
    (s := S.filter (fun m => Not (Nat.Prime m))) IsTwoPrime
  rw [htwo, hthree] at hsplit2
  change S.card = (S.filter Nat.Prime).card + (S.filter IsTwoPrime).card +
    (S.filter IsThreePrime).card
  omega

/-- All primes in the open square interval, without a sieve condition. -/
noncomputable def squareIntervalPrimes (n : Nat) : Finset Nat :=
  (Finset.range ((n + 1) * (n + 1))).filter (fun m => n * n < m /\ Nat.Prime m)

/-- For index at least two, the rough prime count is the actual interval prime count. -/
theorem squareRoughSurvivors_filter_prime {n : Nat} (hn : 2 <= n) :
    (squareRoughSurvivors n).filter Nat.Prime = squareIntervalPrimes n := by
  classical
  ext m
  simp only [squareRoughSurvivors, squareIntervalPrimes, Finset.mem_filter]
  constructor
  next => intro h; exact And.intro h.1.1 (And.intro h.1.2.2.1 h.2)
  next =>
    intro h
    have hodd : m % 2 = 1 := h.2.2.eq_two_or_odd.resolve_left (by nlinarith [h.2.1])
    refine And.intro (And.intro h.1 (And.intro h.2.2.two_le
      (And.intro h.2.1 (And.intro hodd ?_)))) h.2.2
    intro p hp hpd
    have hpm : p = m := (h.2.2.eq_one_or_self_of_dvd p hpd).resolve_left hp.ne_one
    rw [hpm]
    nlinarith [h.2.1]

/-- Exact prime supply equals the survivors minus the two retained composite counts. -/
theorem square_interval_prime_count_identity {n : Nat} (hn : 2 <= n) :
    (squareRoughSurvivors n).card = (squareIntervalPrimes n).card +
      ((squareRoughSurvivors n).filter IsTwoPrime).card +
      ((squareRoughSurvivors n).filter IsThreePrime).card := by
  rw [card_squareRoughSurvivors, squareRoughSurvivors_filter_prime hn]

/-- Odd multiples up to a closed endpoint, including all repeated factors. -/
noncomputable def oddMultiplesUpTo (d X : Nat) : Finset Nat :=
  (Finset.range (X + 1)).filter (fun m => m % 2 = 1 /\ Dvd.dvd d m)

/-- Exact progression parametrization of the odd multiples of an odd divisor. -/
theorem oddMultiplesUpTo_image {d X : Nat} (hd : d % 2 = 1) :
    oddMultiplesUpTo d X =
      (Finset.range ((X / d + 1) / 2)).image (fun k => d * (2 * k + 1)) := by
  have hd0 : 0 < d := by omega
  ext m
  constructor
  next =>
    intro hm
    have hm' := Finset.mem_filter.mp hm
    have hmX : m <= X := by have := Finset.mem_range.mp hm'.1; omega
    choose r hmr using hm'.2.2
    have hr : r % 2 = 1 := by
      have hmod := hm'.2.1
      rw [hmr, Nat.mul_mod, hd] at hmod
      simpa using hmod
    have hrX : r <= X / d := (Nat.le_div_iff_mul_le hd0).mpr (by
      simpa only [Nat.mul_comm] using (hmr.symm.trans_le hmX))
    apply Finset.mem_image.mpr
    refine Exists.intro (r / 2) (And.intro ?_ ?_)
    next => apply Finset.mem_range.mpr; omega
    next =>
      have hre : r = 2 * (r / 2) + 1 := by omega
      rw [<- hre]
      exact hmr.symm
  next =>
    intro hm
    choose k hk using Finset.mem_image.mp hm
    have hkbound := Finset.mem_range.mp hk.1
    have hrX : 2 * k + 1 <= X / d := by omega
    have hmX : m <= X := by
      rw [<- hk.2]
      have hmul := (Nat.le_div_iff_mul_le hd0).mp hrX
      simpa only [Nat.mul_comm] using hmul
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_range.mpr (by omega)) (And.intro ?_ ?_)
    next => rw [<- hk.2, Nat.mul_mod, hd]; omega
    next => rw [<- hk.2]; exact dvd_mul_right d (2 * k + 1)

/-- Exact floor count of odd multiples; no density approximation is used. -/
theorem card_oddMultiplesUpTo {d X : Nat} (hd : d % 2 = 1) :
    (oddMultiplesUpTo d X).card = (X / d + 1) / 2 := by
  have hd0 : 0 < d := by omega
  have hinj : Function.Injective (fun k : Nat => d * (2 * k + 1)) := by
    intro a b hab
    have h := Nat.eq_of_mul_eq_mul_left hd0 hab
    omega
  rw [oddMultiplesUpTo_image hd, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- Odd multiples in the open interval between consecutive squares. -/
noncomputable def oddMultiplesInSquare (n d : Nat) : Finset Nat :=
  (oddMultiplesUpTo d (n * n + 2 * n)).filter (fun m => n * n < m)

/-- Exact endpoint subtraction for odd multiples of every odd divisor. -/
theorem card_oddMultiplesInSquare {d : Nat} (n : Nat) (hd : d % 2 = 1) :
    (oddMultiplesInSquare n d).card + (n * n / d + 1) / 2 =
      ((n * n + 2 * n) / d + 1) / 2 := by
  have hprefix : (oddMultiplesUpTo d (n * n + 2 * n)).filter
      (fun m => Not (n * n < m)) = oddMultiplesUpTo d (n * n) := by
    ext m
    simp only [oddMultiplesUpTo, Finset.mem_filter, Finset.mem_range]
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := oddMultiplesUpTo d (n * n + 2 * n)) (fun m => n * n < m)
  rw [hprefix, card_oddMultiplesUpTo hd, card_oddMultiplesUpTo hd] at hsplit
  exact hsplit

/-- Complete residue-by-residue count of multiples of three that are not even. -/
theorem count_owner_three_residues (n : Nat) :
    3 * (oddMultiplesInSquare n 3).card +
        (if n % 6 = 2 then 2 else if n % 6 = 4 then 1 else 0) =
      n + (if n % 6 = 1 then 2 else if n % 6 = 5 then 1 else 0) := by
  have hcount := card_oddMultiplesInSquare n (d := 3) (by decide)
  have hsqmod := Nat.mul_mod n n 6
  have hcases : n % 6 = 0 \/ n % 6 = 1 \/ n % 6 = 2 \/
      n % 6 = 3 \/ n % 6 = 4 \/ n % 6 = 5 := by omega
  rcases hcases with h | h | h | h | h | h <;>
    rw [h] at hsqmod <;> norm_num at hsqmod <;> norm_num [h] <;> omega

/-- Uniform sharp bound on the scaled owner-three discrepancy. -/
theorem count_owner_three_sharp_bounds (n : Nat) :
    n <= 3 * (oddMultiplesInSquare n 3).card + 2 /\
      3 * (oddMultiplesInSquare n 3).card <= n + 2 := by
  have h := count_owner_three_residues n
  split_ifs at h <;> omega

/-- The odd multiples of three are exactly the existing least-owner-three packet. -/
theorem oddMultiplesUpTo_three_eq_owner (X : Nat) :
    oddMultiplesUpTo 3 X = Nat.PrimeSieve.leastPrimeOwnerPacketAt 3 X := by
  classical
  ext m
  simp only [oddMultiplesUpTo, Nat.PrimeSieve.leastPrimeOwnerPacketAt,
    Nat.PrimeSieve.leastPrimeOwnerSurvivorsBefore, Finset.mem_filter,
    Finset.mem_range, Finset.mem_Icc]
  constructor
  next =>
    intro h
    have hmpos : 0 < m := by have := h.2.1; omega
    have hmthree : 3 <= m := Nat.le_of_dvd hmpos h.2.2
    refine And.intro (And.intro (And.intro (by omega) (by omega)) ?_) h.2.2
    intro p hp hple hpd
    have hptwo : p = 2 := by have := hp.two_le; omega
    subst p
    have hmod := Nat.mod_eq_zero_of_dvd hpd
    have hodd := h.2.1
    omega
  next =>
    intro h
    have hnot : Not (Dvd.dvd 2 m) := h.1.2 2 Nat.prime_two (by decide)
    have hodd : m % 2 = 1 := by
      have hmod : Not (m % 2 = 0) := fun hz => hnot (Nat.dvd_of_mod_eq_zero hz)
      omega
    exact And.intro (by omega) (And.intro hodd h.2)

/-- A selected prime owns an odd candidate after all specified earlier owners are excluded. -/
noncomputable def oddSievedOwnerInSquare (n p : Nat) (s : Finset Nat) : Finset Nat :=
  (oddMultiplesInSquare n 1).filter (fun m => Dvd.dvd p m /\
    forall r, Membership.mem s r -> Not (Dvd.dvd r m))

/-- Divisibility filtering of the odd square interval gives the exact multiple packet. -/
theorem oddMultiplesInSquare_one_filter (n d : Nat) :
    (oddMultiplesInSquare n 1).filter (fun m => Dvd.dvd d m) =
      oddMultiplesInSquare n d := by
  ext m
  simp [oddMultiplesInSquare, oddMultiplesUpTo, and_assoc, and_left_comm, and_comm]

/-- Complete signed subset expansion of the actual odd owner count. -/
theorem card_oddSievedOwnerInSquare (n : Nat) {p : Nat} {s : Finset Nat}
    (hp : Nat.Prime p)
    (hs : forall r, Membership.mem s r -> Nat.Prime r /\ r < p) :
    ((oddSievedOwnerInSquare n p s).card : Int) =
      Finset.sum s.powerset (fun t => (-1 : Int) ^ t.card *
        ((oddMultiplesInSquare n (p * Finset.prod t (fun r => r))).card : Int)) := by
  have h := Nat.PrimeSieve.sum_ownerPrimeSieve_eq_powerset (fun _ => (1 : Int))
    (oddMultiplesInSquare n 1) hp hs
  simp_rw [oddMultiplesInSquare_one_filter] at h
  simpa [oddSievedOwnerInSquare] using h

/-- All odd prime owners strictly earlier than the given prime clock. -/
noncomputable def oddEarlierPrimes (p : Nat) : Finset Nat :=
  (Finset.range p).filter (fun r => Nat.Prime r /\ r % 2 = 1)

/-- The odd-domain formulation is the original least-owner packet restricted to the square interval. -/
theorem oddSievedOwnerInSquare_eq_owner {n p : Nat} (hp3 : 3 <= p) :
    oddSievedOwnerInSquare n p (oddEarlierPrimes p) =
      (Nat.PrimeSieve.leastPrimeOwnerPacketAt p (n * n + 2 * n)).filter
        (fun m => n * n < m) := by
  ext m
  simp only [oddSievedOwnerInSquare, oddMultiplesInSquare, oddMultiplesUpTo,
    Nat.PrimeSieve.leastPrimeOwnerPacketAt, Nat.PrimeSieve.leastPrimeOwnerSurvivorsBefore,
    Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, one_dvd, and_true]
  constructor
  next =>
    intro h
    have hodd := h.1.1.2
    have hmpos : 0 < m := by omega
    have hmge := Nat.le_of_dvd hmpos h.2.1
    refine And.intro (And.intro (And.intro (And.intro (by omega) (by omega)) ?_)
      h.2.1) h.1.2
    intro r hr hrle hrd
    rcases hr.eq_two_or_odd with hr2 | hro
    next =>
      subst r
      have hmod := Nat.mod_eq_zero_of_dvd hrd
      omega
    next =>
      have hrmem : Membership.mem (oddEarlierPrimes p) r :=
        Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega)) (And.intro hr hro))
      exact h.2.2 r hrmem hrd
  next =>
    intro h
    have hnot : Not (Dvd.dvd 2 m) := h.1.1.2 2 Nat.prime_two (by omega)
    have hodd : m % 2 = 1 := by
      have hmod : Not (m % 2 = 0) := fun hz => hnot (Nat.dvd_of_mod_eq_zero hz)
      omega
    refine And.intro (And.intro (And.intro (by omega) hodd) h.2)
      (And.intro h.1.2 ?_)
    intro r hrmem hrd
    have hrdata := Finset.mem_filter.mp hrmem
    have hrlt := Finset.mem_range.mp hrdata.1
    exact h.1.1.2 r hrdata.2.1 (by omega) hrd



/-- Exact signed floor difference for the odd-multiple count. -/
theorem int_card_oddMultiplesInSquare {d : Nat} (n : Nat) (hd : d % 2 = 1) :
    ((oddMultiplesInSquare n d).card : Int) =
      (((n * n + 2 * n) / d + 1) / 2 : Nat) - ((n * n / d + 1) / 2 : Nat) := by
  have h := card_oddMultiplesInSquare n hd
  have hz : ((oddMultiplesInSquare n d).card : Int) +
      ((n * n / d + 1) / 2 : Nat) = (((n * n + 2 * n) / d + 1) / 2 : Nat) := by
    exact_mod_cast h
  omega

/-- An even multiple of the divisor shifts the odd-multiple floor by the exact integer amount. -/
theorem odd_multiple_floor_shift {d : Nat} (X t : Nat) (hd : 0 < d) :
    ((X + d * (2 * t)) / d + 1) / 2 = (X / d + 1) / 2 + t := by
  rw [Nat.add_mul_div_left X (2 * t) hd]
  omega

/-- Exact affine periodicity in the square-interval index, for every odd divisor. -/
theorem card_oddMultiplesInSquare_shift {d : Nat} (n k : Nat) (hd : d % 2 = 1) :
    (oddMultiplesInSquare (n + 2 * d * k) d).card =
      (oddMultiplesInSquare n d).card + 2 * k := by
  have hd0 : 0 < d := by omega
  let t := 2 * n * k + 2 * d * k * k
  have hA : (n + 2 * d * k) * (n + 2 * d * k) = n * n + d * (2 * t) := by
    dsimp [t]
    nlinarith
  have hU : (n + 2 * d * k) * (n + 2 * d * k) + 2 * (n + 2 * d * k) =
      n * n + 2 * n + d * (2 * (t + 2 * k)) := by
    dsimp [t]
    nlinarith
  have hbase := card_oddMultiplesInSquare n hd
  have hshift := card_oddMultiplesInSquare (n + 2 * d * k) hd
  rw [hU, hA, odd_multiple_floor_shift _ _ hd0, odd_multiple_floor_shift _ _ hd0] at hshift
  omega

/-- Products of odd moduli remain odd, including the empty product. -/
theorem prod_odd_mod_two {s : Finset Nat}
    (hs : forall r, Membership.mem s r -> r % 2 = 1) :
    (Finset.prod s (fun r => r)) % 2 = 1 := by
  apply Finset.prod_induction (fun r => r) (fun x : Nat => x % 2 = 1)
  next => intro a b ha hb; rw [Nat.mul_mod, ha, hb]
  next => decide
  next => exact hs

/-- Every actual odd-prime owner count is a complete signed sum of explicit endpoint floors. -/
theorem card_ownerInSquare_eq_signed_floors {n p : Nat}
    (hp : Nat.Prime p) (hp3 : 3 <= p) :
    (((Nat.PrimeSieve.leastPrimeOwnerPacketAt p (n * n + 2 * n)).filter
      (fun m => n * n < m)).card : Int) =
      Finset.sum (oddEarlierPrimes p).powerset (fun t =>
        (-1 : Int) ^ t.card *
          ((((n * n + 2 * n) / (p * Finset.prod t (fun r => r)) + 1) / 2 : Nat) -
            ((n * n / (p * Finset.prod t (fun r => r)) + 1) / 2 : Nat))) := by
  rw [<- oddSievedOwnerInSquare_eq_owner hp3]
  have hs : forall r, Membership.mem (oddEarlierPrimes p) r ->
      Nat.Prime r /\ r < p := by
    intro r hr
    have hh := Finset.mem_filter.mp hr
    exact And.intro hh.2.1 (Finset.mem_range.mp hh.1)
  rw [card_oddSievedOwnerInSquare n hp hs]
  apply Finset.sum_congr rfl
  intro t ht
  have hodd : (p * Finset.prod t (fun r => r)) % 2 = 1 := by
    have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
    have htodd : (Finset.prod t (fun r => r)) % 2 = 1 := by
      apply prod_odd_mod_two
      intro r hr
      exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp ht) hr)).2.2
    rw [Nat.mul_mod, hpodd, htodd]
  rw [int_card_oddMultiplesInSquare n hodd]

end Nat.PrimeSieve
