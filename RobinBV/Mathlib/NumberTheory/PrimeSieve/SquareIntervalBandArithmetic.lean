/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalPrefixBand

/-!
# Exact arithmetic of the quadratic prefix band

The full signed coefficients reduce to Mobius weights with an exact balanced
pair correction when the product is at most twice the base plus one. These
identities retain actual finite support and assert no unsigned prime supply.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- The Mobius weight of a product of distinct primes is exactly the subset parity sign. -/
theorem moebius_prime_subset_product {s : Finset Nat}
    (hs : forall p, Membership.mem s p -> Nat.Prime p) :
    ArithmeticFunction.moebius (s.prod (fun p => p)) = (-1 : Int)^s.card := by
  have ht : forall p, Membership.mem s p ->
      Membership.mem (s.prod (fun p => p)).primeFactors p := by
    rw [Nat.primeFactors_prod hs]
    exact fun p hp => hp
  rw [ArithmeticFunction.isMultiplicative_moebius.map_prod_of_subset_primeFactors _ s ht]
  have heq : s.prod (fun p => ArithmeticFunction.moebius p) = s.prod (fun _ => (-1 : Int)) := by
    apply Finset.prod_congr rfl
    exact fun p hp => ArithmeticFunction.moebius_apply_prime (hs p hp)
  rw [heq, Finset.prod_const]

/-- Two factors above the square-root cutoff leave no room for a third odd nonunit in the doubled band. -/
theorem two_large_factors_exclude_third_odd {n p q r : Nat}
    (hp : n < p*p) (hq : n < q*q) (hr : 3 <= r)
    (hbound : p*q*r <= 2*n+1) : False := by
  have hpq := index_lt_mul_of_sq_lt hp hq
  have hmul := Nat.mul_le_mul_left (p*q) hr
  nlinarith

/-- An odd prime-subset product in the doubled band containing two large primes consists of exactly that pair. -/
theorem oddPrimeProduct_eq_pair_of_band {n p q : Nat} {s : Finset Nat}
    (hs : forall t, Membership.mem s t -> Nat.Prime t /\ t % 2 = 1)
    (hp : Membership.mem s p) (hq : Membership.mem s q) (hpq : Not (p = q))
    (hpbig : n < p*p) (hqbig : n < q*q)
    (hbound : s.prod (fun t => t) <= 2*n+1) : s = {p, q} := by
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
        have hsub : forall t, Membership.mem ({p, q, r} : Finset Nat) t -> Membership.mem s t := by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with ht | ht | ht <;> subst t <;> assumption
        have hprod := Finset.prod_le_prod_of_subset_of_one_le hsub
          (fun t _ => Nat.zero_le t)
          (fun t ht _ => le_trans (by decide : 1 <= 2) (hs t ht).1.two_le)
        have hpr : Not (p = r) := Ne.symm hrp
        have hqr : Not (q = r) := Ne.symm hrq
        have hsmall : p*q*r <= s.prod (fun t => t) := by
          simpa [Finset.prod_insert, hpq, hpr, hqr, mul_assoc] using hprod
        have hrthree : 3 <= r := by have htwo := (hs r hr).1.two_le; have hodd := (hs r hr).2; omega
        exact False.elim (two_large_factors_exclude_third_odd hpbig hqbig hrthree
          (le_trans hsmall hbound))
  next =>
    intro hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with hr | hr <;> subst r <;> assumption

/-- In the doubled band the full subset coefficient is three times Mobius, minus the balanced-pair correction. -/
theorem squareSubsetWeight_band_moebius {n : Nat} {u v : Finset Nat}
    (hu : forall p, Membership.mem u p -> Nat.Prime p /\ p % 2 = 1)
    (hv : forall p, Membership.mem v p -> Nat.Prime p /\ p % 2 = 1 /\ n < p*p)
    (huv : Disjoint u v)
    (hbound : (Union.union u v).prod (fun p => p) <= 2*n+1) :
    squareSubsetWeight u v =
      3 * ArithmeticFunction.moebius ((Union.union u v).prod (fun p => p)) -
        (if v.card = 2 then 1 else 0) := by
  have hs : forall p, Membership.mem (Union.union u v) p -> Nat.Prime p /\ p % 2 = 1 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    next => exact hu p hp
    next => exact And.intro (hv p hp).1 (hv p hp).2.1
  have hmu := moebius_prime_subset_product (fun p hp => (hs p hp).1)
  rw [Finset.card_union_of_disjoint huv] at hmu
  by_cases hvc : v.card <= 1
  next =>
    have hcases : v.card = 0 \/ v.card = 1 := by omega
    rcases hcases with h | h <;> simp [squareSubsetWeight, hmu, h, pow_add] <;> ring
  next =>
    choose p hp q hq hpq using Finset.one_lt_card.mp (show 1 < v.card by omega)
    have hset := oddPrimeProduct_eq_pair_of_band hs
      (Finset.mem_union_right u hp) (Finset.mem_union_right u hq) hpq
      (hv p hp).2.2 (hv q hq).2.2 hbound
    have hvset : v = {p,q} := by
      ext r
      constructor
      next => intro hr; rw [<- hset]; exact Finset.mem_union_right u hr
      next =>
        intro hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with hr | hr <;> subst r <;> assumption
    have huset : u = {} := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hrs : Membership.mem (Union.union u v) r := Finset.mem_union_left v hr
      rw [hset, <- hvset] at hrs
      exact Finset.disjoint_left.mp huv hr hrs
    have hvc2 : v.card = 2 := by rw [hvset]; simp [hpq]
    rw [hmu]
    simp [squareSubsetWeight, huset, hvc2]

/-- The actual supported coefficient has an exact Mobius and balanced-pair decomposition. -/
theorem squareModulusCoefficient_band_moebius {n d : Nat} {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1 /\ n < p*p)
    (hab : Disjoint a b) (hd : Membership.mem (squareModulusSupport a b) d)
    (hbound : d <= 2*n+1) :
    squareModulusCoefficient a b d = 3*ArithmeticFunction.moebius d -
      (if (Inter.inter d.primeFactors b).card = 2 then 1 else 0) := by
  choose x hx using Finset.mem_image.mp hd
  have hu := Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).1
  have hv := Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).2
  have huv : Disjoint x.1 x.2 := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact Finset.disjoint_left.mp hab (hu hp) (hv hq)
  have hs : forall p, Membership.mem (Union.union x.1 x.2) p -> Nat.Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    next => exact (ha p (hu hp)).1
    next => exact (hb p (hv hp)).1
  rw [<- hx.2, squareModulusCoefficient_prod
    (fun p hp => (ha p hp).1) (fun p hp => (hb p hp).1) hab
    (fun p hp => hu hp) (fun p hp => hv hp), Nat.primeFactors_prod hs,
    (disjoint_subsets_union_inter hab (fun p hp => hu hp) (fun p hp => hv hp)).2]
  exact squareSubsetWeight_band_moebius (fun p hp => ha p (hu hp))
    (fun p hp => hb p (hv hp)) huv (by rw [hx.2]; exact hbound)

/-- Every supported prime-subset modulus is squarefree. -/
theorem squareModulusSupport_squarefree {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p)
    {d : Nat} (hd : Membership.mem (squareModulusSupport a b) d) : Squarefree d := by
  choose x hx using Finset.mem_image.mp hd
  have hs : forall p, Membership.mem (Union.union x.1 x.2) p -> Nat.Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    next => exact ha p ((Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).1) hp)
    next => exact hb p ((Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).2) hp)
  apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
  rw [<- hx.2, moebius_prime_subset_product hs]
  exact pow_ne_zero _ (by norm_num)

/-- A squarefree integer with all prime factors in the two clocks belongs to their product support. -/
theorem squareModulusSupport_of_squarefree {a b : Finset Nat} {d : Nat}
    (hd : Squarefree d)
    (hf : forall p, Membership.mem d.primeFactors p -> Membership.mem (Union.union a b) p) :
    Membership.mem (squareModulusSupport a b) d := by
  let u := Inter.inter d.primeFactors a
  let v := Inter.inter d.primeFactors b
  have hu : forall p, Membership.mem u p -> Membership.mem a p := fun p hp => (Finset.mem_inter.mp hp).2
  have hv : forall p, Membership.mem v p -> Membership.mem b p := fun p hp => (Finset.mem_inter.mp hp).2
  have heq : Union.union u v = d.primeFactors := by
    ext p
    simp only [Finset.mem_union, Finset.mem_inter, u, v]
    constructor
    next => intro hp; exact Or.elim hp And.left And.left
    next =>
      intro hp
      rcases Finset.mem_union.mp (hf p hp) with hpa | hpb
      next => exact Or.inl (And.intro hp hpa)
      next => exact Or.inr (And.intro hp hpb)
  apply Finset.mem_image.mpr
  refine Exists.intro (Prod.mk u v) (And.intro ?_ ?_)
  next => exact Finset.mem_product.mpr (And.intro
    (Finset.mem_powerset.mpr (fun p hp => hu p hp))
    (Finset.mem_powerset.mpr (fun p hp => hv p hp)))
  next => change (Union.union u v).prod (fun p => p) = d
          rw [heq, Nat.prod_primeFactors_of_squarefree hd]

/-- Every prime divisor of an odd composite at most twice the index plus one is at most the index. -/
theorem odd_composite_prime_divisor_le_half_band {n d p : Nat}
    (hodd : d % 2 = 1) (hcomp : Not (Nat.Prime d))
    (hp : Nat.Prime p) (hpd : Dvd.dvd p d) (hbound : d <= 2*n+1) : p <= n := by
  choose r hr using hpd
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with he | he
    next => rw [he] at hr; have hmod := congrArg (fun t : Nat => t % 2) hr; simp at hmod; omega
    next => exact he
  have hrodd : r % 2 = 1 := by
    have hmod := congrArg (fun t : Nat => t % 2) hr
    rw [Nat.mul_mod, hpodd] at hmod
    simpa [hodd] using hmod.symm
  have hrne : Not (r = 1) := by
    intro he
    rw [he, Nat.mul_one] at hr
    apply hcomp
    rw [hr]
    exact hp
  have hrthree : 3 <= r := by omega
  have hmul := Nat.mul_le_mul_left p hrthree
  nlinarith

/-- A prime that occurs as a supported product already belongs to one of the clocks. -/
theorem prime_mem_clock_of_mem_squareModulusSupport {a b : Finset Nat} {d : Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p)
    (hd : Nat.Prime d) (hm : Membership.mem (squareModulusSupport a b) d) :
    Membership.mem (Union.union a b) d := by
  choose x hx using Finset.mem_image.mp hm
  have hu := Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).1
  have hv := Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).2
  have hs : forall p, Membership.mem (Union.union x.1 x.2) p -> Nat.Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    next => exact ha p (hu hp)
    next => exact hb p (hv hp)
  have hself : Membership.mem d.primeFactors d :=
    Nat.mem_primeFactors.mpr (And.intro hd (And.intro (dvd_refl d) hd.ne_zero))
  rw [<- hx.2, Nat.primeFactors_prod hs] at hself
  rw [hx.2] at hself
  rcases Finset.mem_union.mp hself with h | h
  next => exact Finset.mem_union_left b (hu h)
  next => exact Finset.mem_union_right a (hv h)

/-- An odd integer in the doubled band above the clocks is supported exactly when it is a squarefree composite. -/
theorem squareClock_band_support_iff {n d : Nat}
    (hodd : d % 2 = 1) (hlo : n+1 < d) (hhi : d <= 2*n+1) :
    Membership.mem (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d <->
      Squarefree d /\ Not (Nat.Prime d) := by
  have ha : forall p, Membership.mem (squareSmallOddPrimes n) p -> Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1
  have hb : forall p, Membership.mem (squareMediumOddPrimes n) p -> Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1
  constructor
  next =>
    intro hm
    refine And.intro (squareModulusSupport_squarefree ha hb hm) ?_
    intro hprime
    have hclock := prime_mem_clock_of_mem_squareModulusSupport ha hb hprime hm
    rcases Finset.mem_union.mp hclock with h | h
    all_goals have hr := Finset.mem_range.mp (Finset.mem_filter.mp h).1; omega
  next =>
    intro hd
    apply squareModulusSupport_of_squarefree hd.1
    intro p hp
    have hpf := Nat.mem_primeFactors.mp hp
    have hple := odd_composite_prime_divisor_le_half_band hodd hd.2 hpf.1 hpf.2.1 hhi
    have hpodd : p % 2 = 1 := by
      rcases hpf.1.eq_two_or_odd with htwo | ho
      next =>
        have hdiv := hpf.2.1
        rw [htwo] at hdiv
        have hz := Nat.mod_eq_zero_of_dvd hdiv
        omega
      next => exact ho
    by_cases hsq : p*p <= n
    next =>
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
        (And.intro hpf.1 (And.intro hpodd hsq)))
    next =>
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
        (And.intro hpf.1 (And.intro hpodd (show n < p*p by omega))))

/-- The actual modulus coefficient extended by zero outside its full finite support. -/
noncomputable def squareSupportedCoefficient (a b : Finset Nat) (d : Nat) : Int :=
  if Membership.mem (squareModulusSupport a b) d then squareModulusCoefficient a b d else 0

/-- The zero-extended actual band coefficient is exactly Mobius, prime compensation, and supported-pair correction. -/
theorem squareSupportedCoefficient_band_identity {n d : Nat}
    (hodd : d % 2 = 1) (hlo : n+1 < d) (hhi : d <= 2*n+1) :
    let a := squareSmallOddPrimes n
    let b := squareMediumOddPrimes n
    squareSupportedCoefficient a b d =
      3*ArithmeticFunction.moebius d + 3*(if Nat.Prime d then 1 else 0) -
        (if Membership.mem (squareModulusSupport a b) d /\
          (Inter.inter d.primeFactors b).card = 2 then 1 else 0) := by
  let a := squareSmallOddPrimes n
  let b := squareMediumOddPrimes n
  have ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1 := by
    intro p hp
    have h := (Finset.mem_filter.mp hp).2
    exact And.intro h.1 h.2.1
  have hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1 /\ n < p*p :=
    fun p hp => (Finset.mem_filter.mp hp).2
  have hab : Disjoint a b := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hsmall := (Finset.mem_filter.mp hp).2.2.2
    have hbig := (hb p hq).2.2
    omega
  have hiff := squareClock_band_support_iff hodd hlo hhi
  change squareSupportedCoefficient a b d =
    3*ArithmeticFunction.moebius d + 3*(if Nat.Prime d then 1 else 0) -
      (if Membership.mem (squareModulusSupport a b) d /\
        (Inter.inter d.primeFactors b).card = 2 then 1 else 0)
  by_cases hm : Membership.mem (squareModulusSupport a b) d
  next =>
    have hcomp := (hiff.mp hm).2
    have he := squareModulusCoefficient_band_moebius ha hb hab hm hhi
    simp only [squareSupportedCoefficient, hm, if_true, true_and, hcomp, if_false, mul_zero, add_zero]
    exact he
  next =>
    have hmu : 3*ArithmeticFunction.moebius d + 3*(if Nat.Prime d then (1 : Int) else 0) = 0 := by
      by_cases hp : Nat.Prime d
      next => simp [ArithmeticFunction.moebius_apply_prime hp, hp]
      next =>
        have hns : Not (Squarefree d) := by
          intro hs
          exact hm (hiff.mpr (And.intro hs hp))
        simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns, hp]
    simp only [squareSupportedCoefficient, hm, if_false, false_and, hmu, sub_zero]

/-- Summing the zero extension is exactly summing the coefficient over the retained support. -/
theorem sum_squareSupportedCoefficient (a b s : Finset Nat) :
    s.sum (squareSupportedCoefficient a b) =
      (s.filter (fun d => Membership.mem (squareModulusSupport a b) d)).sum
        (squareModulusCoefficient a b) := by
  rw [Finset.sum_filter]
  rfl

/-- Any finite odd doubled-band domain has an exact Mobius, prime-count, and supported-pair identity. -/
theorem sum_squareSupportedCoefficient_band {n : Nat} (s : Finset Nat)
    (hs : forall d, Membership.mem s d -> d % 2 = 1 /\ n+1 < d /\ d <= 2*n+1) :
    let a := squareSmallOddPrimes n
    let b := squareMediumOddPrimes n
    s.sum (squareSupportedCoefficient a b) =
      3*s.sum ArithmeticFunction.moebius + 3*((s.filter Nat.Prime).card : Int) -
        ((s.filter (fun d => Membership.mem (squareModulusSupport a b) d /\
          (Inter.inter d.primeFactors b).card = 2)).card : Int) := by
  let a := squareSmallOddPrimes n
  let b := squareMediumOddPrimes n
  have he : s.sum (squareSupportedCoefficient a b) =
      s.sum (fun d => 3*ArithmeticFunction.moebius d + 3*(if Nat.Prime d then 1 else 0) -
        (if Membership.mem (squareModulusSupport a b) d /\
          (Inter.inter d.primeFactors b).card = 2 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact squareSupportedCoefficient_band_identity (hs d hd).1 (hs d hd).2.1 (hs d hd).2.2
  dsimp only
  rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    <- Finset.mul_sum, <- Finset.mul_sum, Finset.sum_boole, Finset.sum_boole]

/-- The geometric fixed-band core equals its explicit arithmetic decomposition with no omitted integer. -/
theorem squareFixedBand_core_eq_arithmetic {n J : Nat} (hcut : 4*J <= n) :
    let a := squareSmallOddPrimes n
    let b := squareMediumOddPrimes n
    let s := (squareModulusSupport a b).filter (fun d => n+1 < d)
    let t := (Finset.Icc (n+2) (quadraticPrefixBandEnd n J)).filter (fun d => d % 2 = 1)
    (s.filter (fun d => d <= quadraticPrefixBandEnd n J)).sum (squareModulusCoefficient a b) =
      3*t.sum ArithmeticFunction.moebius + 3*((t.filter Nat.Prime).card : Int) -
        ((t.filter (fun d => Membership.mem (squareModulusSupport a b) d /\
          (Inter.inter d.primeFactors b).card = 2)).card : Int) := by
  let a := squareSmallOddPrimes n
  let b := squareMediumOddPrimes n
  let s := (squareModulusSupport a b).filter (fun d => n+1 < d)
  let t := (Finset.Icc (n+2) (quadraticPrefixBandEnd n J)).filter (fun d => d % 2 = 1)
  have he : s.filter (fun d => d <= quadraticPrefixBandEnd n J) =
      t.filter (fun d => Membership.mem (squareModulusSupport a b) d) := by
    ext d
    dsimp only [s, t]
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    next =>
      intro h
      have hodd := squareModulusSupport_odd
        (fun p hp => (Finset.mem_filter.mp hp).2.2.1)
        (fun p hp => (Finset.mem_filter.mp hp).2.2.1) h.1.1
      exact And.intro (And.intro (And.intro (by omega) h.2) hodd) h.1.1
    next =>
      intro h
      exact And.intro (And.intro h.2 (by omega)) h.1.1.2
  have ht : forall d, Membership.mem t d -> d % 2 = 1 /\ n+1 < d /\ d <= 2*n+1 := by
    intro d hd
    have hm := Finset.mem_filter.mp hd
    have hi := Finset.mem_Icc.mp hm.1
    have hbnd := quadraticPrefixBandEnd_le_twice hcut
    exact And.intro hm.2 (And.intro (by omega) (by omega))
  change (s.filter (fun d => d <= quadraticPrefixBandEnd n J)).sum (squareModulusCoefficient a b) = _
  rw [he, <- sum_squareSupportedCoefficient]
  exact sum_squareSupportedCoefficient_band t ht

/-- The complete joint packet has the arithmetic band lower comparison, retaining every outside-prefix contribution. -/
theorem squareJointPacket_arithmeticBand_lower {n J : Nat}
    (hJ : 1 <= J) (hcut : 4*J <= n) :
    let a := squareSmallOddPrimes n
    let b := squareMediumOddPrimes n
    let s := (squareModulusSupport a b).filter (fun d => n+1 < d)
    let p := quadraticLayerUnionPrefix n J s
    let t := (Finset.Icc (n+2) (quadraticPrefixBandEnd n J)).filter (fun d => d % 2 = 1)
    3*t.sum ArithmeticFunction.moebius + 3*((t.filter Nat.Prime).card : Int) -
      ((t.filter (fun d => Membership.mem (squareModulusSupport a b) d /\
        (Inter.inter d.primeFactors b).card = 2)).card : Int) - (9*(J : Int)+3) +
      ((squareModulusSupport a b).filter (fun d => Not (Membership.mem p d))).sum
        (fun d => squareModulusCoefficient a b d *
          (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)) <=
      2 * squareJointPacket (n+1) a b - squareJointPacket n a b := by
  have ha : forall q, Membership.mem (squareSmallOddPrimes n) q -> Nat.Prime q /\ q % 2 = 1 := by
    intro q hq
    have h := (Finset.mem_filter.mp hq).2
    exact And.intro h.1 h.2.1
  have hb : forall q, Membership.mem (squareMediumOddPrimes n) q -> Nat.Prime q /\ q % 2 = 1 := by
    intro q hq
    have h := (Finset.mem_filter.mp hq).2
    exact And.intro h.1 h.2.1
  have hab : Disjoint (squareSmallOddPrimes n) (squareMediumOddPrimes n) := by
    apply Finset.disjoint_left.mpr
    intro q hq hr
    have hsmall := (Finset.mem_filter.mp hq).2.2.2
    have hbig := (Finset.mem_filter.mp hr).2.2.2
    omega
  have hlo := squareJointPacket_fixedBand_lower hJ hcut ha hb hab
  have he := squareFixedBand_core_eq_arithmetic hcut
  dsimp only at hlo he
  dsimp only
  rw [he] at hlo
  exact hlo

end Nat.PrimeSieve
