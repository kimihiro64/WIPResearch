/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalDensity
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalGapCells
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalSuccessor

/-!
# Exact joint centering and complementary-factor switch

The complete signed two-interval packet is decomposed into its proved
positive reciprocal coefficient and the actual centered remainder. Large
moduli are switched exactly to cofactors at most the successor index, with
both quadratic windows and all signed weights retained. No lower bound for
the joint remainder or proof of Legendre's conjecture is assumed.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- Every signed centered modulus term, including moduli with zero actual count. -/
noncomputable def squareCenteredIncidence (x : Nat) (a b : Finset Nat) (k : Nat) : Real :=
  a.powerset.sum (fun u => (-1 : Real)^u.card *
    (b.powersetCard k).sum (fun v =>
      (oddSquareFloor x ((Union.union u v).prod (fun p => p)) : Real) -
        (x : Real) / (((Union.union u v).prod (fun p => p) : Nat) : Real)))

/-- The complete incidence-floor packet with its prime sets held fixed. -/
noncomputable def squareFrozenFloorIncidence (x : Nat) (a b : Finset Nat) (k : Nat) : Int :=
  a.powerset.sum (fun u => (-1 : Int)^u.card *
    (b.powersetCard k).sum (fun v =>
      oddSquareFloor x ((Union.union u v).prod (fun p => p))))

/-- Exact coefficient and secondary term for the entire incidence packet. -/
theorem squareFrozenFloorIncidence_centered (x : Nat) (a b : Finset Nat) (k : Nat) :
    (squareFrozenFloorIncidence x a b k : Real) =
      (x : Real) * squareReciprocalIncidence a b k + squareCenteredIncidence x a b k := by
  unfold squareFrozenFloorIncidence squareReciprocalIncidence squareCenteredIncidence
  push_cast
  rw [Finset.mul_sum, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  simp_rw [div_eq_mul_inv, Finset.sum_sub_distrib, <- Finset.mul_sum]
  ring

/-- The finite-sieve joint packet equals all three complete frozen floor expansions. -/
theorem squareJointPacket_eq_frozenFloors (x : Nat) {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1) :
    squareJointPacket x a b =
      3 * squareFrozenFloorIncidence x a b 0 - 3 * squareFrozenFloorIncidence x a b 1 +
        2 * squareFrozenFloorIncidence x a b 2 := by
  have hinc (k : Nat) :
      ((oddMultiplesInSquare x 1).filter (fun m =>
        forall p, Membership.mem a p -> Not (Dvd.dvd p m))).sum
          (fun m => (Nat.choose ((b.filter (fun q => Dvd.dvd q m)).card) k : Int)) =
            squareFrozenFloorIncidence x a b k := by
    rw [sieved_incidence_eq_signed_subset_counts
      (fun p hp => (ha p hp).1) (fun p hp => (hb p hp).1)]
    apply Finset.sum_congr rfl
    intro u hu
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [oddMultiplesInSquare_one_filter]
    have hodd : ((Union.union u v).prod (fun p => p)) % 2 = 1 := by
      apply prod_odd_mod_two
      intro p hp
      rcases Finset.mem_union.mp hp with hpu | hpv
      next => exact (ha p ((Finset.mem_powerset.mp hu) hpu)).2
      next => exact (hb p ((Finset.mem_powersetCard.mp hv).1 hpv)).2
    exact int_card_oddMultiplesInSquare x hodd
  have h0 := hinc 0
  have h1 := hinc 1
  have h2 := hinc 2
  simp only [Nat.choose_zero_right, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one] at h0
  simp only [Nat.choose_one_right] at h1
  unfold squareJointPacket
  simp only [jointIncidenceWeight, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    <- Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2]
  nlinarith only [h0]

/-- The complete three-incidence centered remainder, with no assumed sign. -/
noncomputable def squareJointCentered (x : Nat) (a b : Finset Nat) : Real :=
  3 * squareCenteredIncidence x a b 0 - 3 * squareCenteredIncidence x a b 1 +
    2 * squareCenteredIncidence x a b 2

/-- Exact centering of the actual joint packet for arbitrary odd-prime clock sets. -/
theorem squareJointPacket_centered (x : Nat) {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1) :
    (squareJointPacket x a b : Real) =
      (x : Real) * (3 * squareReciprocalIncidence a b 0 -
        3 * squareReciprocalIncidence a b 1 + 2 * squareReciprocalIncidence a b 2) +
      squareJointCentered x a b := by
  rw [squareJointPacket_eq_frozenFloors x ha hb]
  push_cast
  rw [squareFrozenFloorIncidence_centered, squareFrozenFloorIncidence_centered,
    squareFrozenFloorIncidence_centered]
  unfold squareJointCentered
  ring

/-- The coupled two-interval identity with the exact coefficient n+2. -/
theorem squareJointPacket_paired_centered (n : Nat) :
    2 * (squareJointPacket (n+1) (squareSmallOddPrimes n) (squareMediumOddPrimes n) : Real) -
      (squareJointPacket n (squareSmallOddPrimes n) (squareMediumOddPrimes n) : Real) =
      ((n : Real) + 2) * squareJointDensity n +
        (2 * squareJointCentered (n+1) (squareSmallOddPrimes n) (squareMediumOddPrimes n) -
          squareJointCentered n (squareSmallOddPrimes n) (squareMediumOddPrimes n)) := by
  have ha : forall p, Membership.mem (squareSmallOddPrimes n) p -> Nat.Prime p /\ p % 2 = 1 :=
    fun p hp => And.intro (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2.1
  have hb : forall p, Membership.mem (squareMediumOddPrimes n) p -> Nat.Prime p /\ p % 2 = 1 :=
    fun p hp => And.intro (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2.1
  rw [squareJointPacket_centered (n+1) ha hb, squareJointPacket_centered n ha hb]
  unfold squareJointDensity
  push_cast
  ring

/-- Above the successor diagonal, every live cofactor is at most the successor. -/
theorem large_divisor_cofactor_bound {n x d r : Nat} (hx : x <= n+1)
    (hd : n+1 < d) (hprod : d*r <= x*x+2*x) : r <= n+1 := by
  by_contra hr
  have hrge : n+2 <= r := by omega
  have hdge : n+2 <= d := by omega
  have hmul := Nat.mul_le_mul hdge hrge
  nlinarith

/-- Exact finite parametrization after the complementary-factor switch. -/
theorem oddMultiplesInSquare_large_divisor_image {n x d : Nat}
    (hx : x <= n+1) (hd : n+1 < d) (hodd : d % 2 = 1) :
    oddMultiplesInSquare x d =
      ((Finset.range (n+2)).filter (fun r =>
        r % 2 = 1 /\ x*x < d*r /\ d*r <= x*x+2*x)).image (fun r => d*r) := by
  ext m
  simp only [oddMultiplesInSquare, oddMultiplesUpTo, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  constructor
  next =>
    intro hm
    choose r he using hm.1.2.2
    have hprod : d*r <= x*x+2*x := by omega
    have hrbound := large_divisor_cofactor_bound hx hd hprod
    have hrOdd : r % 2 = 1 := by
      have h := hm.1.2.1
      rw [he, Nat.mul_mod, hodd] at h
      simpa using h
    exact Exists.intro r (And.intro (And.intro (by omega)
      (And.intro hrOdd (And.intro (by omega) hprod))) he.symm)
  next =>
    intro hm
    choose r hr using hm
    have hmOdd : m % 2 = 1 := by
      rw [<- hr.2, Nat.mul_mod, hodd, hr.1.2.1]
    have hdvd : Dvd.dvd d m := Exists.intro r hr.2.symm
    exact And.intro (And.intro (by omega) (And.intro hmOdd hdvd)) (by omega)

/-- Every large-modulus floor is an exact finite sum over the short cofactors. -/
theorem oddSquareFloor_large_divisor (n : Nat) {x d : Nat}
    (hx : x <= n+1) (hd : n+1 < d) (hodd : d % 2 = 1) :
    oddSquareFloor x d =
      (Finset.range (n+2)).sum (fun r =>
        if r % 2 = 1 /\ x*x < d*r /\ d*r <= x*x+2*x then (1 : Int) else 0) := by
  rw [oddSquareFloor, <- int_card_oddMultiplesInSquare x hodd]
  rw [oddMultiplesInSquare_large_divisor_image hx hd hodd]
  have hinj : Function.Injective (fun r : Nat => d*r) := by
    intro r s he
    exact Nat.eq_of_mul_eq_mul_left (by omega) he
  rw [Finset.card_image_of_injective _ hinj, Finset.sum_boole]

/-- The signed pair of quadratic cofactor windows; parity and endpoints are retained. -/
def squarePairedCofactorKernel (n d r : Nat) : Int :=
  2 * (if r % 2 = 1 /\ (n+1)*(n+1) < d*r /\
    d*r <= (n+1)*(n+1)+2*(n+1) then 1 else 0) -
    (if r % 2 = 1 /\ n*n < d*r /\ d*r <= n*n+2*n then 1 else 0)

/-- The whole large-modulus signed packet switches to the same cofactor domain. -/
theorem sum_large_modulus_joint_switch (n : Nat) (s : Finset Nat) (c : Nat -> Int)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1) :
    s.sum (fun d => c d * (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)) =
      (Finset.range (n+2)).sum (fun r => s.sum (fun d => c d * squarePairedCofactorKernel n d r)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [oddSquareFloor_large_divisor n (by omega) (hs d hd).1 (hs d hd).2,
    oddSquareFloor_large_divisor n (by omega) (hs d hd).1 (hs d hd).2]
  simp only [squarePairedCofactorKernel, Finset.mul_sum, <- Finset.sum_sub_distrib]

/-- An elementary positive coefficient bound at every actual square-root cutoff. -/
theorem squareJointDensity_sqrt_lower {n : Nat} (hn : 2 <= n) :
    1 / (2 * (n.sqrt : Real)) < squareJointDensity n := by
  have hr : 1 <= n.sqrt := Nat.le_sqrt.mpr (by omega)
  have he : n.sqrt - 1 + 1 = n.sqrt := by omega
  have hprod := finite_reciprocal_product_lower (N := n.sqrt - 1)
    (a := squareSmallOddPrimes n) (by
      intro p hp
      have h := (Finset.mem_filter.mp hp).2
      refine And.intro h.1.two_le ?_
      rw [he]
      exact Nat.le_sqrt.mpr h.2.2)
  have heR : ((n.sqrt - 1 : Nat) : Real) + 1 = (n.sqrt : Real) := by exact_mod_cast he
  rw [heR] at hprod
  calc
    1 / (2 * (n.sqrt : Real)) = (1 / (n.sqrt : Real)) / 2 := by ring
    _ <= (squareSmallOddPrimes n).prod (fun p => 1 - 1 / (p : Real)) / 2 :=
      _root_.div_le_div_of_nonneg_right hprod (by norm_num)
    _ < squareJointDensity n := squareJointDensity_lower n

/-- Every nonzero paired-kernel cell retains oddness and the common quadratic window. -/
theorem squarePairedCofactorKernel_geometry {n d r : Nat}
    (hk : Not (squarePairedCofactorKernel n d r = 0)) :
    r % 2 = 1 /\ n*n < d*r /\ d*r < (n+2)*(n+2) := by
  by_cases hnew : r % 2 = 1 /\ (n+1)*(n+1) < d*r /\
      d*r <= (n+1)*(n+1)+2*(n+1)
  next => exact And.intro hnew.1 (And.intro (by nlinarith [hnew.2.1])
    (by nlinarith [hnew.2.2]))
  next =>
    have hold : r % 2 = 1 /\ n*n < d*r /\ d*r <= n*n+2*n := by
      by_contra hnold
      apply hk
      simp [squarePairedCofactorKernel, hnew, hnold]
    exact And.intro hold.1 (And.intro hold.2.1 (by nlinarith [hold.2.2]))

/-- All live large-modulus cells within a half-gap cutoff, shared by the two intervals. -/
noncomputable def nearGapCofactorCells (n K : Nat) (s : Finset Nat) : Finset (Prod Nat Nat) :=
  ((Finset.range (n+2)).product s).filter (fun x =>
    (x.2-x.1)/2 <= K /\ Not (squarePairedCofactorKernel n x.2 x.1 = 0))

/-- Exact positivity, parity and square-window data for each selected joint cell. -/
theorem nearGapCofactorCells_data {n K : Nat} {s : Finset Nat}
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    {x : Prod Nat Nat} (hx : Membership.mem (nearGapCofactorCells n K s) x) :
    Membership.mem s x.2 /\ x.1 % 2 = 1 /\
      x.2 = x.1 + 2*((x.2-x.1)/2) /\
      1 <= (x.2-x.1)/2 /\ (x.2-x.1)/2 <= K /\
      n*n < x.2*x.1 /\ x.2*x.1 < (n+2)*(n+2) := by
  have hm := Finset.mem_filter.mp hx
  have hpair := Finset.mem_product.mp hm.1
  have hrange := Finset.mem_range.mp hpair.1
  have hd := hs x.2 hpair.2
  have hgeom := squarePairedCofactorKernel_geometry hm.2.2
  exact And.intro hpair.2 (And.intro hgeom.1 (And.intro (by omega)
    (And.intro (by omega) (And.intro hm.2.1 hgeom.2))))

/-- The two adjacent intervals cannot spend the same half-gap capacity twice. -/
theorem nearGapCofactorCells_halfGap_injOn (n K : Nat) {s : Finset Nat}
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1) :
    Set.InjOn (fun x : Prod Nat Nat => (x.2-x.1)/2) (nearGapCofactorCells n K s) := by
  intro x hx y hy he
  have hxd := nearGapCofactorCells_data hs hx
  have hyd := nearGapCofactorCells_data hs hy
  change (x.2-x.1)/2 = (y.2-y.1)/2 at he
  have hp : x.1 = y.1 := by
    apply odd_factor_left_unique_two_intervals hxd.2.1 hyd.2.1
      (g := 2*((x.2-x.1)/2))
    next => nlinarith [hxd.2.2.1, hxd.2.2.2.2.2.1]
    next => nlinarith [hxd.2.2.1, hxd.2.2.2.2.2.2]
    next => nlinarith [hyd.2.2.1, hyd.2.2.2.2.2.1]
    next => nlinarith [hyd.2.2.1, hyd.2.2.2.2.2.2]
  apply Prod.ext hp
  have hxe := hxd.2.2.1
  have hye := hyd.2.2.1
  omega

/-- A joint half-gap budget bounds the combined cell count, not two separate counts. -/
theorem card_nearGapCofactorCells_le (n K : Nat) {s : Finset Nat}
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1) :
    (nearGapCofactorCells n K s).card <= K := by
  have hcard : (nearGapCofactorCells n K s).card <= (Finset.Icc 1 K).card := by
    apply Finset.card_le_card_of_injOn (fun x : Prod Nat Nat => (x.2-x.1)/2)
    next =>
      intro x hx
      have h := nearGapCofactorCells_data hs hx
      exact Finset.mem_Icc.mpr (And.intro h.2.2.2.1 h.2.2.2.2.1)
    next => exact nearGapCofactorCells_halfGap_injOn n K hs
  simpa using hcard

/-- The actual paired kernel has weights between minus one and two. -/
theorem squarePairedCofactorKernel_bounds (n d r : Nat) :
    (-1 : Int) <= squarePairedCofactorKernel n d r /\
      squarePairedCofactorKernel n d r <= 2 := by
  unfold squarePairedCofactorKernel
  split_ifs <;> norm_num

/-- The actual signed near-gap contribution of the paired cofactor kernel. -/
noncomputable def nearGapJointPacket (n K : Nat) (s : Finset Nat) (c : Nat -> Int) : Int :=
  (nearGapCofactorCells n K s).sum (fun x => c x.2 * squarePairedCofactorKernel n x.2 x.1)

/-- The common gap budget bounds the combined loss for coefficients between minus three and three. -/
theorem nearGapJointPacket_lower (n K : Nat) {s : Finset Nat} (c : Nat -> Int)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hc : forall d, Membership.mem s d -> (-3 : Int) <= c d /\ c d <= 3) :
    -(6 : Int)*(K : Int) <= nearGapJointPacket n K s c := by
  have hsum : -(6 : Int)*((nearGapCofactorCells n K s).card : Int) <=
      nearGapJointPacket n K s c := by
    calc
      _ = (nearGapCofactorCells n K s).sum (fun _ => (-6 : Int)) := by
        simp [Finset.sum_const, mul_comm]
      _ <= _ := by
        apply Finset.sum_le_sum
        intro x hx
        have hc' := hc x.2 (nearGapCofactorCells_data hs hx).1
        have hk := squarePairedCofactorKernel_bounds n x.2 x.1
        by_cases hpos : 0 <= c x.2
        next =>
          have hprod := _root_.mul_le_mul_of_nonneg_left hk.1 hpos
          nlinarith
        next =>
          have hneg : c x.2 <= 0 := by omega
          have hprod := _root_.mul_le_mul_of_nonpos_left hk.2 hneg
          nlinarith
  have hcard : ((nearGapCofactorCells n K s).card : Int) <= K := by
    exact_mod_cast card_nearGapCofactorCells_le n K hs
  nlinarith

/-- A live odd cofactor above the diagonal makes the complete odd-multiple floor exactly one. -/
theorem oddSquareFloor_eq_one_of_odd_cofactor {n d r : Nat}
    (hd : n < d) (hdodd : d % 2 = 1) (hr : r % 2 = 1)
    (hlo : n*n < d*r) (hhi : d*r < (n+1)*(n+1)) : oddSquareFloor n d = 1 := by
  have hd0 : 0 < d := by omega
  have hrformula := odd_cofactor_eq_floor hd hr hlo hhi
  have hhi' : d*r <= n*n+2*n := by nlinarith
  have hle : r <= (n*n+2*n)/d := (Nat.le_div_iff_mul_le hd0).mpr
    (by simpa only [Nat.mul_comm] using hhi')
  have hlt : (n*n+2*n)/d < r+2 := (Nat.div_lt_iff_lt_mul hd0).mpr (by nlinarith)
  have hcount := card_oddMultiplesInSquare n hdodd
  have hcard : (oddMultiplesInSquare n d).card = 1 := by omega
  rw [oddSquareFloor, <- int_card_oddMultiplesInSquare n hdodd, hcard]
  rfl

/-- Every admissible odd divisor in the first quadratic layer occurs once in the old interval. -/
theorem first_quadratic_layer_old_floor {n k : Nat} (_hn : 2 <= n)
    (hk : 1 <= k) (hksq : k*k <= 2*n) (hodd : (n+1+k) % 2 = 1) :
    oddSquareFloor n (n+1+k) = 1 := by
  have hkn : k <= n := by
    by_contra h
    have hge : n+1 <= k := by omega
    have hsq := Nat.mul_le_mul hge hge
    nlinarith
  let r := n+1-k
  have hr : r+k = n+1 := by dsimp [r]; omega
  have hro : r % 2 = 1 := by omega
  have hprod : (n+1+k)*r+k*k = (n+1)*(n+1) := by nlinarith
  apply oddSquareFloor_eq_one_of_odd_cofactor (r := r) (by omega) hodd hro
  next => nlinarith
  next => nlinarith

/-- The exceptional divisor at the next-square boundary has no odd multiple in the new interval. -/
theorem oddSquareFloor_successor_boundary {n : Nat} (hodd : (n+2) % 2 = 1) :
    oddSquareFloor (n+1) (n+2) = 0 := by
  rw [oddSquareFloor_large_divisor n (by omega) (by omega) hodd]
  apply Finset.sum_eq_zero
  intro r hr
  apply if_neg
  intro h
  have hrange := Finset.mem_range.mp hr
  have hrn : r <= n := by omega
  have hmul := Nat.mul_le_mul_left (n+2) hrn
  nlinarith [h.2.1]

/-- Exact same-divisor cancellation in the first quadratic layer, including the exceptional boundary. -/
theorem paired_first_quadratic_layer {n k : Nat} (hn : 2 <= n)
    (hk : 1 <= k) (hksq : k*k <= 2*n) (hodd : (n+1+k) % 2 = 1) :
    2 * oddSquareFloor (n+1) (n+1+k) - oddSquareFloor n (n+1+k) =
      if k = 1 then (-1 : Int) else 1 := by
  rw [first_quadratic_layer_old_floor hn hk hksq hodd]
  by_cases hk1 : k = 1
  next =>
    subst k
    have hdodd : (n+2) % 2 = 1 := by simpa only [Nat.add_assoc] using hodd
    rw [show n+1+1 = n+2 by omega, oddSquareFloor_successor_boundary hdodd]
    norm_num
  next =>
    rw [if_neg hk1]
    have hk2 : 2 <= k := by omega
    have hkn : k <= n := by
      by_contra h
      have hge : n+1 <= k := by omega
      have hsq := Nat.mul_le_mul hge hge
      nlinarith
    let r := n+1-k
    have hr : r+k = n+1 := by dsimp [r]; omega
    have hro : (r+2) % 2 = 1 := by omega
    have hprod : (n+1+k)*r+k*k = (n+1)*(n+1) := by nlinarith
    have htwok : 2*k <= k*k := by nlinarith [Nat.mul_le_mul_left k hk2]
    have hnew : oddSquareFloor (n+1) (n+1+k) = 1 := by
      apply oddSquareFloor_eq_one_of_odd_cofactor (r := r+2) (by omega) hodd hro
      next => nlinarith
      next => nlinarith
    rw [hnew]
    norm_num

end Nat.PrimeSieve
