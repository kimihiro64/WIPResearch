/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalCounts

/-!
# Exact affine periodicity of signed square-interval packets

The complete signed packet shares a common period. Bounds reduce to that
finite domain without replacing correlated terms by separate worst errors.
Fixed-clock periodicity does not by itself bound a cutoff growing with the index.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

/-- Exact raw odd-multiple shift at any common multiple of twice the divisor. -/
theorem raw_odd_count_shift_common {d W : Nat} (n : Nat)
    (hd : d % 2 = 1) (hW : Dvd.dvd (2 * d) W) :
    (oddMultiplesInSquare (n + W) d).card =
      (oddMultiplesInSquare n d).card + W / d := by
  choose k hk using hW
  have hd0 : 0 < d := by omega
  have hdiv : W / d = 2 * k := by
    rw [hk]
    have heq : 2 * d * k = d * (2 * k) := by ac_rfl
    rw [heq, Nat.mul_div_cancel_left _ hd0]
  rw [hk, card_oddMultiplesInSquare_shift n k hd, <- hk, hdiv]

/-- An arbitrary finite signed combination of actual odd-multiple square-interval counts. -/
noncomputable def signedOddSquarePacket {I : Type*} (s : Finset I) (d : I -> Nat)
    (w : I -> Int) (n : Nat) : Int :=
  Finset.sum s (fun i => w i * ((oddMultiplesInSquare n (d i)).card : Int))

/-- The exact packet drift at a specified common period; its sign is not assumed. -/
def signedOddSquareDrift {I : Type*} (s : Finset I) (d : I -> Nat)
    (w : I -> Int) (W : Nat) : Int :=
  Finset.sum s (fun i => w i * (W / d i : Nat))

/-- All signed terms shift together, retaining their actual weights and divisor correlations. -/
theorem signedOddSquarePacket_shift {I : Type*} (s : Finset I) (d : I -> Nat)
    (w : I -> Int) (n W : Nat)
    (hd : forall i, Membership.mem s i -> d i % 2 = 1)
    (hW : forall i, Membership.mem s i -> Dvd.dvd (2 * d i) W) :
    signedOddSquarePacket s d w (n + W) =
      signedOddSquarePacket s d w n + signedOddSquareDrift s d w W := by
  unfold signedOddSquarePacket signedOddSquareDrift
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [raw_odd_count_shift_common n (hd i hi) (hW i hi), Nat.cast_add, mul_add]

/-- Exact integral centering of a whole packet, without an assumed error sign. -/
noncomputable def signedOddSquareCentered {I : Type*} (s : Finset I) (d : I -> Nat)
    (w : I -> Int) (W n : Nat) : Int :=
  (W : Int) * signedOddSquarePacket s d w n - signedOddSquareDrift s d w W * (n : Int)

/-- Exact affine shift through every natural multiple of the common period. -/
theorem signedOddSquarePacket_shift_mul {I : Type*} (s : Finset I) (d : I -> Nat)
    (w : I -> Int) (n k W : Nat)
    (hd : forall i, Membership.mem s i -> d i % 2 = 1)
    (hW : forall i, Membership.mem s i -> Dvd.dvd (2 * d i) W) :
    signedOddSquarePacket s d w (n + k * W) =
      signedOddSquarePacket s d w n + (k : Int) * signedOddSquareDrift s d w W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, <- Nat.add_assoc, signedOddSquarePacket_shift s d w _ W hd hW, ih]
    push_cast
    ring

/-- The centered signed packet is unchanged by any multiple of its common period. -/
theorem signedOddSquareCentered_shift_mul {I : Type*} (s : Finset I) (d : I -> Nat)
    (w : I -> Int) (n k W : Nat)
    (hd : forall i, Membership.mem s i -> d i % 2 = 1)
    (hW : forall i, Membership.mem s i -> Dvd.dvd (2 * d i) W) :
    signedOddSquareCentered s d w W (n + k * W) = signedOddSquareCentered s d w W n := by
  unfold signedOddSquareCentered
  rw [signedOddSquarePacket_shift_mul s d w n k W hd hW]
  push_cast
  ring

/-- Every centered packet value equals its actual residue representative. -/
theorem signedOddSquareCentered_eq_mod {I : Type*} (s : Finset I) (d : I -> Nat)
    (w : I -> Int) (n W : Nat)
    (hd : forall i, Membership.mem s i -> d i % 2 = 1)
    (hW : forall i, Membership.mem s i -> Dvd.dvd (2 * d i) W) :
    signedOddSquareCentered s d w W n = signedOddSquareCentered s d w W (n % W) := by
  have h := signedOddSquareCentered_shift_mul s d w (n % W) (n / W) W hd hW
  have heq : n % W + (n / W) * W = n := by nlinarith [Nat.mod_add_div n W]
  rw [heq] at h
  exact h

/-- A universal packet bound reduces exactly to the explicitly bounded full-period domain. -/
theorem signedOddSquareCentered_bounds_iff_finite {I : Type*}
    (s : Finset I) (d : I -> Nat) (w : I -> Int) (W : Nat) (L H : Int)
    (hW0 : 0 < W)
    (hd : forall i, Membership.mem s i -> d i % 2 = 1)
    (hW : forall i, Membership.mem s i -> Dvd.dvd (2 * d i) W) :
    (forall n : Nat, L <= signedOddSquareCentered s d w W n /\
      signedOddSquareCentered s d w W n <= H) <->
    (forall r : Nat, r < W -> L <= signedOddSquareCentered s d w W r /\
      signedOddSquareCentered s d w W r <= H) := by
  constructor
  next => intro h r _; exact h r
  next =>
    intro h n
    rw [signedOddSquareCentered_eq_mod s d w n W hd hW]
    exact h (n % W) (Nat.mod_lt n hW0)

/-- A common period for every divisor term in the selected owner's full expansion. -/
def oddOwnerPeriod (p : Nat) (s : Finset Nat) : Nat :=
  2 * p * Finset.prod s (fun r => r)

/-- The complete owner drift as a finite product, prior to any positivity hypothesis. -/
def oddOwnerProductDrift (s : Finset Nat) : Int :=
  2 * Finset.prod s (fun r => (r : Int) - 1)

/-- Every selected divisor term divides the actual owner period with its parity factor. -/
theorem oddOwnerPeriod_common (p : Nat) {s t : Finset Nat}
    (ht : Membership.mem s.powerset t) :
    Dvd.dvd (2 * (p * Finset.prod t (fun r => r))) (oddOwnerPeriod p s) := by
  have hprod := Finset.prod_sdiff (f := fun r : Nat => r) (Finset.mem_powerset.mp ht)
  refine Exists.intro (Finset.prod (SDiff.sdiff s t) (fun r => r)) ?_
  unfold oddOwnerPeriod
  rw [<- hprod]
  ac_rfl

/-- Each selected owner divisor is odd when all selected clocks are odd. -/
theorem oddOwner_subset_modulus_odd {p : Nat} {s t : Finset Nat}
    (hp : p % 2 = 1) (hs : forall r, Membership.mem s r -> r % 2 = 1)
    (ht : Membership.mem s.powerset t) :
    (p * Finset.prod t (fun r => r)) % 2 = 1 := by
  have htodd := prod_odd_mod_two (fun r hr => hs r ((Finset.mem_powerset.mp ht) hr))
  rw [Nat.mul_mod, hp, htodd]

/-- Exact cancellation of the complete signed drift into the product of local differences. -/
theorem oddOwner_drift_eq_product {p : Nat} {s : Finset Nat}
    (hp : p % 2 = 1) (hs : forall r, Membership.mem s r -> r % 2 = 1) :
    signedOddSquareDrift s.powerset (fun t => p * Finset.prod t (fun r => r))
      (fun t => (-1 : Int) ^ t.card) (oddOwnerPeriod p s) = oddOwnerProductDrift s := by
  unfold signedOddSquareDrift oddOwnerProductDrift
  rw [Finset.prod_sub (fun r : Nat => (r : Int)) (fun _ => (1 : Int)) s]
  simp only [Finset.prod_const_one, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hprod := Finset.prod_sdiff (f := fun r : Nat => r) (Finset.mem_powerset.mp ht)
  have hdodd := oddOwner_subset_modulus_odd hp hs ht
  have hd0 : 0 < p * Finset.prod t (fun r => r) := by omega
  have hfactor : oddOwnerPeriod p s = (p * Finset.prod t (fun r => r)) *
      (2 * Finset.prod (SDiff.sdiff s t) (fun r => r)) := by
    unfold oddOwnerPeriod
    rw [<- hprod]
    ac_rfl
  rw [hfactor, Nat.mul_div_cancel_left _ hd0]
  push_cast
  ring

/-- Exact affine periodicity of the full earlier-prime-corrected owner packet. -/
theorem oddSievedOwner_count_shift {p : Nat} {s : Finset Nat} (n : Nat)
    (hp : Nat.Prime p) (hpodd : p % 2 = 1)
    (hs : forall r, Membership.mem s r -> Nat.Prime r /\ r < p /\ r % 2 = 1) :
    ((oddSievedOwnerInSquare (n + oddOwnerPeriod p s) p s).card : Int) =
      ((oddSievedOwnerInSquare n p s).card : Int) + oddOwnerProductDrift s := by
  have hsearly : forall r, Membership.mem s r -> Nat.Prime r /\ r < p :=
    fun r hr => And.intro (hs r hr).1 (hs r hr).2.1
  have hsodd : forall r, Membership.mem s r -> r % 2 = 1 := fun r hr => (hs r hr).2.2
  rw [card_oddSievedOwnerInSquare _ hp hsearly, card_oddSievedOwnerInSquare _ hp hsearly]
  have hshift := signedOddSquarePacket_shift s.powerset
    (fun t => p * Finset.prod t (fun r => r)) (fun t => (-1 : Int) ^ t.card)
    n (oddOwnerPeriod p s) (fun t ht => oddOwner_subset_modulus_odd hpodd hsodd ht)
    (fun t ht => oddOwnerPeriod_common p ht)
  rw [oddOwner_drift_eq_product hpodd hsodd] at hshift
  exact hshift

/-- The original least-prime-owner count in the open square interval. -/
noncomputable def squareIntervalOwnerCount (n p : Nat) : Nat :=
  ((leastPrimeOwnerPacketAt p (n * n + 2 * n)).filter (fun m => n * n < m)).card

/-- The earlier odd-prime set retains primality, clock order and parity. -/
theorem oddEarlierPrimes_conditions (p : Nat) :
    forall r, Membership.mem (oddEarlierPrimes p) r -> Nat.Prime r /\ r < p /\ r % 2 = 1 := by
  intro r hr
  have h := Finset.mem_filter.mp hr
  exact And.intro h.2.1 (And.intro (Finset.mem_range.mp h.1) h.2.2)

/-- The original owner count is the actual complete signed packet. -/
theorem squareIntervalOwnerCount_eq_packet {p : Nat} (n : Nat)
    (hp : Nat.Prime p) (hp3 : 3 <= p) :
    (squareIntervalOwnerCount n p : Int) =
      signedOddSquarePacket (oddEarlierPrimes p).powerset
        (fun t => p * Finset.prod t (fun r => r)) (fun t => (-1 : Int) ^ t.card) n := by
  have hs : forall r, Membership.mem (oddEarlierPrimes p) r -> Nat.Prime r /\ r < p :=
    fun r hr => And.intro (oddEarlierPrimes_conditions p r hr).1
      (oddEarlierPrimes_conditions p r hr).2.1
  have h := card_oddSievedOwnerInSquare n hp hs
  rw [oddSievedOwnerInSquare_eq_owner hp3] at h
  exact h

/-- Every fixed odd-prime owner count has its explicit primorial period and product drift. -/
theorem squareIntervalOwnerCount_shift {p : Nat} (n : Nat)
    (hp : Nat.Prime p) (hp3 : 3 <= p) :
    (squareIntervalOwnerCount (n + oddOwnerPeriod p (oddEarlierPrimes p)) p : Int) =
      (squareIntervalOwnerCount n p : Int) + oddOwnerProductDrift (oddEarlierPrimes p) := by
  have hpodd := hp.eq_two_or_odd.resolve_left (show Not (p = 2) by omega)
  have h := oddSievedOwner_count_shift n hp hpodd (oddEarlierPrimes_conditions p)
  simpa only [oddSievedOwnerInSquare_eq_owner hp3, squareIntervalOwnerCount] using h

/-- Exact quotient-and-residue formula for every index of a fixed owner clock. -/
theorem squareIntervalOwnerCount_quot_rem {p : Nat} (n : Nat)
    (hp : Nat.Prime p) (hp3 : 3 <= p) :
    (squareIntervalOwnerCount n p : Int) =
      (squareIntervalOwnerCount (n % oddOwnerPeriod p (oddEarlierPrimes p)) p : Int) +
      (n / oddOwnerPeriod p (oddEarlierPrimes p) : Nat) *
        oddOwnerProductDrift (oddEarlierPrimes p) := by
  let s := oddEarlierPrimes p
  let W := oddOwnerPeriod p s
  have hpodd := hp.eq_two_or_odd.resolve_left (show Not (p = 2) by omega)
  have hsodd : forall r, Membership.mem s r -> r % 2 = 1 :=
    fun r hr => (oddEarlierPrimes_conditions p r hr).2.2
  have h := signedOddSquarePacket_shift_mul s.powerset
    (fun t => p * Finset.prod t (fun r => r)) (fun t => (-1 : Int) ^ t.card)
    (n % W) (n / W) W (fun t ht => oddOwner_subset_modulus_odd hpodd hsodd ht)
    (fun t ht => oddOwnerPeriod_common p ht)
  have heq : n % W + (n / W) * W = n := by nlinarith [Nat.mod_add_div n W]
  rw [heq, oddOwner_drift_eq_product hpodd hsodd] at h
  rw [<- squareIntervalOwnerCount_eq_packet n hp hp3,
    <- squareIntervalOwnerCount_eq_packet (n % W) hp hp3] at h
  exact h

/-- The common owner period is strictly positive for positive clocks. -/
theorem oddOwnerPeriod_pos {p : Nat} {s : Finset Nat} (hp : 0 < p)
    (hs : forall r, Membership.mem s r -> 0 < r) : 0 < oddOwnerPeriod p s := by
  exact Nat.mul_pos (Nat.mul_pos (by decide) hp) (Finset.prod_pos hs)

/-- The actual product drift is positive when every selected earlier clock is at least two. -/
theorem oddOwnerProductDrift_pos {s : Finset Nat}
    (hs : forall r, Membership.mem s r -> 2 <= r) : 0 < oddOwnerProductDrift s := by
  apply mul_pos (by decide : (0 : Int) < 2)
  apply Finset.prod_pos
  intro r hr
  have h : (2 : Int) <= r := by exact_mod_cast hs r hr
  omega

/-- An odd owner can occupy at most the exact number of odd candidates. -/
theorem owner_count_le_index {n p : Nat} (hp3 : 3 <= p) :
    squareIntervalOwnerCount n p <= n := by
  have hraw := card_oddMultiplesInSquare n (d := 1) (by decide)
  simp only [Nat.div_one] at hraw
  have hrawcard : (oddMultiplesInSquare n 1).card = n := by omega
  unfold squareIntervalOwnerCount
  rw [<- oddSievedOwnerInSquare_eq_owner hp3]
  exact (Finset.card_filter_le _ _).trans_eq hrawcard

/-- The explicit fixed-clock density given by the full product drift divided by its period. -/
noncomputable def fixedOwnerDensity (p : Nat) : Real :=
  (oddOwnerProductDrift (oddEarlierPrimes p) : Real) /
    (oddOwnerPeriod p (oddEarlierPrimes p) : Real)

/-- Exact normalized owner count with its actual finite-residue secondary term. -/
theorem owner_normalized_exact {p n : Nat} (hp : Nat.Prime p) (hp3 : 3 <= p)
    (hn : 0 < n) :
    (squareIntervalOwnerCount n p : Real) / n = fixedOwnerDensity p +
      (squareIntervalOwnerCount (n % oddOwnerPeriod p (oddEarlierPrimes p)) p : Real) / n -
      fixedOwnerDensity p * ((n % oddOwnerPeriod p (oddEarlierPrimes p) : Nat) : Real) / n := by
  let W := oddOwnerPeriod p (oddEarlierPrimes p)
  let D := oddOwnerProductDrift (oddEarlierPrimes p)
  have hW : 0 < W := oddOwnerPeriod_pos hp.pos
    (fun r hr => (oddEarlierPrimes_conditions p r hr).1.pos)
  have hnR : Not ((n : Real) = 0) := by exact_mod_cast (Nat.ne_of_gt hn)
  have hWR : Not ((W : Real) = 0) := by exact_mod_cast (Nat.ne_of_gt hW)
  have hcount : (squareIntervalOwnerCount n p : Real) =
      (squareIntervalOwnerCount (n % W) p : Real) + (n / W : Nat) * (D : Real) := by
    have hReal := congrArg (fun x : Int => (x : Real))
      (squareIntervalOwnerCount_quot_rem n hp hp3)
    push_cast at hReal
    exact hReal
  have hnReal : (n % W : Nat) + (W : Real) * (n / W : Nat) = (n : Real) := by
    exact_mod_cast Nat.mod_add_div n W
  have hmul := congrArg (fun x : Real => x * (W : Real)) hcount
  have hmulN := congrArg (fun x : Real => x * (D : Real)) hnReal
  change (squareIntervalOwnerCount n p : Real) / n = (D : Real) / W +
    (squareIntervalOwnerCount (n % W) p : Real) / n - (D : Real) / W * (n % W : Nat) / n
  field_simp [hnR, hWR]
  nlinarith

/-- Every fixed odd-prime owner has the explicit normalized limit; no uniform moving-clock limit is asserted. -/
theorem owner_normalized_tendsto {p : Nat} (hp : Nat.Prime p) (hp3 : 3 <= p) :
    Filter.Tendsto (fun n : Nat => (squareIntervalOwnerCount n p : Real) / n)
      Filter.atTop (nhds (fixedOwnerDensity p)) := by
  let W := oddOwnerPeriod p (oddEarlierPrimes p)
  have hW : 0 < W := oddOwnerPeriod_pos hp.pos
    (fun r hr => (oddEarlierPrimes_conditions p r hr).1.pos)
  have hrem : Filter.Tendsto
      (fun n : Nat => (squareIntervalOwnerCount (n % W) p : Real) / n)
      Filter.atTop (nhds 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
      (Filter.Eventually.of_forall (fun n : Nat => Nat.cast_nonneg (squareIntervalOwnerCount (n % W) p)))
      (Filter.Eventually.of_forall (fun n : Nat =>
        (show (squareIntervalOwnerCount (n % W) p : Real) <= W by
          exact_mod_cast (le_trans (owner_count_le_index hp3) (Nat.mod_lt n hW).le))))
      tendsto_natCast_atTop_atTop
  have hr := tendsto_mod_div_atTop_nhds_zero_nat hW
  have hc : Filter.Tendsto (fun _ : Nat => fixedOwnerDensity p) Filter.atTop
      (nhds (fixedOwnerDensity p)) := tendsto_const_nhds
  have hsum : Filter.Tendsto (fun n : Nat => fixedOwnerDensity p +
      (squareIntervalOwnerCount (n % W) p : Real) / n -
      fixedOwnerDensity p * ((n % W : Nat) : Real) / n)
      Filter.atTop (nhds (fixedOwnerDensity p)) := by
    simpa [mul_div_assoc] using
      (hc.add hrem).sub (hc.mul hr)
  apply Filter.Tendsto.congr' ?_ hsum
  apply (Filter.eventually_ge_atTop (1 : Nat)).mono
  intro n hn
  exact (owner_normalized_exact hp hp3 (by omega)).symm

end Nat.PrimeSieve
