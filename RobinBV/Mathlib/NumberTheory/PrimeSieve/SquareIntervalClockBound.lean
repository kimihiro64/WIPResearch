/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.Progression
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalHighMedium
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalPeriodicity
/-!
# A complete finite-clock prime-count lower enclosure

The positive prefix supply uses its full signed finite period. Each low owner
row is bounded by every possible cofactor phase, while the high class is covered
by an integer hyperbola with selected small-prime exclusions. The final bound
holds for every splitting index and introduces no analytic estimate as a
hypothesis. Positivity of this explicit bound is not asserted.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- Selected-prime survivors in K consecutive odd cofactor slots. -/
noncomputable def oddCofactorWindow (S : Finset Nat) (A K : Nat) : Finset Nat :=
  (Finset.range K).filter (fun j =>
    forall ell, Membership.mem S ell -> Not (Dvd.dvd ell (2*(A+j)+1)))

/-- A finite maximum over every starting residue, not the actual owner phase. -/
noncomputable def oddCofactorWindowCapacity (S : Finset Nat) (W K : Nat) : Nat :=
  (Finset.range W).sup (fun A => (oddCofactorWindow S A K).card)

/-- The complete cofactor window retains its exact residue phase at a common clock. -/
theorem oddCofactorWindow_eq_mod (S : Finset Nat) (A W K : Nat)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    oddCofactorWindow S A K = oddCofactorWindow S (A%W) K := by
  have hmod : Nat.ModEq W A (A%W) := by simp [Nat.ModEq]
  have hd (ell j : Nat) (hell : Membership.mem S ell) :
      Dvd.dvd ell (2*(A+j)+1) <-> Dvd.dvd ell (2*(A%W+j)+1) :=
    (Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 2
      (Nat.ModEq.add_right j hmod))).dvd_iff (hW ell hell)
  ext j
  simp only [oddCofactorWindow, Finset.mem_filter]
  constructor
  next =>
    intro h
    exact And.intro h.1 (fun ell hell he => h.2 ell hell ((hd ell j hell).mpr he))
  next =>
    intro h
    exact And.intro h.1 (fun ell hell he => h.2 ell hell ((hd ell j hell).mp he))

/-- Every starting phase is bounded by the finite complete-clock maximum. -/
theorem card_oddCofactorWindow_le_capacity (S : Finset Nat) (A W K : Nat)
    (hW0 : 0 < W) (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    (oddCofactorWindow S A K).card <= oddCofactorWindowCapacity S W K := by
  rw [oddCofactorWindow_eq_mod S A W K hW]
  exact Finset.le_sup (f := fun a => (oddCofactorWindow S a K).card)
    (Finset.mem_range.mpr (Nat.mod_lt A hW0))

/-- The entire partially sieved owner row fits in a cofactor window of length ceil(n/p). -/
theorem card_oddSievedOwner_le_cofactorWindow {n p : Nat} (S : Finset Nat)
    (hp : p%2 = 1) :
    (oddSievedOwnerInSquare n p S).card <=
      (oddCofactorWindow S ((n*n/p+1)/2) ((n+p-1)/p)).card := by
  let A := (n*n/p+1)/2
  let K := (n+p-1)/p
  have hp0 : 0 < p := by omega
  have hceil : n <= p*K := by
    have he := Nat.mod_add_div (n+p-1) p
    have hl := Nat.mod_lt (n+p-1) hp0
    dsimp [K]
    omega
  have hfirst : n*n < p*(2*A+1) := by
    have hq : n*n/p < 2*A+1 := by dsimp [A]; omega
    have hh := (Nat.div_lt_iff_lt_mul hp0).mp hq
    simpa only [Nat.mul_comm] using hh
  have hsub : oddSievedOwnerInSquare n p S <=
      (oddCofactorWindow S A K).image (fun j => p*(2*(A+j)+1)) := by
    intro m hm
    have hs := Finset.mem_filter.mp hm
    have hi := Finset.mem_filter.mp hs.1
    have hu := Finset.mem_filter.mp hi.1
    have htop := Finset.mem_range.mp hu.1
    have hpm := hs.2.1
    choose r hr using hpm
    have hodd : r%2 = 1 := by
      have ho := hu.2.1
      rw [hr, Nat.mul_mod, hp] at ho
      simpa using ho
    have hlow : n*n/p < r := (Nat.div_lt_iff_lt_mul hp0).mpr (by
      rw [Nat.mul_comm r p, <- hr]
      exact hi.2)
    have hA : A <= r/2 := by dsimp [A]; omega
    let j := r/2-A
    have hrepr : r = 2*(A+j)+1 := by dsimp [j]; omega
    have hj : j < K := by
      by_contra hh
      have hge : K <= j := by omega
      have hrge : 2*A+1+2*K <= r := by omega
      have hmul := Nat.mul_le_mul_left p hrge
      rw [<- hr] at hmul
      nlinarith
    apply Finset.mem_image.mpr
    refine Exists.intro j (And.intro ?_ ?_)
    next =>
      apply Finset.mem_filter.mpr
      refine And.intro (Finset.mem_range.mpr hj) ?_
      intro ell hell hdiv
      apply hs.2.2 ell hell
      have hrd : Dvd.dvd r m := by rw [hr]; exact dvd_mul_left r p
      rw [<- hrepr] at hdiv
      exact dvd_trans hdiv hrd
    next => rw [<- hrepr, <- hr]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- A genuine pointwise owner upper bound using only the finite complete cofactor clock. -/
theorem card_oddSievedOwner_le_windowCapacity {n p W : Nat} (S : Finset Nat)
    (hp : p%2 = 1) (hW0 : 0 < W)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    (oddSievedOwnerInSquare n p S).card <= oddCofactorWindowCapacity S W ((n+p-1)/p) :=
  (card_oddSievedOwner_le_cofactorWindow S hp).trans
    (card_oddCofactorWindow_le_capacity S _ W _ hW0 hW)

/-- Nonprefix odd prime owners through an arbitrary splitting index. -/
noncomputable def lowClockOwners (S : Finset Nat) (T : Nat) : Finset Nat :=
  (Finset.range (T+1)).filter (fun p => Nat.Prime p /\ p%2 = 1 /\ Not (Membership.mem S p))

/-- Every surviving composite belongs to a low owner row or a high integer-factor cell. -/
theorem prefix_composite_mem_owner_or_lattice {n T m : Nat} (S : Finset Nat)
    (hn : 2 <= n) (hm : Membership.mem (oddSievedOwnerInSquare n 1 S) m)
    (hnp : Not (Nat.Prime m)) :
    Membership.mem ((lowClockOwners S T).biUnion (fun p => oddSievedOwnerInSquare n p S)) m \/
      Membership.mem ((siftedHighFactorCells n T S).image (fun x => x.1*x.2)) m := by
  have hs := Finset.mem_filter.mp hm
  have hi := Finset.mem_filter.mp hs.1
  have hu := Finset.mem_filter.mp hi.1
  have htop := Finset.mem_range.mp hu.1
  have hm2 : 2 <= m := by nlinarith [hi.2]
  choose r hr using exists_minFac_mul hm2 hnp
  let p := m.minFac
  have hp : Nat.Prime p := Nat.minFac_prime (by omega)
  have he : m = p*r := hr.2
  have hpd : Dvd.dvd p m := Nat.minFac_dvd m
  have hrd : Dvd.dvd r m := by rw [he]; exact dvd_mul_left r p
  have hpr : p <= r := Nat.minFac_le_of_dvd hr.1 hrd
  have hbounds := semiprime_straddles hpr
    (show n*n < p*r by rw [<- he]; exact hi.2)
    (show p*r < (n+1)*(n+1) by rw [<- he]; nlinarith)
  have hpo : p%2 = 1 := hp.eq_two_or_odd.resolve_left (by
    intro h2
    rw [h2] at hpd
    have hz := Nat.mod_eq_zero_of_dvd hpd
    omega)
  have hnotS : Not (Membership.mem S p) := fun h => hs.2.2 p h hpd
  by_cases hlow : p <= T
  next =>
    apply Or.inl
    apply Finset.mem_biUnion.mpr
    refine Exists.intro p (And.intro ?_ ?_)
    next =>
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
        (And.intro hp (And.intro hpo hnotS)))
    next => exact Finset.mem_filter.mpr (And.intro hs.1 (And.intro hpd hs.2.2))
  next =>
    apply Or.inr
    apply Finset.mem_image.mpr
    refine Exists.intro (Prod.mk p r) (And.intro ?_ he.symm)
    have hrle := Nat.le_of_dvd (show 0 < m by omega) hrd
    have hro : r%2 = 1 := by
      have ho := hu.2.1
      rw [he, Nat.mul_mod, hpo] at ho
      simpa using ho
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_product.mpr (And.intro
      (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by nlinarith)))) ?_
    refine And.intro (by omega) (And.intro (by rw [<- he]; exact hi.2)
      (And.intro (by rw [<- he]; nlinarith) (And.intro hpo (And.intro hro ?_))))
    intro ell hell
    exact And.intro (fun h => hs.2.2 ell hell (dvd_trans h hpd))
      (fun h => hs.2.2 ell hell (dvd_trans h hrd))

/-- The complete prime-count bound from a prefix supply, finite cofactor windows, and high lattice geometry. -/
theorem prefix_survivors_le_prime_owner_lattice_capacity {n T W : Nat} (S : Finset Nat)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    (oddSievedOwnerInSquare n 1 S).card <= (squareIntervalPrimes n).card +
      (lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) +
      (siftedHighFactorCells n T S).card := by
  let F := oddSievedOwnerInSquare n 1 S
  let B := F.filter (fun m => Not (Nat.Prime m))
  let rows := (lowClockOwners S T).biUnion (fun p => oddSievedOwnerInSquare n p S)
  let cells := (siftedHighFactorCells n T S).image (fun x => x.1*x.2)
  have hsub : B <= Union.union rows cells := by
    intro m hm
    have hd := Finset.mem_filter.mp hm
    exact Finset.mem_union.mpr (prefix_composite_mem_owner_or_lattice S hn hd.1 hd.2)
  have hrows : rows.card <= (lowClockOwners S T).sum
      (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) := by
    have h1 : rows.card <= (lowClockOwners S T).sum
        (fun p => (oddSievedOwnerInSquare n p S).card) := Finset.card_biUnion_le
    apply h1.trans
    apply Finset.sum_le_sum
    intro p hp
    exact card_oddSievedOwner_le_windowCapacity S (Finset.mem_filter.mp hp).2.2.1 hW0 hW
  have hbad : B.card <= rows.card + (siftedHighFactorCells n T S).card := by
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le rows cells)
    have h2 : cells.card <= (siftedHighFactorCells n T S).card := Finset.card_image_le
    omega
  have hprime : (F.filter Nat.Prime).card <= (squareIntervalPrimes n).card := by
    apply Finset.card_le_card
    intro m hm
    have hd := Finset.mem_filter.mp hm
    have hs := Finset.mem_filter.mp hd.1
    have hi := Finset.mem_filter.mp hs.1
    have hu := Finset.mem_filter.mp hi.1
    have htop := Finset.mem_range.mp hu.1
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by nlinarith))
      (And.intro hi.2 hd.2))
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) Nat.Prime
  change _ + B.card = F.card at hsplit
  change F.card <= _
  omega

/-- The fixed-prime prefix supply is the existing complete signed odd-divisor packet. -/
theorem prefix_card_eq_signed_packet (S : Finset Nat) (n : Nat)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell) :
    ((oddSievedOwnerInSquare n 1 S).card : Int) =
      signedOddSquarePacket S.powerset (fun t => t.prod (fun p => p))
        (fun t => (-1 : Int)^t.card) n := by
  have h := sum_primeSieve_eq_powerset (fun _ => (1 : Int)) (oddMultiplesInSquare n 1) hS
  simp_rw [oddMultiplesInSquare_one_filter] at h
  simpa [signedOddSquarePacket, oddSievedOwnerInSquare] using h

/-- Exact centered prefix transport, reusing the complete signed-period identity. -/
theorem prefix_defect_eq_mod (S : Finset Nat) (n : Nat)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell /\ ell%2 = 1) :
    (oddOwnerPeriod 1 S : Int)*((oddSievedOwnerInSquare n 1 S).card : Int)-
      oddOwnerProductDrift S*(n : Int) =
    (oddOwnerPeriod 1 S : Int)*
      ((oddSievedOwnerInSquare (n % oddOwnerPeriod 1 S) 1 S).card : Int)-
      oddOwnerProductDrift S*((n % oddOwnerPeriod 1 S : Nat) : Int) := by
  have hprime := fun ell hell => (hS ell hell).1
  have hodd := fun ell hell => (hS ell hell).2
  have hd : signedOddSquareDrift S.powerset (fun t => t.prod (fun p => p))
      (fun t => (-1 : Int)^t.card) (oddOwnerPeriod 1 S) = oddOwnerProductDrift S := by
    simpa only [Nat.one_mul] using oddOwner_drift_eq_product (p := 1) (by decide) hodd
  have h := signedOddSquareCentered_eq_mod S.powerset (fun t => t.prod (fun p => p))
    (fun t => (-1 : Int)^t.card) n (oddOwnerPeriod 1 S)
    (fun t ht => by simpa only [Nat.one_mul] using oddOwner_subset_modulus_odd (p := 1) (by decide) hodd ht)
    (fun t ht => by simpa only [Nat.one_mul] using oddOwnerPeriod_common 1 ht)
  simpa only [signedOddSquareCentered, hd,
    <- prefix_card_eq_signed_packet S n hprime,
    <- prefix_card_eq_signed_packet S (n % oddOwnerPeriod 1 S) hprime] using h

/-- The exact minimum centered supply over the full finite clock; zero ensures nonemptiness even for degenerate input. -/
noncomputable def prefixClockMinimum (S : Finset Nat) : Int :=
  (Insert.insert 0 (Finset.range (oddOwnerPeriod 1 S))).inf' (by simp)
    (fun r => (oddOwnerPeriod 1 S : Int)*((oddSievedOwnerInSquare r 1 S).card : Int)-
      oddOwnerProductDrift S*(r : Int))

/-- A uniform prefix supply lower bound with its exact finite-clock minimum, not an actual moving remainder. -/
theorem prefixClockMinimum_le_defect (S : Finset Nat) (n : Nat)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell /\ ell%2 = 1) :
    prefixClockMinimum S <=
      (oddOwnerPeriod 1 S : Int)*((oddSievedOwnerInSquare n 1 S).card : Int)-
        oddOwnerProductDrift S*(n : Int) := by
  rw [prefix_defect_eq_mod S n hS]
  have hW : 0 < oddOwnerPeriod 1 S := oddOwnerPeriod_pos (by decide)
    (fun ell hell => (hS ell hell).1.pos)
  unfold prefixClockMinimum
  apply Finset.inf'_le
  exact Finset.mem_insert.mpr (Or.inr (Finset.mem_range.mpr (Nat.mod_lt n hW)))

/-- Complete unconditional cross-multiplied prime-count bound from finite clock extrema and integer hyperbola capacity. -/
theorem prime_count_complete_clock_bound {n T W : Nat} (S : Finset Nat)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell /\ ell%2 = 1)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    oddOwnerProductDrift S*(n : Int)+prefixClockMinimum S <=
      (oddOwnerPeriod 1 S : Int)*
        (((squareIntervalPrimes n).card : Int)+
          ((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
          ((siftedHighFactorCells n T S).card : Int)) := by
  have hprefix := prefixClockMinimum_le_defect S n hS
  have hcover := prefix_survivors_le_prime_owner_lattice_capacity (T := T) S hn hW0 hW
  have hcast : ((oddSievedOwnerInSquare n 1 S).card : Int) <=
      ((squareIntervalPrimes n).card : Int)+
        ((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
        ((siftedHighFactorCells n T S).card : Int) := by exact_mod_cast hcover
  have hscale := _root_.mul_le_mul_of_nonneg_left hcast
    (show (0 : Int) <= oddOwnerPeriod 1 S by omega)
  linarith

/-- Keep only factor pairs compatible with being a least-prime-owner witness. -/
noncomputable def ownerPrunedHighFactorCells (n T : Nat) (S R : Finset Nat) : Finset (Prod Nat Nat) :=
  (siftedHighFactorCells n T S).filter (fun x =>
    forall ell, Membership.mem R ell ->
      (Dvd.dvd ell x.1 -> ell = x.1) /\
        (ell < x.1 -> Not (Dvd.dvd ell x.2)))

/-- Pruning cannot increase the composite allowance. -/
theorem ownerPrunedHighFactorCells_card_le (n T : Nat) (S R : Finset Nat) :
    (ownerPrunedHighFactorCells n T S R).card <= (siftedHighFactorCells n T S).card :=
  Finset.card_filter_le _ _

/-- Enforce actual prime status at the auxiliary lower-factor scale. -/
noncomputable def primeOwnerHighFactorCells (n T : Nat) (S R : Finset Nat) :
    Finset (Prod Nat Nat) :=
  (ownerPrunedHighFactorCells n T S R).filter (fun x => Nat.Prime x.1)

theorem primeOwnerHighFactorCells_card_le (n T : Nat) (S R : Finset Nat) :
    (primeOwnerHighFactorCells n T S R).card <=
      (ownerPrunedHighFactorCells n T S R).card :=
  Finset.card_filter_le _ _

/-- The actual least-prime-owner witness survives every auxiliary pruning condition. -/
theorem prefix_composite_mem_owner_or_prime_lattice {n T m : Nat} (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hm : Membership.mem (oddSievedOwnerInSquare n 1 S) m)
    (hnp : Not (Nat.Prime m)) :
    Membership.mem ((lowClockOwners S T).biUnion (fun p => oddSievedOwnerInSquare n p S)) m \/
      Membership.mem ((primeOwnerHighFactorCells n T S R).image (fun x => x.1*x.2)) m := by
  have hs := Finset.mem_filter.mp hm
  have hi := Finset.mem_filter.mp hs.1
  have hu := Finset.mem_filter.mp hi.1
  have htop := Finset.mem_range.mp hu.1
  have hm2 : 2 <= m := by nlinarith [hi.2]
  choose r hr using exists_minFac_mul hm2 hnp
  let p := m.minFac
  have hp : Nat.Prime p := Nat.minFac_prime (by omega)
  have he : m = p*r := hr.2
  have hpd : Dvd.dvd p m := Nat.minFac_dvd m
  have hrd : Dvd.dvd r m := by rw [he]; exact dvd_mul_left r p
  have hpr : p <= r := Nat.minFac_le_of_dvd hr.1 hrd
  have hbounds := semiprime_straddles hpr
    (show n*n < p*r by rw [<- he]; exact hi.2)
    (show p*r < (n+1)*(n+1) by rw [<- he]; nlinarith)
  have hpo : p%2 = 1 := hp.eq_two_or_odd.resolve_left (by
    intro h2
    rw [h2] at hpd
    have hz := Nat.mod_eq_zero_of_dvd hpd
    omega)
  have hnotS : Not (Membership.mem S p) := fun h => hs.2.2 p h hpd
  by_cases hlow : p <= T
  next =>
    apply Or.inl
    apply Finset.mem_biUnion.mpr
    refine Exists.intro p (And.intro ?_ ?_)
    next =>
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
        (And.intro hp (And.intro hpo hnotS)))
    next => exact Finset.mem_filter.mpr (And.intro hs.1 (And.intro hpd hs.2.2))
  next =>
    apply Or.inr
    apply Finset.mem_image.mpr
    refine Exists.intro (Prod.mk p r) (And.intro ?_ he.symm)
    have hrle := Nat.le_of_dvd (show 0 < m by omega) hrd
    have hro : r%2 = 1 := by
      have ho := hu.2.1
      rw [he, Nat.mul_mod, hpo] at ho
      simpa using ho
    have hcell : Membership.mem (siftedHighFactorCells n T S) (Prod.mk p r) := by
      apply Finset.mem_filter.mpr
      refine And.intro (Finset.mem_product.mpr (And.intro
        (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by nlinarith)))) ?_
      refine And.intro (by omega) (And.intro (by rw [<- he]; exact hi.2)
        (And.intro (by rw [<- he]; nlinarith) (And.intro hpo (And.intro hro ?_))))
      intro ell hell
      exact And.intro (fun h => hs.2.2 ell hell (dvd_trans h hpd))
        (fun h => hs.2.2 ell hell (dvd_trans h hrd))
    apply Finset.mem_filter.mpr
    refine And.intro ?_ hp
    apply Finset.mem_filter.mpr
    refine And.intro hcell ?_
    intro ell hell
    refine And.intro ?_ ?_
    next =>
      intro held
      have hlem := dvd_trans held hpd
      have hpl := Nat.minFac_le_of_dvd (hR ell hell) hlem
      have hlp := Nat.le_of_dvd hp.pos held
      exact Nat.le_antisymm hlp hpl
    next =>
      intro hlt held
      have hlem := dvd_trans held hrd
      have hpl := Nat.minFac_le_of_dvd (hR ell hell) hlem
      omega

/-- Prefix survivors are covered by primes, low owner windows, and owner-pruned high cells. -/
theorem prefix_survivors_le_prime_owner_prime_lattice_capacity {n T W : Nat} (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    (oddSievedOwnerInSquare n 1 S).card <= (squareIntervalPrimes n).card +
      (lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) +
      (primeOwnerHighFactorCells n T S R).card := by
  let F := oddSievedOwnerInSquare n 1 S
  let B := F.filter (fun m => Not (Nat.Prime m))
  let rows := (lowClockOwners S T).biUnion (fun p => oddSievedOwnerInSquare n p S)
  let cells := (primeOwnerHighFactorCells n T S R).image (fun x => x.1*x.2)
  have hsub : B <= Union.union rows cells := by
    intro m hm
    have hd := Finset.mem_filter.mp hm
    exact Finset.mem_union.mpr (prefix_composite_mem_owner_or_prime_lattice S R hR hn hd.1 hd.2)
  have hrows : rows.card <= (lowClockOwners S T).sum
      (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) := by
    have h1 : rows.card <= (lowClockOwners S T).sum
        (fun p => (oddSievedOwnerInSquare n p S).card) := Finset.card_biUnion_le
    apply h1.trans
    apply Finset.sum_le_sum
    intro p hp
    exact card_oddSievedOwner_le_windowCapacity S (Finset.mem_filter.mp hp).2.2.1 hW0 hW
  have hbad : B.card <= rows.card + (primeOwnerHighFactorCells n T S R).card := by
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le rows cells)
    have h2 : cells.card <= (primeOwnerHighFactorCells n T S R).card := Finset.card_image_le
    omega
  have hprime : (F.filter Nat.Prime).card <= (squareIntervalPrimes n).card := by
    apply Finset.card_le_card
    intro m hm
    have hd := Finset.mem_filter.mp hm
    have hs := Finset.mem_filter.mp hd.1
    have hi := Finset.mem_filter.mp hs.1
    have hu := Finset.mem_filter.mp hi.1
    have htop := Finset.mem_range.mp hu.1
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by nlinarith))
      (And.intro hi.2 hd.2))
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) Nat.Prime
  change _ + B.card = F.card at hsplit
  change F.card <= _
  omega

/-- Complete prime-count enclosure retaining auxiliary least-owner constraints in the high lattice. -/
theorem prime_count_prime_owner_clock_bound {n T W : Nat} (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell /\ ell%2 = 1)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    oddOwnerProductDrift S*(n : Int)+prefixClockMinimum S <=
      (oddOwnerPeriod 1 S : Int)*
        (((squareIntervalPrimes n).card : Int)+
          ((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
          ((primeOwnerHighFactorCells n T S R).card : Int)) := by
  have hprefix := prefixClockMinimum_le_defect S n hS
  have hcover := prefix_survivors_le_prime_owner_prime_lattice_capacity (T := T) S R hR hn hW0 hW
  have hcast : ((oddSievedOwnerInSquare n 1 S).card : Int) <=
      ((squareIntervalPrimes n).card : Int)+
        ((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
        ((primeOwnerHighFactorCells n T S R).card : Int) := by exact_mod_cast hcover
  have hscale := _root_.mul_le_mul_of_nonneg_left hcast
    (show (0 : Int) <= oddOwnerPeriod 1 S by omega)
  linarith

/-- Compatibility cover after forgetting the extra prime constraint. -/
theorem prefix_composite_mem_owner_or_pruned_lattice {n T m : Nat} (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hm : Membership.mem (oddSievedOwnerInSquare n 1 S) m)
    (hnp : Not (Nat.Prime m)) :
    Membership.mem ((lowClockOwners S T).biUnion (fun p => oddSievedOwnerInSquare n p S)) m \/
      Membership.mem ((ownerPrunedHighFactorCells n T S R).image (fun x => x.1*x.2)) m := by
  apply (prefix_composite_mem_owner_or_prime_lattice S R hR hn hm hnp).imp id
  have hsub : primeOwnerHighFactorCells n T S R <= ownerPrunedHighFactorCells n T S R :=
    Finset.filter_subset _ _
  intro hh
  exact Finset.image_subset_image (f := fun x : Prod Nat Nat => x.1*x.2) hsub hh

/-- Compatibility capacity after enlarging the prime-factor lattice. -/
theorem prefix_survivors_le_prime_owner_pruned_lattice_capacity {n T W : Nat} (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    (oddSievedOwnerInSquare n 1 S).card <= (squareIntervalPrimes n).card +
      (lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) +
      (ownerPrunedHighFactorCells n T S R).card := by
  exact (prefix_survivors_le_prime_owner_prime_lattice_capacity S R hR hn hW0 hW).trans
    (Nat.add_le_add_left (primeOwnerHighFactorCells_card_le n T S R) _)

/-- Complete prime-count enclosure retaining auxiliary least-owner constraints in the high lattice. -/
theorem prime_count_owner_pruned_clock_bound {n T W : Nat} (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell /\ ell%2 = 1)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    oddOwnerProductDrift S*(n : Int)+prefixClockMinimum S <=
      (oddOwnerPeriod 1 S : Int)*
        (((squareIntervalPrimes n).card : Int)+
          ((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
          ((ownerPrunedHighFactorCells n T S R).card : Int)) := by
  have hprefix := prefixClockMinimum_le_defect S n hS
  have hcover := prefix_survivors_le_prime_owner_pruned_lattice_capacity (T := T) S R hR hn hW0 hW
  have hcast : ((oddSievedOwnerInSquare n 1 S).card : Int) <=
      ((squareIntervalPrimes n).card : Int)+
        ((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
        ((ownerPrunedHighFactorCells n T S R).card : Int) := by exact_mod_cast hcover
  have hscale := _root_.mul_le_mul_of_nonneg_left hcast
    (show (0 : Int) <= oddOwnerPeriod 1 S by omega)
  linarith

end Nat.PrimeSieve
