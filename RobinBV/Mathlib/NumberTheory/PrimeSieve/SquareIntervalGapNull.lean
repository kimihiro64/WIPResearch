/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalGapTransport
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalQuarticBand
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalSuccessorReflection

/-!
# Whole-column cancellation for near quadratic factorizations

The supported near products lie in the fourth-power divisor band. Their full
native weights vanish. Removing these integer columns changes every modulus
count together, and the exact paired packet retains all those compensations.
Only the whole column vanishes: the near modulus packet alone need not do so.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- Five-center geometry gives an explicit upper bound for each large factor. -/
theorem squareGeometricNearCells_modulus_upper {n K : Nat}
    (hK : K*K <= 8*n) {x : Prod Nat Nat}
    (hx : Membership.mem (squareGeometricNearCells n K) x) : x.2 <= n+5+K := by
  have hs : forall d, Membership.mem (squareGeometricLargeModuli n) d ->
      n+1 < d /\ d%2 = 1 := by
    intro d hd
    have h := squareGeometricLargeModuli_data hd
    exact And.intro h.1 h.2.1
  have hd := nearGapCofactorCells_data hs hx
  have hc := (squareGeometricNearCells_five_centers hK hx).2
  omega

/-- For indices at least eighteen the square-root gap and five-center shift fit inside the index. -/
theorem sqrt_eight_gap_add_five_le {n K : Nat} (hn : 18 <= n)
    (hK : K*K <= 8*n) : K+5 <= n := by
  by_contra hnot
  have hn4 : n-4+4 = n := by omega
  have hle : n-4 <= K := by omega
  have hsq := Nat.mul_le_mul hle hle
  have ht : 14 <= n-4 := by omega
  have hprod := Nat.mul_le_mul_right (n-4) ht
  nlinarith only [hn4, hsq, hK, hprod, ht]

/-- Every selected near modulus lies within the fourth-power cancellation band. -/
theorem squareGeometricNearCells_quartic_cut {n K : Nat} (hn : 18 <= n)
    (hK : K*K <= 8*n) {x : Prod Nat Nat}
    (hx : Membership.mem (squareGeometricNearCells n K) x) : x.2^4 <= n^5 := by
  have hu := squareGeometricNearCells_modulus_upper hK hx
  have hg := sqrt_eight_gap_add_five_le hn hK
  have hd : x.2 <= 2*n := by omega
  have hs := Nat.mul_le_mul hd hd
  calc
    x.2^4 = (x.2*x.2)*(x.2*x.2) := by ring
    _ <= ((2*n)*(2*n))*((2*n)*(2*n)) := Nat.mul_le_mul hs hs
    _ = 16*n^4 := by ring
    _ <= n*n^4 := Nat.mul_le_mul_right _ (by omega)
    _ = n^5 := by ring

/-- A supported fourth-power-band divisor annihilates the full native point weight. -/
theorem squareJointPointWeight_quartic_zero {n m d : Nat}
    (hodd : m%2 = 1) (hmlo : n*n < m) (hmhi : m <= (n+1)*(n+1)+2*(n+1))
    (hd : Membership.mem
      (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d)
    (hdlo : n+1 < d) (hdcut : d^4 <= n^5) (hdm : Dvd.dvd d m) :
    squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n) m = 0 := by
  unfold squareJointPointWeight
  split_ifs with hsmall
  next =>
    exact quartic_divisible_rough_joint_weight_zero hmlo hmhi hd hdlo hdcut hdm
      (squareSmallSieve_rough_of_odd hodd hsmall)
  next => rfl

/-- Every supported near-gap product has zero full native weight. -/
theorem squareGeometricNearCells_supported_point_zero {n K : Nat} (hn : 18 <= n)
    (hK : K*K <= 8*n) {x : Prod Nat Nat}
    (hx : Membership.mem (squareGeometricNearCells n K) x)
    (hd : Membership.mem
      (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) x.2) :
    squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n) (x.2*x.1) = 0 := by
  have hs : forall d, Membership.mem (squareGeometricLargeModuli n) d ->
      n+1 < d /\ d%2 = 1 := by
    intro d hd
    have h := squareGeometricLargeModuli_data hd
    exact And.intro h.1 h.2.1
  have h := nearGapCofactorCells_data hs hx
  have hm : (x.2*x.1)%2 = 1 := by rw [Nat.mul_mod, (hs x.2 h.1).2, h.2.1]
  apply squareJointPointWeight_quartic_zero hm h.2.2.2.2.2.1
    (by nlinarith only [h.2.2.2.2.2.2]) hd (hs x.2 h.1).1
    (squareGeometricNearCells_quartic_cut hn hK hx)
  exact dvd_mul_right x.2 x.1

/-- The full point weight equals the signed sum over all its supported product divisors. -/
theorem squareJointPointWeight_eq_modulus_sum {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p) (hab : Disjoint a b) (m : Nat) :
    squareJointPointWeight a b m = (squareModulusSupport a b).sum (fun d =>
      squareModulusCoefficient a b d * (if Dvd.dvd d m then (1 : Int) else 0)) := by
  let f := fun k => a.powerset.sum (fun u => (-1 : Int)^u.card *
    (b.powersetCard k).sum (fun v =>
      if Dvd.dvd ((Union.union u v).prod (fun p => p)) m then (1 : Int) else 0))
  have hsingle (d : Nat) :
      ((({m} : Finset Nat).filter (fun z => Dvd.dvd d z)).card : Int) =
        (if Dvd.dvd d m then 1 else 0) := by
    have he : ({m} : Finset Nat).filter (fun z => Dvd.dvd d z) =
        if Dvd.dvd d m then {m} else {} := by
      ext z
      by_cases hd : Dvd.dvd d m <;> simp [hd] <;> intro hz <;> simpa only [hz] using hd
    rw [he]
    split_ifs <;> simp
  have hk (k : Nat) :
      (if forall p, Membership.mem a p -> Not (Dvd.dvd p m) then
        (Nat.choose ((b.filter (fun p => Dvd.dvd p m)).card) k : Int) else 0) = f k := by
    have h := sieved_incidence_eq_signed_subset_counts ha hb ({m} : Finset Nat) k
    simp_rw [hsingle] at h
    simpa only [Finset.sum_filter, Finset.sum_singleton] using h
  rw [squareModulus_sum_eq_subsets ha hb hab]
  have ht : a.powerset.sum (fun u => b.powerset.sum (fun v => squareSubsetWeight u v *
      (if Dvd.dvd ((Union.union u v).prod (fun p => p)) m then (1 : Int) else 0))) =
      3*f 0-3*f 1+2*f 2 := by
    dsimp [f]
    simp_rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
    simp only [Finset.mul_sum, <- Finset.sum_sub_distrib, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    unfold squareSubsetWeight
    split_ifs <;> omega
  rw [ht, <- hk 0, <- hk 1, <- hk 2]
  unfold squareJointPointWeight jointIncidenceWeight
  split_ifs <;> simp

/-- Finite weighted point sums equal the complete modulus-column expansion. -/
theorem sum_weighted_squareJointPointWeight {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p) (hab : Disjoint a b)
    (s : Finset Nat) (f : Nat -> Int) :
    s.sum (fun m => f m*squareJointPointWeight a b m) =
      (squareModulusSupport a b).sum (fun d => squareModulusCoefficient a b d *
        s.sum (fun m => if Dvd.dvd d m then f m else 0)) := by
  simp_rw [squareJointPointWeight_eq_modulus_sum ha hb hab, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro m hm
  split_ifs <;> ring

/-- All integer columns hit by a supported geometric near-gap cell. -/
noncomputable def squareNearNullColumns (n K : Nat) : Finset Nat :=
  ((squareGeometricNearCells n K).filter (fun x => Membership.mem
    (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)) x.2)).image
      (fun x => x.2*x.1)

/-- Every selected integer column has zero full frozen incidence weight. -/
theorem squareNearNullColumns_point_zero {n K : Nat} (hn : 18 <= n)
    (hK : K*K <= 8*n) {m : Nat} (hm : Membership.mem (squareNearNullColumns n K) m) :
    squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n) m = 0 := by
  choose x hx using Finset.mem_image.mp hm
  rw [<- hx.2]
  have hd := Finset.mem_filter.mp hx.1
  exact squareGeometricNearCells_supported_point_zero hn hK hd.1 hd.2

/-- Whole-column cancellation retains every supported modulus and any signed column weights. -/
theorem squareNearNullColumns_full_modulus_sum {n K : Nat} (hn : 18 <= n)
    (hK : K*K <= 8*n) (f : Nat -> Int) :
    (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)).sum
      (fun d => squareModulusCoefficient (squareSmallOddPrimes n) (squareMediumOddPrimes n) d *
        (squareNearNullColumns n K).sum (fun m => if Dvd.dvd d m then f m else 0)) = 0 := by
  have ha : forall p, Membership.mem (squareSmallOddPrimes n) p -> Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1
  have hb : forall p, Membership.mem (squareMediumOddPrimes n) p -> Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1
  have hab : Disjoint (squareSmallOddPrimes n) (squareMediumOddPrimes n) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp0 := (Finset.mem_filter.mp hp).2.2.2
    have hq0 := (Finset.mem_filter.mp hq).2.2.2
    omega
  rw [<- sum_weighted_squareJointPointWeight ha hb hab]
  apply Finset.sum_eq_zero
  intro m hm
  rw [squareNearNullColumns_point_zero hn hK hm, mul_zero]

/-- Removing the selected whole columns preserves any square-window packet. -/
theorem squareJointPacket_erase_near_columns {n K : Nat} (hn : 18 <= n)
    (hK : K*K <= 8*n) (x : Nat) :
    squareJointPacket x (squareSmallOddPrimes n) (squareMediumOddPrimes n) =
      ((oddMultiplesInSquare x 1).filter (fun m =>
        Not (Membership.mem (squareNearNullColumns n K) m))).sum
          (squareJointPointWeight (squareSmallOddPrimes n) (squareMediumOddPrimes n)) := by
  rw [squareJointPacket_eq_point_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hz : Membership.mem (squareNearNullColumns n K) m
  next => simp only [hz, not_true_eq_false, if_false]; exact squareNearNullColumns_point_zero hn hK hz
  next => simp only [hz, not_false_eq_true, if_true]

/-- No actual near-gap cell survives this whole-column deletion. -/
theorem nearGapCofactorCells_erase_near_columns (n K : Nat) :
    ((nearGapCofactorCells n K
      (squareRemainingLargeModuli n (squareSmallOddPrimes n) (squareMediumOddPrimes n))).filter
        (fun x => Not (Membership.mem (squareNearNullColumns n K) (x.2*x.1)))) = {} := by
  have hs : forall d, Membership.mem
      (squareRemainingLargeModuli n (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d ->
        n+1 < d /\ d%2 = 1 := by
    intro d hd
    have h := Finset.mem_filter.mp hd
    exact And.intro h.2.1 (squareModulusSupport_odd
      (fun p hp => (Finset.mem_filter.mp hp).2.2.1)
      (fun p hp => (Finset.mem_filter.mp hp).2.2.1) h.1)
  have hout : forall d, Membership.mem
      (squareRemainingLargeModuli n (squareSmallOddPrimes n) (squareMediumOddPrimes n)) d ->
        2*n < (d-(n+1))*(d-(n+1)) :=
    fun d hd => (Finset.mem_filter.mp hd).2.2
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h := Finset.mem_filter.mp hx
  have hg := nearGapCofactorCells_subset_geometry n K hs hout h.1
  have hd := (nearGapCofactorCells_data hs h.1).1
  apply h.2
  apply Finset.mem_image.mpr
  exact Exists.intro x (And.intro
    (Finset.mem_filter.mpr (And.intro hg (Finset.mem_filter.mp hd).1)) rfl)

/-- Odd multiples in one open square window after deleting the full selected columns. -/
noncomputable def squareErasedNearOddCount (n K x d : Nat) : Nat :=
  (((oddMultiplesInSquare x 1).filter (fun m =>
    Not (Membership.mem (squareNearNullColumns n K) m))).filter (fun m => Dvd.dvd d m)).card

/-- All modulus counts change together when the zero native columns are erased. -/
theorem squareJointPacket_eq_erased_near_moduli {n K : Nat} (hn : 18 <= n)
    (hK : K*K <= 8*n) (x : Nat) :
    squareJointPacket x (squareSmallOddPrimes n) (squareMediumOddPrimes n) =
      (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)).sum
        (fun d => squareModulusCoefficient (squareSmallOddPrimes n) (squareMediumOddPrimes n) d *
          (squareErasedNearOddCount n K x d : Int)) := by
  rw [squareJointPacket_erase_near_columns hn hK]
  have ha : forall p, Membership.mem (squareSmallOddPrimes n) p -> Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1
  have hb : forall p, Membership.mem (squareMediumOddPrimes n) p -> Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp hp).2.1
  have hab : Disjoint (squareSmallOddPrimes n) (squareMediumOddPrimes n) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp0 := (Finset.mem_filter.mp hp).2.2.2
    have hq0 := (Finset.mem_filter.mp hq).2.2.2
    omega
  have h := sum_weighted_squareJointPointWeight ha hb hab
    ((oddMultiplesInSquare x 1).filter (fun m =>
      Not (Membership.mem (squareNearNullColumns n K) m))) (fun _ => (1 : Int))
  simpa only [one_mul, Finset.sum_boole, squareErasedNearOddCount] using h

/-- The complete signed successor packet uses the erased counts on every supported modulus. -/
theorem squareJointPacket_paired_erased_near_moduli {n K : Nat} (hn : 18 <= n)
    (hK : K*K <= 8*n) :
    2*squareJointPacket (n+1) (squareSmallOddPrimes n) (squareMediumOddPrimes n) -
      squareJointPacket n (squareSmallOddPrimes n) (squareMediumOddPrimes n) =
        (squareModulusSupport (squareSmallOddPrimes n) (squareMediumOddPrimes n)).sum
          (fun d => squareModulusCoefficient (squareSmallOddPrimes n) (squareMediumOddPrimes n) d *
            (2*(squareErasedNearOddCount n K (n+1) d : Int) -
              (squareErasedNearOddCount n K n d : Int))) := by
  rw [squareJointPacket_eq_erased_near_moduli hn hK,
    squareJointPacket_eq_erased_near_moduli hn hK,
    Finset.mul_sum, <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end Nat.PrimeSieve
