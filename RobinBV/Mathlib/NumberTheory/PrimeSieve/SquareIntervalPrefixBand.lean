/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalLayerLedger

/-!
# Explicit divisor bands for quadratic-center prefixes

Quadratic factor positivity gives an explicit square-root divisor endpoint.
Adjacent-base endpoints differ by at most two. These are exact finite
geometric statements; no coefficient or omitted-tail sign is assumed.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- The explicit upper divisor endpoint for a prefix of quadratic factor centers. -/
def quadraticPrefixBandEnd (n J : Nat) : Nat :=
  n+J+Nat.sqrt (2*n*J+J*J-1)

/-- Every divisor in a retained quadratic row satisfies the explicit prefix endpoint. -/
theorem quadraticDivisorLayer_le_bandEnd {n h J d : Nat} {s : Finset Nat}
    (hd : n < d) (hh : h <= J) (hmem : Membership.mem (quadraticDivisorLayer n h s) d) :
    d <= quadraticPrefixBandEnd n J := by
  choose r hr using (Finset.mem_filter.mp hmem).2
  have htop : d*r < (n+1)*(n+1) := by nlinarith [hr.2.2.2]
  have hrbound := cofactor_le_index hd htop
  have hdodd : d % 2 = 1 := by omega
  let t := (d-r)/2
  have heq : d = r+2*t := by dsimp [t]; omega
  have hgap : 0 < t := by omega
  have hcell : OddFactorGapCell n r t := by
    refine { odd_left := hr.1, gap_pos := hgap, interval_lower := ?_, interval_upper := ?_ }
    next => rw [<- heq]; simpa only [Nat.mul_comm] using hr.2.2.1
    next => rw [<- heq]; simpa only [Nat.mul_comm] using htop
  have hcenter : r+t <= n+J := by omega
  have hsq := hcell.halfGap_sq_lt hcenter
  have hsqrt : t <= Nat.sqrt (2*n*J+J*J-1) := Nat.le_sqrt.mpr (by omega)
  unfold quadraticPrefixBandEnd
  omega

/-- Up to one quarter of the base index, the endpoint stays within twice that index. -/
theorem quadraticPrefixBandEnd_le_twice {n J : Nat} (hJ : 4*J <= n) :
    quadraticPrefixBandEnd n J <= 2*n := by
  let R := 2*n*J+J*J-1
  let s := Nat.sqrt R
  have hs : s*s <= R := Nat.le_sqrt.mp (le_refl s)
  have hR : R <= 2*n*J+J*J := by dsimp [R]; omega
  let b := n-J
  have hb : b+J = n := by dsimp [b]; omega
  change n+J+s <= 2*n
  by_contra hbad
  have hge : b+1 <= s := by omega
  have hsq := Nat.mul_le_mul hge hge
  have hbJ := congrArg (fun z : Nat => z*J) hb
  have hbSq := congrArg (fun z : Nat => z*z) hb
  have hnJ := Nat.mul_le_mul_left n hJ
  nlinarith

/-- Adjacent-base quadratic prefix endpoints differ by either one or two. -/
theorem quadraticPrefixBandEnd_successor_width {n J : Nat} (hn : 1 <= n) (hJ : 1 <= J) :
    quadraticPrefixBandEnd n J + 1 <= quadraticPrefixBandEnd (n+1) J /\
      quadraticPrefixBandEnd (n+1) J <= quadraticPrefixBandEnd n J + 2 := by
  let R0 := 2*n*J+J*J-1
  let R1 := 2*(n+1)*J+J*J-1
  let S0 := Nat.sqrt R0
  let S1 := Nat.sqrt R1
  have hJJ : 1 <= J*J := by nlinarith
  have hnJ : 1 <= n*J := by simpa using Nat.mul_le_mul hn hJ
  have hR0 : R0+1 = 2*n*J+J*J := by dsimp [R0]; omega
  have hR1 : R1+1 = 2*(n+1)*J+J*J := by dsimp [R1]; omega
  have hR : R1 = R0+2*J := by nlinarith
  have hJS : J <= S0 := Nat.le_sqrt.mpr (show J*J <= R0 by nlinarith)
  have hupper : R0 < (S0+1)*(S0+1) := by
    by_contra h
    have hbad : S0+1 <= S0 := Nat.le_sqrt.mpr (show (S0+1)*(S0+1) <= R0 by omega)
    omega
  have hstep : S1 <= S0+1 := by
    by_contra h
    have hge : S0+2 <= S1 := by omega
    have hlow : (S0+2)*(S0+2) <= R1 := Nat.le_sqrt.mp hge
    nlinarith
  have hsq : S0*S0 <= R0 := Nat.le_sqrt.mp (le_refl S0)
  have hmono : S0 <= S1 := Nat.le_sqrt.mpr (le_trans hsq (show R0 <= R1 by omega))
  change n+J+S0+1 <= n+1+J+S1 /\ n+1+J+S1 <= n+J+S0+2
  omega

/-- The complementary factor at the retained center lies strictly above the lower square. -/
theorem bandEnd_complement_mul_gt_square {n J d : Nat}
    (hJ : 1 <= J) (hcut : 4*J <= n) (hd : n+1 < d)
    (hend : d <= quadraticPrefixBandEnd n J) :
    n*n < d*(2*(n+J)-d) := by
  have hdcap := le_trans hend (quadraticPrefixBandEnd_le_twice hcut)
  let c := n+J
  let r := 2*c-d
  have hrsum : r+d = 2*c := by dsimp [r, c]; omega
  change n*n < d*r
  by_cases hcd : c <= d
  next =>
    let t := d-c
    have htd : t+c = d := by dsimp [t]; omega
    have hrt : r+t = c := by omega
    have htroot : t <= Nat.sqrt (2*n*J+J*J-1) := by
      change d <= c+Nat.sqrt (2*n*J+J*J-1) at hend
      omega
    have htsq := Nat.le_sqrt.mp htroot
    have h1 := congrArg (fun z : Nat => c*z) hrt
    have h2 := congrArg (fun z : Nat => t*z) hrt
    have h3 := congrArg (fun z : Nat => z*r) htd
    have hprod : d*r+t*t = c*c := by nlinarith
    have hc : c*c = n*n+2*n*J+J*J := by dsimp [c]; ring
    have hJJ : 1 <= J*J := by nlinarith
    have hrad : 2*n*J+J*J-1 < 2*n*J+J*J := by omega
    nlinarith
  next =>
    have hrge : n+1 <= r := by dsimp [c] at hrsum hcd; omega
    have hp := Nat.mul_le_mul (show n+1 <= d by omega) hrge
    nlinarith

/-- An admissible odd pair below the center cutoff belongs to a retained quadratic row. -/
theorem exists_quadraticLayer_index_of_center_bound {n J d r : Nat} {s : Finset Nat}
    (hd : n < d) (hdodd : d % 2 = 1) (hds : Membership.mem s d)
    (hrodd : r % 2 = 1) (hlower : n*n < d*r) (hupper : d*r <= n*n+2*n)
    (hcenter : d+r <= 2*(n+J)) :
    exists h : Nat, Membership.mem (Finset.Icc 1 J) h /\
      Membership.mem (quadraticDivisorLayer n h s) d := by
  have hrbound := cofactor_le_index hd (show d*r < (n+1)*(n+1) by nlinarith)
  let g := d-r
  have heq : r+g = d := by dsimp [g]; omega
  have hlo : n*n < r*(r+g) := by rw [heq]; simpa only [Nat.mul_comm] using hlower
  have hsum := factor_sum_gt_twice_index hlo
  let h := (d+r)/2-n
  have hpos : 1 <= h := by dsimp [h]; omega
  have hle : h <= J := by dsimp [h]; omega
  have hceq : d+r = 2*(n+h) := by dsimp [h]; omega
  exact Exists.intro h (And.intro (Finset.mem_Icc.mpr (And.intro hpos hle))
    (Finset.mem_filter.mpr (And.intro hds (Exists.intro r
      (And.intro hrodd (And.intro hceq (And.intro hlower hupper)))))))

/-- Every odd band divisor that does not divide the middle square occurs in the prefix. -/
theorem mem_prefix_of_not_dvd_middle_band {n J d : Nat} {s : Finset Nat}
    (hJ : 1 <= J) (hcut : 4*J <= n) (hd : n+1 < d)
    (hdodd : d % 2 = 1) (hds : Membership.mem s d)
    (hend : d <= quadraticPrefixBandEnd n J)
    (hmid : Not (Dvd.dvd d ((n+1)*(n+1)))) :
    Membership.mem (quadraticLayerUnionPrefix n J s) d := by
  have hdcap := le_trans hend (quadraticPrefixBandEnd_le_twice hcut)
  let R := 2*(n+J)-d
  have hRprod : n*n < d*R := bandEnd_complement_mul_gt_square hJ hcut hd hend
  have hRsum : R+d = 2*(n+J) := by dsimp [R]; omega
  have hRodd : R % 2 = 1 := by omega
  choose r hr using exists_odd_cofactor_after (n*n) (show 0 < d by omega)
  have hrR : r <= R := by
    by_contra h
    have hgap : R+2 <= r := by omega
    have hp := Nat.mul_le_mul_left d hgap
    nlinarith [hr.2.2]
  have hcenter : d+r <= 2*(n+J) := by omega
  have hne : Not (d*r = (n+1)*(n+1)) := by
    intro he
    exact hmid (Exists.intro r he.symm)
  by_cases hold : d*r < (n+1)*(n+1)
  next =>
    choose h hh using exists_quadraticLayer_index_of_center_bound
      (show n < d by omega) hdodd hds hr.1 hr.2.1
      (show d*r <= n*n+2*n by nlinarith) hcenter
    exact Finset.mem_biUnion.mpr (Exists.intro h (And.intro hh.1
      (Finset.mem_union_left (quadraticDivisorLayer (n+1) h s) hh.2)))
  next =>
    choose h hh using exists_quadraticLayer_index_of_center_bound hd hdodd hds hr.1
      (show (n+1)*(n+1) < d*r by omega)
      (show d*r <= (n+1)*(n+1)+2*(n+1) by nlinarith [hr.2.2])
      (show d+r <= 2*((n+1)+J) by omega)
    exact Finset.mem_biUnion.mpr (Exists.intro h (And.intro hh.1
      (Finset.mem_union_right (quadraticDivisorLayer n h s) hh.2)))

/-- The whole aligned prefix is bounded by the successor-base divisor endpoint. -/
theorem quadraticLayerUnionPrefix_le_bandEnd {n J d : Nat} {s : Finset Nat}
    (hn : 1 <= n) (hJ : 1 <= J) (hs : forall e, Membership.mem s e -> n+1 < e)
    (hd : Membership.mem (quadraticLayerUnionPrefix n J s) d) :
    d <= quadraticPrefixBandEnd (n+1) J := by
  have hdlarge := hs d (quadraticLayerUnionPrefix_subset n J s d hd)
  choose h hh using Finset.mem_biUnion.mp hd
  have hhJ := (Finset.mem_Icc.mp hh.1).2
  rcases Finset.mem_union.mp hh.2 with hold | hnew
  next =>
    have hb := quadraticDivisorLayer_le_bandEnd (show n < d by omega) hhJ hold
    have he := (quadraticPrefixBandEnd_successor_width hn hJ).1
    omega
  next => exact quadraticDivisorLayer_le_bandEnd hdlarge hhJ hnew

/-- The lower fixed band is included in the aligned prefix when the middle square is excluded. -/
theorem quadraticPrefixBand_subset_prefix {n J : Nat} {s : Finset Nat}
    (hJ : 1 <= J) (hcut : 4*J <= n)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hmid : forall d, Membership.mem s d -> Not (Dvd.dvd d ((n+1)*(n+1)))) :
    forall d, Membership.mem (s.filter (fun e => e <= quadraticPrefixBandEnd n J)) d ->
      Membership.mem (quadraticLayerUnionPrefix n J s) d := by
  intro d hd
  have hm := Finset.mem_filter.mp hd
  exact mem_prefix_of_not_dvd_middle_band hJ hcut (hs d hm.1).1
    (hs d hm.1).2 hm.1 hm.2 (hmid d hm.1)

/-- There is at most one odd prefix modulus beyond the lower fixed endpoint. -/
theorem quadraticLayerUnionPrefix_extra_card_le_one {n J : Nat} {s : Finset Nat}
    (hn : 1 <= n) (hJ : 1 <= J)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1) :
    ((quadraticLayerUnionPrefix n J s).filter
      (fun d => quadraticPrefixBandEnd n J < d)).card <= 1 := by
  apply Finset.card_le_one.mpr
  intro d hd e he
  have hdm := Finset.mem_filter.mp hd
  have hem := Finset.mem_filter.mp he
  have hdodd := (hs d (quadraticLayerUnionPrefix_subset n J s d hdm.1)).2
  have heodd := (hs e (quadraticLayerUnionPrefix_subset n J s e hem.1)).2
  have hdend := quadraticLayerUnionPrefix_le_bandEnd hn hJ (fun t ht => (hs t ht).1) hdm.1
  have heend := quadraticLayerUnionPrefix_le_bandEnd hn hJ (fun t ht => (hs t ht).1) hem.1
  have hwidth := (quadraticPrefixBandEnd_successor_width hn hJ).2
  omega

/-- Replacing the signed prefix core by its lower fixed band costs at most three. -/
theorem quadraticLayerUnionPrefix_band_core_error {n J : Nat} {s : Finset Nat}
    (hJ : 1 <= J) (hcut : 4*J <= n) (c : Nat -> Int)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hmid : forall d, Membership.mem s d -> Not (Dvd.dvd d ((n+1)*(n+1))))
    (hc : forall d, Membership.mem s d -> (-3 : Int) <= c d /\ c d <= 3) :
    abs ((quadraticLayerUnionPrefix n J s).sum c -
      (s.filter (fun d => d <= quadraticPrefixBandEnd n J)).sum c) <= 3 := by
  let p := quadraticLayerUnionPrefix n J s
  let b := s.filter (fun d => d <= quadraticPrefixBandEnd n J)
  let e := p.filter (fun d => quadraticPrefixBandEnd n J < d)
  have hsub := quadraticPrefixBand_subset_prefix hJ hcut hs hmid
  have heq : p.filter (fun d => d <= quadraticPrefixBandEnd n J) = b := by
    ext d
    dsimp only [b]
    simp only [Finset.mem_filter]
    constructor
    next => exact fun h => And.intro (quadraticLayerUnionPrefix_subset n J s d h.1) h.2
    next => exact fun h => And.intro (hsub d (Finset.mem_filter.mpr h)) h.2
  have hsplit := Finset.sum_filter_add_sum_filter_not p
    (fun d => d <= quadraticPrefixBandEnd n J) c
  simp only [not_le] at hsplit
  rw [heq] at hsplit
  have hecard := quadraticLayerUnionPrefix_extra_card_le_one (show 1 <= n by omega) hJ hs
  have hec : forall d, Membership.mem e d -> (-3 : Int) <= c d /\ c d <= 3 := by
    intro d hd
    exact hc d (quadraticLayerUnionPrefix_subset n J s d (Finset.mem_filter.mp hd).1)
  have hlo := Finset.sum_le_sum (fun d hd => (hec d hd).1)
  have hhi := Finset.sum_le_sum (fun d hd => (hec d hd).2)
  have hcard : (e.card : Int) <= 1 := by exact_mod_cast hecard
  simp only [Finset.sum_const, nsmul_eq_mul] at hlo hhi
  change b.sum c + e.sum c = p.sum c at hsplit
  change abs (p.sum c - b.sum c) <= 3
  rw [abs_le]
  constructor <;> nlinarith

/-- The full paired prefix differs from the fixed-band coefficient sum by at most nine times J plus three. -/
theorem quadraticLayerUnionPrefix_fixedBand_error {n J : Nat} {s : Finset Nat}
    (hJ : 1 <= J) (hcut : 4*J <= n) (c : Nat -> Int)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hmid : forall d, Membership.mem s d -> Not (Dvd.dvd d ((n+1)*(n+1))))
    (hc : forall d, Membership.mem s d -> (-3 : Int) <= c d /\ c d <= 3) :
    abs ((quadraticLayerUnionPrefix n J s).sum (fun d =>
      c d * (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)) -
        (s.filter (fun d => d <= quadraticPrefixBandEnd n J)).sum c) <= 9*(J : Int)+3 := by
  have hp := quadraticLayerUnionPrefix_core_error n J c hs hc
  have hb := quadraticLayerUnionPrefix_band_core_error hJ hcut c hs hmid hc
  have hpl := (abs_le.mp hp).1
  have hpu := (abs_le.mp hp).2
  have hbl := (abs_le.mp hb).1
  have hbu := (abs_le.mp hb).2
  rw [abs_le]
  constructor <;> linarith

/-- Actual large prime-subset moduli cannot divide the excluded middle square. -/
theorem squareModulusSupport_large_not_dvd_middle {n : Nat} {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p) :
    forall d, Membership.mem ((squareModulusSupport a b).filter (fun e => n+1 < e)) d ->
      Not (Dvd.dvd d ((n+1)*(n+1))) := by
  intro d hd hmid
  have hm := Finset.mem_filter.mp hd
  have hroot := (squareModulusSupport_dvd_square_iff ha hb hm.1 (n+1)).mp hmid
  have hle := Nat.le_of_dvd (show 0 < n+1 by omega) hroot
  omega

/-- A fixed-band lower comparison for the complete joint packet, retaining its entire support complement. -/
theorem squareJointPacket_fixedBand_lower {n J : Nat}
    (hJ : 1 <= J) (hcut : 4*J <= n) {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1)
    (hab : Disjoint a b) :
    let s := (squareModulusSupport a b).filter (fun d => n+1 < d)
    let p := quadraticLayerUnionPrefix n J s
    (s.filter (fun d => d <= quadraticPrefixBandEnd n J)).sum (squareModulusCoefficient a b) -
      (9*(J : Int)+3) +
        ((squareModulusSupport a b).filter (fun d => Not (Membership.mem p d))).sum
          (fun d => squareModulusCoefficient a b d *
            (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)) <=
      2 * squareJointPacket (n+1) a b - squareJointPacket n a b := by
  let s := (squareModulusSupport a b).filter (fun d => n+1 < d)
  have hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1 := by
    intro d hd
    have hm := Finset.mem_filter.mp hd
    exact And.intro hm.2 (squareModulusSupport_odd
      (fun p hp => (ha p hp).2) (fun p hp => (hb p hp).2) hm.1)
  have hmid := squareModulusSupport_large_not_dvd_middle
    (fun p hp => (ha p hp).1) (fun p hp => (hb p hp).1) (n := n)
  have hc := quadraticLayerUnionPrefix_band_core_error hJ hcut
    (squareModulusCoefficient a b) hs hmid
    (fun d _ => squareModulusCoefficient_bounds a b d)
  have hlo := squareJointPacket_layerPrefix_lower (show 2 <= n by omega) J ha hb hab
  have hcl := (abs_le.mp hc).1
  dsimp only at hlo
  dsimp only
  linarith

end Nat.PrimeSieve
