/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalLayerTransport
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalModulusLedger

/-!
# Signed quadratic-layer core and boundary ledger

The whole same-divisor packet on an aligned pair of quadratic rows is its
signed union-of-divisors coefficient sum plus two possible boundary terms.
The boundary loss is at most nine per row. No sign of the retained core or
of any omitted center tail is assumed.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- The actual paired-floor packet on the union of two aligned quadratic divisor rows. -/
noncomputable def quadraticLayerPacket (n h : Nat) (s : Finset Nat) (c : Nat -> Int) : Int :=
  (Union.union (quadraticDivisorLayer n h s) (quadraticDivisorLayer (n+1) h s)).sum
    (fun d => c d * (2 * oddSquareFloor (n+1) d - oddSquareFloor n d))

/-- The complete signed coefficient sum on the union of aligned rows, with no assumed sign. -/
noncomputable def quadraticLayerCore (n h : Nat) (s : Finset Nat) (c : Nat -> Int) : Int :=
  (Union.union (quadraticDivisorLayer n h s) (quadraticDivisorLayer (n+1) h s)).sum c

/-- Only the old-only and new-only corrections after exact interior cancellation. -/
noncomputable def quadraticLayerBoundary (n h : Nat) (s : Finset Nat) (c : Nat -> Int) : Int :=
  -2 * ((quadraticDivisorLayer n h s).filter (fun d =>
    Not (Membership.mem (quadraticDivisorLayer (n+1) h s) d))).sum c +
    ((quadraticDivisorLayer (n+1) h s).filter (fun d =>
      Not (Membership.mem (quadraticDivisorLayer n h s) d))).sum c

/-- The signed interior sum is retained exactly; only two possible row boundaries remain. -/
theorem quadraticLayerPacket_eq_core_add_boundary (n h : Nat) {s : Finset Nat}
    (c : Nat -> Int) (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1) :
    quadraticLayerPacket n h s c = quadraticLayerCore n h s c + quadraticLayerBoundary n h s c := by
  let a := quadraticDivisorLayer n h s
  let b := quadraticDivisorLayer (n+1) h s
  let g := fun d => c d * (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)
  have hdis : Disjoint a (b.filter (fun d => Not (Membership.mem a d))) := by
    apply Finset.disjoint_left.mpr
    intro d hda hdb
    exact (Finset.mem_filter.mp hdb).2 hda
  have hunion : Union.union a (b.filter (fun d => Not (Membership.mem a d))) = Union.union a b := by
    ext d
    by_cases hda : Membership.mem a d <;> simp [hda]
  have hsplit (f : Nat -> Int) :
      (Union.union a b).sum f = a.sum f + (b.filter (fun d => Not (Membership.mem a d))).sum f := by
    rw [<- hunion, Finset.sum_union hdis]
  have ha : a.sum g = a.sum c - 2 * (a.filter (fun d => Not (Membership.mem b d))).sum c := by
    rw [Finset.sum_filter, Finset.mul_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hddata := hs d (Finset.mem_filter.mp hd).1
    have hpair := quadraticLayer_old_paired_floor hddata.1 hddata.2 hd
    change 2 * oddSquareFloor (n+1) d - oddSquareFloor n d =
      (if Membership.mem b d then (1 : Int) else -1) at hpair
    dsimp [g]
    rw [hpair]
    by_cases hdb : Membership.mem b d <;> simp [hdb] <;> ring
  have hb : (b.filter (fun d => Not (Membership.mem a d))).sum g =
      2 * (b.filter (fun d => Not (Membership.mem a d))).sum c := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hm := Finset.mem_filter.mp hd
    have hddata := hs d (Finset.mem_filter.mp hm.1).1
    have hpair := quadraticLayer_new_paired_floor hddata.1 hddata.2 hm.1
    change 2 * oddSquareFloor (n+1) d - oddSquareFloor n d =
      (if Membership.mem a d then (1 : Int) else 2) at hpair
    rw [if_neg hm.2] at hpair
    dsimp [g]
    rw [hpair]
    ring
  change (Union.union a b).sum g = (Union.union a b).sum c +
    (-2 * (a.filter (fun d => Not (Membership.mem b d))).sum c +
      (b.filter (fun d => Not (Membership.mem a d))).sum c)
  rw [hsplit g, hsplit c, ha, hb]
  ring

/-- Actual old-only and new-only row capacities bound the absolute boundary correction by nine. -/
theorem abs_quadraticLayerBoundary_le (n h : Nat) {s : Finset Nat} (c : Nat -> Int)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hc : forall d, Membership.mem s d -> (-3 : Int) <= c d /\ c d <= 3) :
    abs (quadraticLayerBoundary n h s c) <= 9 := by
  have hsum (t : Finset Nat) (ht : t.card <= 1)
      (hct : forall d, Membership.mem t d -> (-3 : Int) <= c d /\ c d <= 3) :
      (-3 : Int) <= t.sum c /\ t.sum c <= 3 := by
    have hlo := Finset.sum_le_sum (fun d hd => (hct d hd).1)
    have hhi := Finset.sum_le_sum (fun d hd => (hct d hd).2)
    have hcard : (t.card : Int) <= 1 := by exact_mod_cast ht
    simp only [Finset.sum_const, nsmul_eq_mul] at hlo hhi
    constructor <;> nlinarith
  have hold := hsum _ (quadraticLayer_old_only_card_le_one n h hs)
    (fun d hd => hc d (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1)
  have hnew := hsum _ (quadraticLayer_new_only_card_le_one n h hs)
    (fun d hd => hc d (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1)
  unfold quadraticLayerBoundary
  rw [abs_le]
  constructor <;> linarith

/-- The entire paired row differs from its signed union-core by at most nine. -/
theorem quadraticLayerPacket_core_error (n h : Nat) {s : Finset Nat} (c : Nat -> Int)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hc : forall d, Membership.mem s d -> (-3 : Int) <= c d /\ c d <= 3) :
    abs (quadraticLayerPacket n h s c - quadraticLayerCore n h s c) <= 9 := by
  rw [quadraticLayerPacket_eq_core_add_boundary n h c hs]
  simpa only [add_sub_cancel_left] using abs_quadraticLayerBoundary_le n h c hs hc

/-- The first J aligned rows have total signed-core error at most nine times J, without dropping a row. -/
theorem quadraticLayerPrefix_core_error (n J : Nat) {s : Finset Nat} (c : Nat -> Int)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hc : forall d, Membership.mem s d -> (-3 : Int) <= c d /\ c d <= 3) :
    abs ((Finset.Icc 1 J).sum (fun h => quadraticLayerPacket n h s c) -
      (Finset.Icc 1 J).sum (fun h => quadraticLayerCore n h s c)) <= 9*(J : Int) := by
  rw [<- Finset.sum_sub_distrib]
  calc
    _ <= (Finset.Icc 1 J).sum (fun h =>
      abs (quadraticLayerPacket n h s c - quadraticLayerCore n h s c)) :=
        Finset.abs_sum_le_sum_abs _ _
    _ <= (Finset.Icc 1 J).sum (fun _ => (9 : Int)) :=
      Finset.sum_le_sum (fun h _ => quadraticLayerPacket_core_error n h c hs hc)
    _ = _ := by simp [mul_comm]

/-- The first odd cofactor after any endpoint lies within one complete odd-multiple period. -/
theorem exists_odd_cofactor_after (A : Nat) {d : Nat} (hd : 0 < d) :
    exists r : Nat, r % 2 = 1 /\ A < d*r /\ d*r <= A+2*d := by
  let q := A/d
  let r := 2*((q+1)/2)+1
  have hodd : r % 2 = 1 := by dsimp [r]; omega
  have hlow : q+1 <= r := by dsimp [r]; omega
  have hhigh : r <= q+2 := by dsimp [r]; omega
  have hlo := Nat.lt_mul_div_succ A hd
  have hmullo := Nat.mul_le_mul_left d hlow
  have hmulhi := Nat.mul_le_mul_left d hhigh
  have hdiv := Nat.div_mul_le_self A d
  change A < d*(q+1) at hlo
  change q*d <= A at hdiv
  exact Exists.intro r (And.intro hodd (And.intro (by omega) (by nlinarith)))

/-- In the short divisor band, only the middle square can obstruct a live odd cofactor. -/
theorem exists_odd_cofactor_two_windows_of_not_dvd_middle {n d : Nat}
    (hd : n+1 < d) (hband : d <= 2*n+1)
    (hmid : Not (Dvd.dvd d ((n+1)*(n+1)))) :
    exists r : Nat, r % 2 = 1 /\
      ((n*n < d*r /\ d*r <= n*n+2*n) \/
       ((n+1)*(n+1) < d*r /\ d*r <= (n+1)*(n+1)+2*(n+1))) := by
  choose r hr using exists_odd_cofactor_after (n*n) (show 0 < d by omega)
  have hne : Not (d*r = (n+1)*(n+1)) := by
    intro he
    apply hmid
    exact Exists.intro r he.symm
  refine Exists.intro r (And.intro hr.1 ?_)
  by_cases hold : d*r < (n+1)*(n+1)
  next => exact Or.inl (And.intro hr.2.1 (by nlinarith))
  next => exact Or.inr (And.intro (by omega) (by nlinarith [hr.2.2]))

/-- Squarefreeness excludes the middle-square obstruction throughout the divisor band. -/
theorem exists_odd_cofactor_two_windows_of_squarefree {n d : Nat}
    (hd : n+1 < d) (hband : d <= 2*n+1) (hsq : Squarefree d) :
    exists r : Nat, r % 2 = 1 /\
      ((n*n < d*r /\ d*r <= n*n+2*n) \/
       ((n+1)*(n+1) < d*r /\ d*r <= (n+1)*(n+1)+2*(n+1))) := by
  apply exists_odd_cofactor_two_windows_of_not_dvd_middle hd hband
  intro hmid
  have hpow : Dvd.dvd d ((n+1)^2) := by simpa only [pow_two] using hmid
  have hroot := (hsq.dvd_pow_iff_dvd (by decide : Not ((2 : Nat) = 0))).mp hpow
  have hle := Nat.le_of_dvd (show 0 < n+1 by omega) hroot
  omega

/-- The complete paired floor has no holes on odd squarefree moduli between n+1 and2n+1. -/
theorem paired_floor_ne_zero_of_squarefree_band {n d : Nat}
    (hd : n+1 < d) (hband : d <= 2*n+1) (hdodd : d % 2 = 1) (hsq : Squarefree d) :
    Not (2 * oddSquareFloor (n+1) d - oddSquareFloor n d = 0) := by
  choose r hr using exists_odd_cofactor_two_windows_of_squarefree hd hband hsq
  rcases hr.2 with hold | hnew
  next =>
    have he := paired_floor_of_old_pair hd hdodd hr.1 hold.1 hold.2
    split_ifs at he <;> omega
  next =>
    have he := paired_floor_of_new_pair hd hdodd hr.1 hnew.1 hnew.2
    split_ifs at he <;> omega

/-- Every actual prime-subset modulus has radical divisibility, without an added squarefreeness hypothesis. -/
theorem squareModulusSupport_dvd_square_iff {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p)
    {d : Nat} (hd : Membership.mem (squareModulusSupport a b) d) (m : Nat) :
    Dvd.dvd d (m*m) <-> Dvd.dvd d m := by
  choose x hx using Finset.mem_image.mp hd
  have hp : forall p, Membership.mem (Union.union x.1 x.2) p -> Nat.Prime p := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    next => exact ha p ((Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).1) h)
    next => exact hb p ((Finset.mem_powerset.mp (Finset.mem_product.mp hx.1).2) h)
  rw [<- hx.2, prod_primes_dvd_iff hp (m*m), prod_primes_dvd_iff hp m]
  constructor
  next =>
    intro h p hpmem
    exact Or.elim ((hp p hpmem).dvd_mul.mp (h p hpmem)) id id
  next =>
    intro h p hpmem
    exact dvd_mul_of_dvd_left (h p hpmem) m

/-- The actual supported modulus band has a live cofactor in one of the two windows. -/
theorem exists_odd_cofactor_two_windows_of_modulusSupport {n d : Nat} {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p)
    (hb : forall p, Membership.mem b p -> Nat.Prime p)
    (hsupport : Membership.mem (squareModulusSupport a b) d)
    (hd : n+1 < d) (hband : d <= 2*n+1) :
    exists r : Nat, r % 2 = 1 /\
      ((n*n < d*r /\ d*r <= n*n+2*n) \/
       ((n+1)*(n+1) < d*r /\ d*r <= (n+1)*(n+1)+2*(n+1))) := by
  apply exists_odd_cofactor_two_windows_of_not_dvd_middle hd hband
  intro hmid
  have hroot := (squareModulusSupport_dvd_square_iff ha hb hsupport (n+1)).mp hmid
  have hle := Nat.le_of_dvd (show 0 < n+1 by omega) hroot
  omega

/-- No actual supported odd-prime product modulus in the band is lost to the middle square. -/
theorem paired_floor_ne_zero_of_modulusSupport_band {n d : Nat} {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1)
    (hsupport : Membership.mem (squareModulusSupport a b) d)
    (hd : n+1 < d) (hband : d <= 2*n+1) :
    Not (2 * oddSquareFloor (n+1) d - oddSquareFloor n d = 0) := by
  have hodd := squareModulusSupport_odd (fun p hp => (ha p hp).2)
    (fun p hp => (hb p hp).2) hsupport
  choose r hr using exists_odd_cofactor_two_windows_of_modulusSupport
    (fun p hp => (ha p hp).1) (fun p hp => (hb p hp).1) hsupport hd hband
  rcases hr.2 with hold | hnew
  next =>
    have he := paired_floor_of_old_pair hd hodd hr.1 hold.1 hold.2
    split_ifs at he <;> omega
  next =>
    have he := paired_floor_of_new_pair hd hodd hr.1 hnew.1 hnew.2
    split_ifs at he <;> omega

/-- A large divisor occurring in both windows has cofactors differing by exactly two. -/
theorem old_new_cofactor_step {n d r t : Nat} (hd : n+1 < d)
    (hrodd : r % 2 = 1) (htodd : t % 2 = 1)
    (hrold : n*n < d*r) (hrtop : d*r <= n*n+2*n)
    (htnew : (n+1)*(n+1) < d*t) (httop : d*t <= (n+1)*(n+1)+2*(n+1)) :
    t = r+2 := by
  have hrt : r < t := by
    by_contra h
    have hp := Nat.mul_le_mul_left d (show t <= r by omega)
    nlinarith
  have hge : r+2 <= t := by omega
  have hle : t <= r+2 := by
    by_contra h
    have hgap : r+4 <= t := by omega
    have hp := Nat.mul_le_mul_left d hgap
    nlinarith
  omega

/-- A large divisor cannot occur in aligned old/new row unions with different center indices. -/
theorem quadraticLayer_union_index_unique {n h k d : Nat} {s : Finset Nat}
    (hd : n+1 < d)
    (hh : Membership.mem (Union.union (quadraticDivisorLayer n h s)
      (quadraticDivisorLayer (n+1) h s)) d)
    (hk : Membership.mem (Union.union (quadraticDivisorLayer n k s)
      (quadraticDivisorLayer (n+1) k s)) d) : h = k := by
  rcases Finset.mem_union.mp hh with hh | hh
  next =>
    choose r hr using (Finset.mem_filter.mp hh).2
    rcases Finset.mem_union.mp hk with hk | hk
    next =>
      choose t ht using (Finset.mem_filter.mp hk).2
      have he := odd_cofactor_unique (show n < d by omega) hr.1 ht.1
        hr.2.2.1 (by nlinarith [hr.2.2.2]) ht.2.2.1 (by nlinarith [ht.2.2.2])
      omega
    next =>
      choose t ht using (Finset.mem_filter.mp hk).2
      have he := old_new_cofactor_step hd hr.1 ht.1 hr.2.2.1 hr.2.2.2 ht.2.2.1 ht.2.2.2
      omega
  next =>
    choose r hr using (Finset.mem_filter.mp hh).2
    rcases Finset.mem_union.mp hk with hk | hk
    next =>
      choose t ht using (Finset.mem_filter.mp hk).2
      have he := old_new_cofactor_step hd ht.1 hr.1 ht.2.2.1 ht.2.2.2 hr.2.2.1 hr.2.2.2
      omega
    next =>
      choose t ht using (Finset.mem_filter.mp hk).2
      have he := odd_cofactor_unique hd hr.1 ht.1 hr.2.2.1
        (by nlinarith [hr.2.2.2]) ht.2.2.1 (by nlinarith [ht.2.2.2])
      omega

/-- The full union of supported moduli in the first J aligned quadratic rows. -/
noncomputable def quadraticLayerUnionPrefix (n J : Nat) (s : Finset Nat) : Finset Nat :=
  (Finset.Icc 1 J).biUnion (fun h =>
    Union.union (quadraticDivisorLayer n h s) (quadraticDivisorLayer (n+1) h s))

/-- Exact prefix reindexing into a union of moduli; aligned layer disjointness prevents multiplicity. -/
theorem sum_quadraticLayerUnionPrefix (n J : Nat) (s : Finset Nat)
    {A : Type*} [AddCommMonoid A] (f : Nat -> A)
    (hs : forall d, Membership.mem s d -> n+1 < d) :
    (quadraticLayerUnionPrefix n J s).sum f =
      (Finset.Icc 1 J).sum (fun h =>
        (Union.union (quadraticDivisorLayer n h s) (quadraticDivisorLayer (n+1) h s)).sum f) := by
  have hdis : (Finset.Icc 1 J : Set Nat).PairwiseDisjoint (fun h =>
      Union.union (quadraticDivisorLayer n h s) (quadraticDivisorLayer (n+1) h s)) := by
    intro h hh k hk hne
    apply Finset.disjoint_left.mpr
    intro d hdh hdk
    have hds : Membership.mem s d := by
      rcases Finset.mem_union.mp hdh with h | h
      next => exact (Finset.mem_filter.mp h).1
      next => exact (Finset.mem_filter.mp h).1
    exact hne (quadraticLayer_union_index_unique (hs d hds) hdh hdk)
  unfold quadraticLayerUnionPrefix
  exact Finset.sum_biUnion hdis

/-- Every modulus in the finite row prefix belongs to its original support. -/
theorem quadraticLayerUnionPrefix_subset (n J : Nat) (s : Finset Nat) :
    forall d, Membership.mem (quadraticLayerUnionPrefix n J s) d -> Membership.mem s d := by
  intro d hd
  choose h hh using Finset.mem_biUnion.mp hd
  rcases Finset.mem_union.mp hh.2 with h | h
  next => exact (Finset.mem_filter.mp h).1
  next => exact (Finset.mem_filter.mp h).1

/-- The exact prefix modulus sum differs from its signed core by at most nine times the cutoff. -/
theorem quadraticLayerUnionPrefix_core_error (n J : Nat) {s : Finset Nat} (c : Nat -> Int)
    (hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1)
    (hc : forall d, Membership.mem s d -> (-3 : Int) <= c d /\ c d <= 3) :
    abs ((quadraticLayerUnionPrefix n J s).sum (fun d =>
      c d * (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)) -
        (quadraticLayerUnionPrefix n J s).sum c) <= 9*(J : Int) := by
  have hs' := fun d hd => (hs d hd).1
  rw [sum_quadraticLayerUnionPrefix n J s
      (fun d => c d * (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)) hs',
    sum_quadraticLayerUnionPrefix n J s c hs']
  exact quadraticLayerPrefix_core_error n J c hs hc

/-- The complete joint packet retains every outside-prefix term after applying the proved prefix core bound. -/
theorem squareJointPacket_layerPrefix_lower {n : Nat} (_hn : 2 <= n) (J : Nat)
    {a b : Finset Nat}
    (ha : forall p, Membership.mem a p -> Nat.Prime p /\ p % 2 = 1)
    (hb : forall p, Membership.mem b p -> Nat.Prime p /\ p % 2 = 1)
    (hab : Disjoint a b) :
    let s := (squareModulusSupport a b).filter (fun d => n+1 < d)
    let p := quadraticLayerUnionPrefix n J s
    p.sum (squareModulusCoefficient a b) - 9*(J : Int) +
      ((squareModulusSupport a b).filter (fun d => Not (Membership.mem p d))).sum
        (fun d => squareModulusCoefficient a b d *
          (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)) <=
      2 * squareJointPacket (n+1) a b - squareJointPacket n a b := by
  let s := (squareModulusSupport a b).filter (fun d => n+1 < d)
  let p := quadraticLayerUnionPrefix n J s
  let c := squareModulusCoefficient a b
  let f := fun d => c d * (2 * oddSquareFloor (n+1) d - oddSquareFloor n d)
  change p.sum c - 9*(J : Int) +
    ((squareModulusSupport a b).filter (fun d => Not (Membership.mem p d))).sum f <= _
  have hs : forall d, Membership.mem s d -> n+1 < d /\ d % 2 = 1 := by
    intro d hd
    have hm := Finset.mem_filter.mp hd
    exact And.intro hm.2 (squareModulusSupport_odd
      (fun p hp => (ha p hp).2) (fun p hp => (hb p hp).2) hm.1)
  have herror := quadraticLayerUnionPrefix_core_error n J c hs
    (fun d _ => squareModulusCoefficient_bounds a b d)
  change abs (p.sum f - p.sum c) <= 9*(J : Int) at herror
  have hsub : forall d, Membership.mem p d -> Membership.mem (squareModulusSupport a b) d := by
    intro d hd
    exact (Finset.mem_filter.mp (quadraticLayerUnionPrefix_subset n J s d hd)).1
  have hfilter : (squareModulusSupport a b).filter (fun d => Membership.mem p d) = p := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    next => exact fun h => h.2
    next => exact fun h => And.intro (hsub d h) h
  have hsplit := Finset.sum_filter_add_sum_filter_not (squareModulusSupport a b)
    (fun d => Membership.mem p d) f
  rw [hfilter] at hsplit
  have hpacket := squareJointPacket_paired_modulus_sum n ha hb hab
  change 2 * squareJointPacket (n+1) a b - squareJointPacket n a b =
    (squareModulusSupport a b).sum f at hpacket
  rw [hpacket]
  have hlower := (abs_le.mp herror).1
  linarith

end Nat.PrimeSieve
