/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LinnikResidueCount

/-!
# Block arithmetic for Linnik's residue packets

This module reassembles a length-`k` prefix and a length-`k*(r-1)` tail
into the length-`k*r` tuple used by the lossless mixed-radix frequency.
Consequently, equality of packet frequencies is equality of every power sum.
-/

set_option autoImplicit false

namespace Finset

/-- The prefix and tail block lengths add to `k*r` when `r` is positive. -/
theorem linnik_block_length_eq (k r : Nat) (hr : 0 < r) :
    k + k * (r - 1) = k * r := by
  calc
    k + k * (r - 1) = k * (1 + (r - 1)) := by ring
    _ = k * r := by congr 1 <;> omega

/-- Index equivalence between the prefix/tail sum and the full tuple. -/
def linnikBlockEquiv (k r : Nat) (hr : 0 < r) :
    Equiv (Sum (Fin k) (Fin (k * (r - 1)))) (Fin (k * r)) :=
  finSumFinEquiv.trans (finCongr (linnik_block_length_eq k r hr))

/-- Join one prefix and one tail into the corresponding full tuple. -/
def linnikJoinTuple (k r X : Nat) (hr : 0 < r)
    (vu : Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X)) :
    Fin (k * r) -> Fin X :=
  fun i => Sum.elim vu.fst vu.snd ((linnikBlockEquiv k r hr).symm i)

/-- The full mixed-radix frequency of the joined tuple is the packet
frequency used by the Fourier factorization. -/
theorem linnikMomentFrequency_join_eq_packetFrequency
    (k r X : Nat) (hr : 0 < r)
    (vu : Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X)) :
    linnikMomentFrequency k r X (linnikJoinTuple k r X hr vu) =
      linnikModDistinctPacketFrequency k r X (k * (r - 1)) vu := by
  rw [linnikMomentFrequency_eq_sum_atom]
  unfold linnikModDistinctPacketFrequency linnikPrefixFrequency
    linnikTailFrequency
  calc
    Finset.univ.sum (fun i : Fin (k * r) =>
        linnikMomentAtomFrequency k r X (linnikJoinTuple k r X hr vu i)) =
        Finset.univ.sum (fun s : Sum (Fin k) (Fin (k * (r - 1))) =>
          linnikMomentAtomFrequency k r X
            (linnikJoinTuple k r X hr vu (linnikBlockEquiv k r hr s))) := by
      apply Fintype.sum_equiv (linnikBlockEquiv k r hr).symm
      intro i
      simp
    _ = Finset.univ.sum (fun i : Fin k =>
          linnikMomentAtomFrequency k r X (vu.fst i)) +
        Finset.univ.sum (fun i : Fin (k * (r - 1)) =>
          linnikMomentAtomFrequency k r X (vu.snd i)) := by
      rw [Fintype.sum_sum_type]
      simp [linnikJoinTuple]

/-- Equality of packet frequencies is exactly equality of every power sum of
the joined full tuples. -/
theorem linnikModDistinctPacketFrequency_eq_iff_powerSums
    (k r X : Nat) (hr : 0 < r)
    (v w : Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X)) :
    linnikModDistinctPacketFrequency k r X (k * (r - 1)) v =
        linnikModDistinctPacketFrequency k r X (k * (r - 1)) w <->
      linnikMomentPowerSumData k (k * r) X
          (linnikJoinTuple k r X hr v) =
        linnikMomentPowerSumData k (k * r) X
          (linnikJoinTuple k r X hr w) := by
  rw [<- linnikMomentFrequency_join_eq_packetFrequency k r X hr v]
  rw [<- linnikMomentFrequency_join_eq_packetFrequency k r X hr w]
  exact linnikMomentFrequency_eq_iff k r X _ _

/-- Equal-frequency pairs in one residue packet, before separating prefix
and tail variables. -/
noncomputable def linnikResidueEqualPairs
    (p k r X : Nat) (hp : 0 < p) (a : Fin p) :
    Finset (Prod
      (Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X))
      (Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X))) :=
  ((linnikResiduePacket p k X (k * (r - 1)) hp a).product
      (linnikResiduePacket p k X (k * (r - 1)) hp a)).filter (fun vw =>
    linnikModDistinctPacketFrequency k r X (k * (r - 1)) vw.fst =
      linnikModDistinctPacketFrequency k r X (k * (r - 1)) vw.snd)

/-- The analytic residue packet count is exactly the cardinality of its
equal-frequency pair set. -/
theorem linnikResiduePacketPairCount_eq_card_equalPairs
    (p k r X : Nat) (hp : 0 < p) (a : Fin p) :
    linnikResiduePacketPairCount p k r X (k * (r - 1)) hp a =
      (linnikResidueEqualPairs p k r X hp a).card := by
  classical
  unfold linnikResiduePacketPairCount linnikResidueEqualPairs
    AddCircle.integerPairCount
  rw [Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]
  norm_cast
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  apply if_congr
  next =>
    constructor
    next =>
      intro h
      change linnikModDistinctPacketFrequency k r X (k * (r - 1)) v =
        linnikModDistinctPacketFrequency k r X (k * (r - 1)) w
      exact Int.ofNat_inj.mp (sub_eq_zero.mp h)
    next =>
      intro h
      change (linnikModDistinctPacketFrequency k r X
          (k * (r - 1)) v : Int) -
        (linnikModDistinctPacketFrequency k r X
          (k * (r - 1)) w : Int) = 0
      exact sub_eq_zero.mpr (congrArg Int.ofNat h)
  next => rfl
  next => rfl

/-- Reducing a shifted prefix coordinate modulo `p^k` and then modulo `p`
agrees with reducing that shifted coordinate directly modulo `p`. -/
theorem linnikShiftedResidueVector_mod_eq_shiftedResidue
    (p k a X : Nat) (hp : 0 < p) (hk : 0 < k)
    (m : Fin k -> Fin X) (i : Fin k) :
    ((linnikShiftedResidueVector p k a X hp m i).val % p) =
      (linnikShiftedResidue p a X hp (m i)).val := by
  letI : NeZero (p ^ k) :=
    NeZero.mk (Nat.ne_of_gt (Nat.pow_pos hp))
  letI : NeZero p := NeZero.mk (Nat.ne_of_gt hp)
  let z := linnikShiftedResidueVector p k a X hp m i
  have hfull : ((z.val : Nat) : ZMod (p ^ k)) =
      (((m i).val + 1 : Nat) : ZMod (p ^ k)) -
        (a : ZMod (p ^ k)) := by
    change ((((((m i).val + 1 : Nat) : ZMod (p ^ k)) -
      (a : ZMod (p ^ k))).val : Nat) : ZMod (p ^ k)) = _
    exact ZMod.natCast_zmod_val _
  have hmap := congrArg
    (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hk)) (ZMod p)) hfull
  have hmap' : ((z.val : Nat) : ZMod p) =
      (((m i).val + 1 : Nat) : ZMod p) - (a : ZMod p) := by
    simpa only [ZMod.castHom_apply, map_sub, map_natCast] using hmap
  have hval := congrArg ZMod.val hmap'
  change z.val % p =
    ((((m i).val + 1 : Nat) : ZMod p) - (a : ZMod p)).val
  simpa only [ZMod.val_natCast] using hval

/-- Distinct raw residue classes remain distinct after the common shift used
in `B(p,a)`. -/
theorem injective_shiftedResidueVector_mod_of_injective_residueIndex
    (p k a X : Nat) (hp : 0 < p) (hk : 0 < k)
    (m : Fin k -> Fin X)
    (hinj : Function.Injective (fun i : Fin k =>
      linnikResidueIndex p X hp (m i))) :
    Function.Injective (fun i : Fin k =>
      ((linnikShiftedResidueVector p k a X hp m i).val % p)) := by
  letI : NeZero p := NeZero.mk (Nat.ne_of_gt hp)
  intro i j hij
  apply hinj
  apply Fin.ext
  have hsval : (linnikShiftedResidue p a X hp (m i)).val =
      (linnikShiftedResidue p a X hp (m j)).val := by
    rw [<- linnikShiftedResidueVector_mod_eq_shiftedResidue p k a X hp hk]
    rw [<- linnikShiftedResidueVector_mod_eq_shiftedResidue p k a X hp hk]
    exact hij
  have hs :
      (((m i).val + 1 : Nat) : ZMod p) - (a : ZMod p) =
        (((m j).val + 1 : Nat) : ZMod p) - (a : ZMod p) := by
    exact ZMod.val_injective p hsval
  have hraw : (((m i).val + 1 : Nat) : ZMod p) =
      (((m j).val + 1 : Nat) : ZMod p) := sub_left_inj.mp hs
  have hv := congrArg ZMod.val hraw
  simpa only [linnikResidueIndex, ZMod.val_natCast] using hv

/-- A coordinate in residue class `a` becomes zero after shifting by `a`
modulo `p`. -/
theorem linnikShiftedResidue_eq_zero_of_residueIndex_eq
    (p X : Nat) (a : Fin p) (hp : 0 < p) (x : Fin X)
    (hx : linnikResidueIndex p X hp x = a) :
    linnikShiftedResidue p a.val X hp x = Fin.mk 0 hp := by
  letI : NeZero p := NeZero.mk (Nat.ne_of_gt hp)
  apply Fin.ext
  change ((((x.val + 1 : Nat) : ZMod p) -
    (a.val : ZMod p)).val) = (Fin.mk 0 hp).val
  have hcast : ((x.val + 1 : Nat) : ZMod p) =
      (a.val : ZMod p) := by
    apply ZMod.val_injective p
    have hval := congrArg Fin.val hx
    simpa only [linnikResidueIndex, ZMod.val_natCast,
      Nat.mod_eq_of_lt a.isLt] using hval
  rw [hcast, sub_self]
  simpa only [Fin.val_mk] using ZMod.val_zero

/-- A shifted coordinate lying in residue class `a` has zero `d`-th power
modulo `p^d`. -/
theorem linnikShiftedResidue_pow_eq_zero_of_residueIndex_eq
    (p X d : Nat) (a : Fin p) (hp : 0 < p) (hd : 0 < d) (x : Fin X)
    (hx : linnikResidueIndex p X hp x = a) :
    (((linnikShiftedResidue (p ^ d) a.val X (Nat.pow_pos hp) x).val : Nat) :
        ZMod (p ^ d)) ^ d = 0 := by
  let m : Fin d -> Fin X := fun _i => x
  let i0 : Fin d := Fin.mk 0 hd
  have hreduce := linnikShiftedResidueVector_mod_eq_shiftedResidue
    p d a.val X hp hd m i0
  have hzero := linnikShiftedResidue_eq_zero_of_residueIndex_eq
    p X a hp x hx
  have hmod :
      (linnikShiftedResidue (p ^ d) a.val X (Nat.pow_pos hp) x).val % p = 0 := by
    simpa only [m, i0, linnikShiftedResidueVector] using
      hreduce.trans (congrArg Fin.val hzero)
  choose c hc using Nat.dvd_of_mod_eq_zero hmod
  rw [hc, Nat.cast_mul, mul_pow]
  have hpzero : ((p : Nat) : ZMod (p ^ d)) ^ d = 0 := by
    rw [<- Nat.cast_pow]
    simp
  rw [hpzero, zero_mul]

/-- Literal shifted values have zero `d`-th power modulo `p^d` when their
raw residue is `a`. -/
theorem linnikShiftedValue_pow_eq_zero_of_residueIndex_eq
    (p X d : Nat) (a : Fin p) (hp : 0 < p) (hd : 0 < d) (x : Fin X)
    (hx : linnikResidueIndex p X hp x = a) :
    ((((x.val + 1 : Nat) : ZMod (p ^ d)) -
      (a.val : ZMod (p ^ d))) ^ d) = 0 := by
  letI : NeZero (p ^ d) :=
    NeZero.mk (Nat.ne_of_gt (Nat.pow_pos hp))
  have hz := linnikShiftedResidue_pow_eq_zero_of_residueIndex_eq
    p X d a hp hd x hx
  have heq :
      (((linnikShiftedResidue (p ^ d) a.val X (Nat.pow_pos hp) x).val : Nat) :
          ZMod (p ^ d)) =
        (((x.val + 1 : Nat) : ZMod (p ^ d)) -
          (a.val : ZMod (p ^ d))) := by
    unfold linnikShiftedResidue
    exact ZMod.natCast_zmod_val _
  rw [heq] at hz
  exact hz

/-- A sum over a joined tuple splits exactly into its prefix and tail sums. -/
theorem sum_linnikJoinTuple
    {R : Type*} [AddCommMonoid R]
    (k r X : Nat) (hr : 0 < r)
    (vu : Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X))
    (F : Fin X -> R) :
    Finset.univ.sum (fun i : Fin (k * r) =>
        F (linnikJoinTuple k r X hr vu i)) =
      Finset.univ.sum (fun i : Fin k => F (vu.fst i)) +
        Finset.univ.sum (fun i : Fin (k * (r - 1)) => F (vu.snd i)) := by
  calc
    Finset.univ.sum (fun i : Fin (k * r) =>
        F (linnikJoinTuple k r X hr vu i)) =
        Finset.univ.sum (fun s : Sum (Fin k) (Fin (k * (r - 1))) =>
          F (linnikJoinTuple k r X hr vu (linnikBlockEquiv k r hr s))) := by
      apply Fintype.sum_equiv (linnikBlockEquiv k r hr).symm
      intro i
      simp
    _ = Finset.univ.sum (fun i : Fin k => F (vu.fst i)) +
        Finset.univ.sum (fun i : Fin (k * (r - 1)) => F (vu.snd i)) := by
      rw [Fintype.sum_sum_type]
      simp [linnikJoinTuple]

/-- Equality of all lower power sums is preserved by a common subtraction
in any commutative ring. -/
theorem sum_sub_pow_eq_of_sum_pow_eq
    {R : Type*} [CommRing R] (m d : Nat)
    (f g : Fin m -> R) (a : R)
    (hpow : forall l, l <= d ->
      Finset.univ.sum (fun i => f i ^ l) =
        Finset.univ.sum (fun i => g i ^ l)) :
    Finset.univ.sum (fun i => (f i - a) ^ d) =
      Finset.univ.sum (fun i => (g i - a) ^ d) := by
  simp_rw [sub_eq_add_neg, add_pow]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  have hle : l <= d := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  calc
    Finset.univ.sum (fun i =>
        f i ^ l * (-a) ^ (d - l) * Nat.choose d l) =
        (Nat.choose d l : R) * (-a) ^ (d - l) *
          Finset.univ.sum (fun i => f i ^ l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (Nat.choose d l : R) * (-a) ^ (d - l) *
          Finset.univ.sum (fun i => g i ^ l) := by
      rw [hpow l hle]
    _ = Finset.univ.sum (fun i =>
        g i ^ l * (-a) ^ (d - l) * Nat.choose d l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Every equal-frequency pair in `I1(p,a)` has a prefix pair belonging to
the exact `B(p,a)` congruence space. -/
noncomputable def linnikResidueEqualPairPrefix
    (p k r X : Nat) (hp : 0 < p) (hk : 0 < k) (hr : 0 < r)
    (hx : X < p ^ k) (a : Fin p)
    (vw : linnikResidueEqualPairs p k r X hp a) :
    linnikShiftedCongruencePairs p k a.val X hp hx := by
  let v := vw.val.fst
  let w := vw.val.snd
  have hvw := Finset.mem_filter.mp vw.property
  have hvwPackets := Finset.mem_product.mp hvw.1
  have hvPacket := Finset.mem_product.mp hvwPackets.1
  have hwPacket := Finset.mem_product.mp hvwPackets.2
  have hvPrefix := Finset.mem_filter.mp hvPacket.1
  have hwPrefix := Finset.mem_filter.mp hwPacket.1
  refine Subtype.mk (v.fst, w.fst) ?_
  refine And.intro
    (injective_shiftedResidueVector_mod_of_injective_residueIndex
      p k a.val X hp hk v.fst hvPrefix.2) ?_
  refine And.intro
    (injective_shiftedResidueVector_mod_of_injective_residueIndex
      p k a.val X hp hk w.fst hwPrefix.2) ?_
  intro j
  apply (linnikShiftedPowerSum_modEq_iff
    p k a.val X hp v.fst w.fst j).2
  let d := j.val + 1
  let fv : Fin (k * r) -> Nat := fun i =>
    (linnikJoinTuple k r X hr v i).val
  let fw : Fin (k * r) -> Nat := fun i =>
    (linnikJoinTuple k r X hr w i).val
  have hdata := (linnikModDistinctPacketFrequency_eq_iff_powerSums
    k r X hr v w).1 hvw.2
  have hraw : forall t : Fin k,
      Finset.univ.sum (fun i => fv i ^ (t.val + 1)) =
        Finset.univ.sum (fun i => fw i ^ (t.val + 1)) := by
    intro t
    exact congrFun hdata t
  have haff := affine_nat_power_sums_eq_of_power_sums_general
    (k * r) k 1 1 fv fw hraw
  have hpow : forall l, l <= d ->
      Finset.univ.sum (fun i =>
        (((fv i + 1 : Nat) : ZMod (p ^ d))) ^ l) =
      Finset.univ.sum (fun i =>
        (((fw i + 1 : Nat) : ZMod (p ^ d))) ^ l) := by
    intro l hld
    cases l with
    | zero => simp
    | succ t =>
        have htk : t < k := by
          exact lt_of_lt_of_le (Nat.lt_succ_self t)
            (le_trans hld (Nat.succ_le_iff.mpr j.isLt))
        let jt : Fin k := Fin.mk t htk
        have ht := haff jt
        norm_num only [one_mul] at ht
        have ht' : Finset.univ.sum (fun i => (fv i + 1) ^ (t + 1)) =
            Finset.univ.sum (fun i => (fw i + 1) ^ (t + 1)) := by
          simpa only [jt, Fin.val_mk] using ht
        have hc := congrArg (fun n : Nat => (n : ZMod (p ^ d))) ht'
        simpa only [Nat.cast_sum, Nat.cast_pow] using hc
  have hshift := sum_sub_pow_eq_of_sum_pow_eq
    (R := ZMod (p ^ d)) (k * r) d
    (fun i => ((fv i + 1 : Nat) : ZMod (p ^ d)))
    (fun i => ((fw i + 1 : Nat) : ZMod (p ^ d)))
    (a.val : ZMod (p ^ d)) hpow
  have hvTailZero : Finset.univ.sum (fun i : Fin (k * (r - 1)) =>
      ((((v.snd i).val + 1 : Nat) : ZMod (p ^ d)) -
        (a.val : ZMod (p ^ d))) ^ d) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have htail := (Fintype.mem_piFinset.mp hvPacket.2) i
    have hres := (Finset.mem_filter.mp htail).2
    exact linnikShiftedValue_pow_eq_zero_of_residueIndex_eq
      p X d a hp (by unfold d; omega) (v.snd i) hres
  have hwTailZero : Finset.univ.sum (fun i : Fin (k * (r - 1)) =>
      ((((w.snd i).val + 1 : Nat) : ZMod (p ^ d)) -
        (a.val : ZMod (p ^ d))) ^ d) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have htail := (Fintype.mem_piFinset.mp hwPacket.2) i
    have hres := (Finset.mem_filter.mp htail).2
    exact linnikShiftedValue_pow_eq_zero_of_residueIndex_eq
      p X d a hp (by unfold d; omega) (w.snd i) hres
  have hvSplit := sum_linnikJoinTuple k r X hr v (fun x =>
    ((((x.val + 1 : Nat) : ZMod (p ^ d)) -
      (a.val : ZMod (p ^ d))) ^ d))
  have hwSplit := sum_linnikJoinTuple k r X hr w (fun x =>
    ((((x.val + 1 : Nat) : ZMod (p ^ d)) -
      (a.val : ZMod (p ^ d))) ^ d))
  unfold fv fw at hshift
  rw [hvSplit, hwSplit, hvTailZero, hwTailZero, add_zero, add_zero] at hshift
  exact hshift.symm

/-- The equal-frequency pairs lying above one fixed `B(p,a)` prefix pair. -/
noncomputable def linnikResidueEqualPairPrefixFiber
    (p k r X : Nat) (hp : 0 < p) (hk : 0 < k) (hr : 0 < r)
    (hx : X < p ^ k) (a : Fin p)
    (b : linnikShiftedCongruencePairs p k a.val X hp hx) :
    Finset (linnikResidueEqualPairs p k r X hp a) := by
  classical
  exact Finset.univ.filter (fun vw =>
    linnikResidueEqualPairPrefix p k r X hp hk hr hx a vw = b)

/-- Tail multiplicity above a fixed `B(p,a)` prefix. -/
noncomputable def linnikResidueCompatibleTailCount
    (p k r X : Nat) (hp : 0 < p) (hk : 0 < k) (hr : 0 < r)
    (hx : X < p ^ k) (a : Fin p)
    (b : linnikShiftedCongruencePairs p k a.val X hp hx) : Nat :=
  (linnikResidueEqualPairPrefixFiber p k r X hp hk hr hx a b).card

/-- The complete `I1(p,a)` pair count is exactly the recurrence packet over
`B(p,a)` with its compatible-tail multiplicities. -/
theorem linnikResiduePacketPairCount_eq_shiftedRecurrencePacket
    (p k r X : Nat) (hp : 0 < p) (hk : 0 < k) (hr : 0 < r)
    (hx : X < p ^ k) (a : Fin p) :
    linnikResiduePacketPairCount p k r X (k * (r - 1)) hp a =
      (linnikShiftedRecurrencePacketCount p k a.val X hp hx
        (linnikResidueCompatibleTailCount p k r X hp hk hr hx a) : Real) := by
  classical
  rw [linnikResiduePacketPairCount_eq_card_equalPairs]
  norm_cast
  unfold linnikShiftedRecurrencePacketCount
    linnikResidueCompatibleTailCount linnikResidueEqualPairPrefixFiber
  have h := Finset.sum_fiberwise
    (s := (Finset.univ : Finset (linnikResidueEqualPairs p k r X hp a)))
    (g := linnikResidueEqualPairPrefix p k r X hp hk hr hx a)
    (f := fun _vw => (1 : Nat))
  calc
    (linnikResidueEqualPairs p k r X hp a).card =
        Fintype.card (linnikResidueEqualPairs p k r X hp a) := by
      exact (Fintype.card_coe _).symm
    _ = Finset.univ.sum (fun b =>
        (Finset.univ.filter (fun vw =>
          linnikResidueEqualPairPrefix p k r X hp hk hr hx a vw = b)).card) := by
      simpa using h.symm

/-- The proved `B(p,a)` cardinality estimate bounds the actual `I1(p,a)`
pair count once every compatible tail fiber has a common bound. -/
theorem linnikResiduePacketPairCount_le_explicit
    (p k r X M : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (hr : 0 < r) (hx : X < p ^ k) (a : Fin p)
    (htail : forall b,
      linnikResidueCompatibleTailCount p k r X hp.pos hk hr hx a b <= M) :
    linnikResiduePacketPairCount p k r X (k * (r - 1)) hp.pos a <=
      ((X ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) * M : Nat) := by
  rw [linnikResiduePacketPairCount_eq_shiftedRecurrencePacket
    p k r X hp.pos hk hr hx a]
  exact_mod_cast linnikShiftedRecurrencePacketCount_le_explicit
    p k a.val X M hp hk hkp hx
      (linnikResidueCompatibleTailCount p k r X hp.pos hk hr hx a) htail

/-- The discrete distinct-prefix count now consumes the actual `B(p,a)`
estimate. Only a uniform compatible-tail bound remains. -/
theorem exists_residue_linnikModDistinctPairCount_le_explicit
    (p k r X M : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (hr : 1 < r) (hx : X < p ^ k)
    (htail : forall (a : Fin p) b,
      linnikResidueCompatibleTailCount p k r X hp.pos hk
        (lt_trans (by omega) hr) hx a b <= M) :
    exists a : Fin p,
      linnikModDistinctPacketPairCount p k r X (k * (r - 1)) hp.pos <=
        (p : Real) ^ (2 * (k * (r - 1))) *
          ((X ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) * M : Nat) := by
  have hrpos : 0 < r := lt_trans (by omega) hr
  have hL : 0 < k * (r - 1) := Nat.mul_pos hk (Nat.sub_pos_of_lt hr)
  have hres := exists_residue_linnikModDistinctPairCount_le_residuePairCount
    p k r X (k * (r - 1)) hp.pos hL
  choose a ha using hres
  refine Exists.intro a ?_
  calc
    linnikModDistinctPacketPairCount p k r X (k * (r - 1)) hp.pos <=
        (p : Real) ^ (2 * (k * (r - 1))) *
          linnikResiduePacketPairCount p k r X
            (k * (r - 1)) hp.pos a := ha
    _ <= (p : Real) ^ (2 * (k * (r - 1))) *
        ((X ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) * M : Nat) := by
      gcongr
      exact linnikResiduePacketPairCount_le_explicit
        p k r X M hp hk hkp hrpos hx a (htail a)

/-- Compatible tail pairs over one fixed `B(p,a)` prefix pair. -/
noncomputable def linnikCompatibleTailPairs
    (p k r X : Nat) (hp : 0 < p) (hx : X < p ^ k) (a : Fin p)
    (b : linnikShiftedCongruencePairs p k a.val X hp hx) :
    Finset (Prod (Fin (k * (r - 1)) -> Fin X)
      (Fin (k * (r - 1)) -> Fin X)) :=
  ((linnikResidueTailTuples p X (k * (r - 1)) hp a).product
      (linnikResidueTailTuples p X (k * (r - 1)) hp a)).filter (fun uv =>
    linnikModDistinctPacketFrequency k r X (k * (r - 1))
        (b.val.fst, uv.fst) =
      linnikModDistinctPacketFrequency k r X (k * (r - 1))
        (b.val.snd, uv.snd))

/-- Project a pair in one prefix fiber to its compatible tail pair. -/
noncomputable def linnikResiduePrefixFiberToCompatibleTails
    (p k r X : Nat) (hp : 0 < p) (hk : 0 < k) (hr : 0 < r)
    (hx : X < p ^ k) (a : Fin p)
    (b : linnikShiftedCongruencePairs p k a.val X hp hx) :
    linnikResidueEqualPairPrefixFiber p k r X hp hk hr hx a b ->
      linnikCompatibleTailPairs p k r X hp hx a b := by
  classical
  intro vw
  let z := vw.val.val
  have hzEqual := Finset.mem_filter.mp vw.val.property
  have hzPackets := Finset.mem_product.mp hzEqual.1
  have hvPacket := Finset.mem_product.mp hzPackets.1
  have hwPacket := Finset.mem_product.mp hzPackets.2
  have hprefix := congrArg Subtype.val (Finset.mem_filter.mp vw.property).2
  refine Subtype.mk (z.fst.snd, z.snd.snd) ?_
  apply Finset.mem_filter.mpr
  constructor
  next => exact Finset.mem_product.mpr (And.intro hvPacket.2 hwPacket.2)
  next =>
    have hm : z.fst.fst = b.val.fst := congrArg Prod.fst hprefix
    have hn : z.snd.fst = b.val.snd := congrArg Prod.snd hprefix
    change linnikModDistinctPacketFrequency k r X (k * (r - 1))
        (b.val.fst, z.fst.snd) =
      linnikModDistinctPacketFrequency k r X (k * (r - 1))
        (b.val.snd, z.snd.snd)
    rw [<- hm, <- hn]
    exact hzEqual.2

/-- The tail projection is injective because its prefix is fixed by the
fiber index. -/
theorem linnikResiduePrefixFiberToCompatibleTails_injective
    (p k r X : Nat) (hp : 0 < p) (hk : 0 < k) (hr : 0 < r)
    (hx : X < p ^ k) (a : Fin p)
    (b : linnikShiftedCongruencePairs p k a.val X hp hx) :
    Function.Injective
      (linnikResiduePrefixFiberToCompatibleTails
        p k r X hp hk hr hx a b) := by
  classical
  intro u v huv
  have htails := congrArg Subtype.val huv
  have huprefix := congrArg Subtype.val (Finset.mem_filter.mp u.property).2
  have hvprefix := congrArg Subtype.val (Finset.mem_filter.mp v.property).2
  have hprefix := huprefix.trans hvprefix.symm
  change (u.val.val.fst.fst, u.val.val.snd.fst) =
    (v.val.val.fst.fst, v.val.val.snd.fst) at hprefix
  change (u.val.val.fst.snd, u.val.val.snd.snd) =
    (v.val.val.fst.snd, v.val.val.snd.snd) at htails
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  next =>
    apply Prod.ext
    next => exact congrArg (fun z => z.fst) hprefix
    next => exact congrArg (fun z => z.fst) htails
  next =>
    apply Prod.ext
    next => exact congrArg (fun z => z.snd) hprefix
    next => exact congrArg (fun z => z.snd) htails

/-- Each compatible-tail multiplicity is bounded by the exact finite set of
tail pairs satisfying the residual frequency equation. -/
theorem linnikResidueCompatibleTailCount_le_card_compatibleTailPairs
    (p k r X : Nat) (hp : 0 < p) (hk : 0 < k) (hr : 0 < r)
    (hx : X < p ^ k) (a : Fin p)
    (b : linnikShiftedCongruencePairs p k a.val X hp hx) :
    linnikResidueCompatibleTailCount p k r X hp hk hr hx a b <=
      (linnikCompatibleTailPairs p k r X hp hx a b).card := by
  unfold linnikResidueCompatibleTailCount
  rw [<- Fintype.card_coe]
  rw [<- Fintype.card_coe]
  exact Fintype.card_le_of_injective
    (linnikResiduePrefixFiberToCompatibleTails p k r X hp hk hr hx a b)
    (linnikResiduePrefixFiberToCompatibleTails_injective
      p k r X hp hk hr hx a b)

end Finset
