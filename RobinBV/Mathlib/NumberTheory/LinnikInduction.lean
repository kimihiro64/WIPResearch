/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.NumberTheory.LinnikLocal

/-!
# Finite counting identities for Linnik's VMVT induction

This module converts the fixed-power-sum collision fibers from
LinnikLocal into the repeated-coordinate pair counts used by the
collision branch of Linnik's induction.
-/

set_option autoImplicit false

namespace Finset

/-- The vector of positive power sums attached to one full-modulus tuple. -/
def linnikPowerSumData (p k : Nat) (m : Fin k -> Fin (p ^ k)) : Fin k -> Nat :=
  fun j => Finset.univ.sum fun r : Fin k => (m r).val ^ (j.val + 1)

/-- First tuples selected from an arbitrary finite range, with pairwise
distinct reductions modulo p. Retaining the finite range is what later
specializes the first-tuple factor to the interval count x^k. -/
def linnikFirstPacket (p k : Nat)
    (S : Finset (Fin k -> Fin (p ^ k))) : Type :=
  {m : S // Function.Injective (fun r : Fin k => (m.val r).val % p)}

/-- The selected first-tuple packet is finite. -/
noncomputable instance linnikFirstPacketFintype (p k : Nat)
    (S : Finset (Fin k -> Fin (p ^ k))) :
    Fintype (linnikFirstPacket p k S) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The oriented pair packet whose second tuple satisfies all of Linnik's
lower-modulus power-sum congruences attached to the selected first tuple. -/
def linnikPairPacket (p k : Nat)
    (S : Finset (Fin k -> Fin (p ^ k))) : Type :=
  Sigma fun m : linnikFirstPacket p k S =>
    linnikCongruenceSolutions p k (linnikPowerSumData p k m.val.val)

/-- The oriented pair packet is finite. -/
noncomputable instance linnikPairPacketFintype (p k : Nat)
    (S : Finset (Fin k -> Fin (p ^ k))) :
    Fintype (linnikPairPacket p k S) := by
  unfold linnikPairPacket
  infer_instance

/-- The finite pair-packet estimate used in the distinct-residue branch of
Linnik's induction. The arbitrary first-tuple range is retained exactly. -/
theorem card_linnikPairPacket_le
    (p k : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (S : Finset (Fin k -> Fin (p ^ k))) :
    Fintype.card (linnikPairPacket p k S) <=
      S.card * (k.factorial * p ^ (k * (k - 1) / 2)) := by
  classical
  have hfirst : Fintype.card (linnikFirstPacket p k S) <= S.card := by
    calc
      Fintype.card (linnikFirstPacket p k S) <= Fintype.card S :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = S.card := by simp
  calc
    Fintype.card (linnikPairPacket p k S) =
        Finset.univ.sum (fun m : linnikFirstPacket p k S =>
          Fintype.card (linnikCongruenceSolutions p k
            (linnikPowerSumData p k m.val.val))) := by
      unfold linnikPairPacket
      exact Fintype.card_sigma
    _ <= Finset.univ.sum (fun _m : linnikFirstPacket p k S =>
        k.factorial * p ^ (k * (k - 1) / 2)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact card_linnikCongruenceSolutions_le p k hp hk hkp
        (linnikPowerSumData p k m.val.val)
    _ = Fintype.card (linnikFirstPacket p k S) *
        (k.factorial * p ^ (k * (k - 1) / 2)) := by simp
    _ <= S.card * (k.factorial * p ^ (k * (k - 1) / 2)) :=
      Nat.mul_le_mul_right _ hfirst

/-- The residue of the shifted interval value m+1-a modulo q. Using ZMod
here preserves negative shifts without natural-number truncation. -/
def linnikShiftedResidue (q a x : Nat) (hq : 0 < q) (m : Fin x) : Fin q := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  exact Fin.mk ((((m.val + 1 : Nat) : ZMod q) - (a : ZMod q)).val)
    (ZMod.val_lt _)

/-- Reduction modulo q is injective on any shifted interval of length less
than q. -/
theorem linnikShiftedResidue_injective (q a x : Nat) (hq : 0 < q)
    (hxq : x < q) :
    Function.Injective (linnikShiftedResidue q a x hq) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  intro m n hmn
  apply Fin.ext
  have hval :
      ((((m.val + 1 : Nat) : ZMod q) - (a : ZMod q)).val) =
        ((((n.val + 1 : Nat) : ZMod q) - (a : ZMod q)).val) := by
    exact congrArg Fin.val hmn
  have hz :
      (((m.val + 1 : Nat) : ZMod q) - (a : ZMod q)) =
        (((n.val + 1 : Nat) : ZMod q) - (a : ZMod q)) :=
    ZMod.val_injective q hval
  have hcast : ((m.val + 1 : Nat) : ZMod q) =
      ((n.val + 1 : Nat) : ZMod q) := sub_left_inj.mp hz
  have hm : m.val + 1 < q :=
    lt_of_le_of_lt (Nat.succ_le_iff.mpr m.isLt) hxq
  have hn : n.val + 1 < q :=
    lt_of_le_of_lt (Nat.succ_le_iff.mpr n.isLt) hxq
  have hv := congrArg ZMod.val hcast
  have hsucc : m.val + 1 = n.val + 1 := by
    simpa only [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hn] using hv
  exact Nat.add_right_cancel hsucc

/-- Coordinatewise shifted reduction of an interval tuple modulo p^k. -/
def linnikShiftedResidueVector (p k a x : Nat) (hp : 0 < p)
    (m : Fin k -> Fin x) : Fin k -> Fin (p ^ k) :=
  fun i => linnikShiftedResidue (p ^ k) a x (Nat.pow_pos hp) (m i)

/-- Shifted reduction is injective on interval tuples when x is less than
p^k. -/
theorem linnikShiftedResidueVector_injective (p k a x : Nat) (hp : 0 < p)
    (hx : x < p ^ k) :
    Function.Injective (linnikShiftedResidueVector p k a x hp) := by
  intro m n hmn
  funext i
  apply linnikShiftedResidue_injective (p ^ k) a x (Nat.pow_pos hp) hx
  exact congrFun hmn i

/-- The shifted-reduction embedding of k-tuples from the interval 1 through
x into full-modulus residue tuples. -/
noncomputable def linnikShiftedResidueVectorEmbedding (p k a x : Nat)
    (hp : 0 < p) (hx : x < p ^ k) :
    Function.Embedding (Fin k -> Fin x) (Fin k -> Fin (p ^ k)) :=
  { toFun := linnikShiftedResidueVector p k a x hp
    inj' := linnikShiftedResidueVector_injective p k a x hp hx }

/-- The exact finite range of shifted interval tuples modulo p^k. -/
noncomputable def linnikShiftedFirstRange (p k a x : Nat) (hp : 0 < p)
    (hx : x < p ^ k) : Finset (Fin k -> Fin (p ^ k)) :=
  Finset.univ.map (linnikShiftedResidueVectorEmbedding p k a x hp hx)

/-- The shifted first-tuple range retains exactly x^k elements. -/
theorem card_linnikShiftedFirstRange (p k a x : Nat) (hp : 0 < p)
    (hx : x < p ^ k) :
    (linnikShiftedFirstRange p k a x hp hx).card = x ^ k := by
  rw [linnikShiftedFirstRange, Finset.card_map, Finset.card_univ,
    Fintype.card_fun]
  simp

/-- Linnik's pair-packet bound specialized to shifted tuples from the
interval 1 through x. -/
theorem card_linnikShiftedPairPacket_le
    (p k a x : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (hx : x < p ^ k) :
    Fintype.card (linnikPairPacket p k
      (linnikShiftedFirstRange p k a x hp.pos hx)) <=
        x ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) := by
  calc
    Fintype.card (linnikPairPacket p k
        (linnikShiftedFirstRange p k a x hp.pos hx)) <=
          (linnikShiftedFirstRange p k a x hp.pos hx).card *
            (k.factorial * p ^ (k * (k - 1) / 2)) :=
      card_linnikPairPacket_le p k hp hk hkp _
    _ = x ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) := by
      rw [card_linnikShiftedFirstRange]

/-- The finite B(p,a) pair space from Linnik's distinct-residue branch.
Both tuples lie in the interval 1 through x, both have distinct reductions
modulo p, and their shifted power sums agree modulo every p^(j+1). -/
def linnikShiftedCongruencePairs (p k a x : Nat) (hp : 0 < p)
    (hx : x < p ^ k) : Type :=
  {mn : Prod (Fin k -> Fin x) (Fin k -> Fin x) //
    Function.Injective (fun r : Fin k =>
      ((linnikShiftedResidueVector p k a x hp mn.fst) r).val % p) /\
    Function.Injective (fun r : Fin k =>
      ((linnikShiftedResidueVector p k a x hp mn.snd) r).val % p) /\
    forall j : Fin k, Nat.ModEq (p ^ (j.val + 1))
      (Finset.univ.sum fun r : Fin k =>
        ((linnikShiftedResidueVector p k a x hp mn.snd) r).val ^
          (j.val + 1))
      (Finset.univ.sum fun r : Fin k =>
        ((linnikShiftedResidueVector p k a x hp mn.fst) r).val ^
          (j.val + 1))}

/-- The shifted congruence-pair space is finite. -/
noncomputable instance linnikShiftedCongruencePairsFintype
    (p k a x : Nat) (hp : 0 < p) (hx : x < p ^ k) :
    Fintype (linnikShiftedCongruencePairs p k a x hp hx) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Map a source B(p,a) pair into the shifted local pair packet. -/
noncomputable def linnikShiftedCongruencePairToPacket
    (p k a x : Nat) (hp : p.Prime) (hx : x < p ^ k) :
    linnikShiftedCongruencePairs p k a x hp.pos hx ->
      linnikPairPacket p k
        (linnikShiftedFirstRange p k a x hp.pos hx) := by
  intro mn
  let fm := linnikShiftedResidueVector p k a x hp.pos mn.val.fst
  let fn := linnikShiftedResidueVector p k a x hp.pos mn.val.snd
  have hmem : Membership.mem
      (linnikShiftedFirstRange p k a x hp.pos hx) fm := by
    simp only [linnikShiftedFirstRange, Finset.mem_map, Finset.mem_univ,
      true_and]
    exact Exists.intro mn.val.fst rfl
  let first : linnikFirstPacket p k
      (linnikShiftedFirstRange p k a x hp.pos hx) :=
    Subtype.mk (Subtype.mk fm hmem) mn.property.1
  have hmod : forall j : Fin k, Nat.ModEq (p ^ (j.val + 1))
      (Finset.univ.sum fun r : Fin k => (fn r).val ^ (j.val + 1))
      ((linnikPowerSumData p k first.val.val) j) := by
    intro j
    simpa only [fn, fm, first, linnikPowerSumData] using mn.property.2.2 j
  let second : linnikCongruenceSolutions p k
      (linnikPowerSumData p k first.val.val) :=
    Subtype.mk fn (And.intro mn.property.2.1 hmod)
  exact Sigma.mk first second

/-- The map from the source B(p,a) pair space to the local packet is
injective; both original interval tuples are recovered from shifted
reduction because x is less than p^k. -/
theorem linnikShiftedCongruencePairToPacket_injective
    (p k a x : Nat) (hp : p.Prime) (hx : x < p ^ k) :
    Function.Injective
      (linnikShiftedCongruencePairToPacket p k a x hp hx) := by
  intro u v huv
  apply Subtype.ext
  apply Prod.ext
  next =>
    apply linnikShiftedResidueVector_injective p k a x hp.pos hx
    exact congrArg (fun z : linnikPairPacket p k
      (linnikShiftedFirstRange p k a x hp.pos hx) => z.fst.val.val) huv
  next =>
    apply linnikShiftedResidueVector_injective p k a x hp.pos hx
    exact congrArg (fun z : linnikPairPacket p k
      (linnikShiftedFirstRange p k a x hp.pos hx) => z.snd.val) huv

/-- The exact B(p,a) cardinality estimate used in Linnik's r>1 induction. -/
theorem card_linnikShiftedCongruencePairs_le
    (p k a x : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (hx : x < p ^ k) :
    Fintype.card (linnikShiftedCongruencePairs p k a x hp.pos hx) <=
      x ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) := by
  calc
    Fintype.card (linnikShiftedCongruencePairs p k a x hp.pos hx) <=
        Fintype.card (linnikPairPacket p k
          (linnikShiftedFirstRange p k a x hp.pos hx)) :=
      Fintype.card_le_of_injective
        (linnikShiftedCongruencePairToPacket p k a x hp hx)
        (linnikShiftedCongruencePairToPacket_injective p k a x hp hx)
    _ <= x ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) :=
      card_linnikShiftedPairPacket_le p k a x hp hk hkp hx

/-- Casting a full-modulus shifted residue to a lower power of p recovers
the literal shifted interval value m+1-a in that lower residue ring. -/
theorem linnikShiftedResidue_cast_lower (p k a x : Nat) (hp : 0 < p)
    (m : Fin k -> Fin x) (r j : Fin k) :
    (((linnikShiftedResidueVector p k a x hp m r).val : Nat) :
        ZMod (p ^ (j.val + 1))) =
      (((m r).val + 1 : Nat) : ZMod (p ^ (j.val + 1))) -
        (a : ZMod (p ^ (j.val + 1))) := by
  letI : NeZero (p ^ k) :=
    NeZero.mk (Nat.ne_of_gt (Nat.pow_pos hp))
  letI : NeZero (p ^ (j.val + 1)) :=
    NeZero.mk (Nat.ne_of_gt (Nat.pow_pos hp))
  have hdvd : Dvd.dvd (p ^ (j.val + 1)) (p ^ k) := by
    refine Dvd.intro (p ^ (k - (j.val + 1))) ?_
    rw [Nat.mul_comm]
    exact lower_choice_modulus_product p k j
  let z := linnikShiftedResidueVector p k a x hp m r
  have hfull : ((z.val : Nat) : ZMod (p ^ k)) =
      (((m r).val + 1 : Nat) : ZMod (p ^ k)) -
        (a : ZMod (p ^ k)) := by
    change ((((((m r).val + 1 : Nat) : ZMod (p ^ k)) -
      (a : ZMod (p ^ k))).val : Nat) : ZMod (p ^ k)) = _
    exact ZMod.natCast_zmod_val _
  have hmap := congrArg
    (ZMod.castHom hdvd (ZMod (p ^ (j.val + 1)))) hfull
  simpa only [z, ZMod.castHom_apply, map_sub, map_natCast] using hmap

/-- The lower-modulus cast of an encoded shifted power sum is the literal
power sum of the shifted interval values in the lower residue ring. -/
theorem linnikShiftedPowerSum_cast_lower (p k a x : Nat) (hp : 0 < p)
    (m : Fin k -> Fin x) (j : Fin k) :
    ((Finset.univ.sum fun r : Fin k =>
        ((linnikShiftedResidueVector p k a x hp m r).val : Nat) ^
          (j.val + 1) : Nat) : ZMod (p ^ (j.val + 1))) =
      Finset.univ.sum (fun r : Fin k =>
        ((((m r).val + 1 : Nat) : ZMod (p ^ (j.val + 1))) -
          (a : ZMod (p ^ (j.val + 1)))) ^ (j.val + 1)) := by
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Nat.cast_pow]
  rw [linnikShiftedResidue_cast_lower p k a x hp m r j]

/-- The encoded congruence in linnikShiftedCongruencePairs is exactly the
source congruence between the literal shifted power sums modulo p^(j+1). -/
theorem linnikShiftedPowerSum_modEq_iff
    (p k a x : Nat) (hp : 0 < p)
    (m n : Fin k -> Fin x) (j : Fin k) :
    Nat.ModEq (p ^ (j.val + 1))
      (Finset.univ.sum fun r : Fin k =>
        ((linnikShiftedResidueVector p k a x hp n r).val : Nat) ^
          (j.val + 1))
      (Finset.univ.sum fun r : Fin k =>
        ((linnikShiftedResidueVector p k a x hp m r).val : Nat) ^
          (j.val + 1)) <->
      Finset.univ.sum (fun r : Fin k =>
        ((((n r).val + 1 : Nat) : ZMod (p ^ (j.val + 1))) -
          (a : ZMod (p ^ (j.val + 1)))) ^ (j.val + 1)) =
      Finset.univ.sum (fun r : Fin k =>
        ((((m r).val + 1 : Nat) : ZMod (p ^ (j.val + 1))) -
          (a : ZMod (p ^ (j.val + 1)))) ^ (j.val + 1)) := by
  rw [<- linnikShiftedPowerSum_cast_lower p k a x hp n j]
  rw [<- linnikShiftedPowerSum_cast_lower p k a x hp m j]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).symm

/-- The vector of the first k power sums of a length-m interval tuple. -/
def linnikMomentPowerSumData (k m X : Nat) (v : Fin m -> Fin X) :
    Fin k -> Nat :=
  fun j => Finset.univ.sum fun q : Fin m => (v q).val ^ (j.val + 1)

/-- The first k coordinates of a length-k*r tuple. -/
def linnikMomentPrefix (k r X : Nat) (hr : 0 < r)
    (v : Fin (k * r) -> Fin X) : Fin k -> Fin X :=
  fun i => v (Fin.castLE (Nat.le_mul_of_pos_right k hr) i)

/-- The finite tuple fiber with one fixed vector of power sums. -/
noncomputable def linnikMomentFiber (k r X : Nat) (h : Fin k -> Nat) :
    Finset (Fin (k * r) -> Fin X) :=
  Finset.univ.filter (fun v =>
    linnikMomentPowerSumData k (k * r) X v = h)

/-- The part of a fixed power-sum fiber whose first k coordinates collide. -/
noncomputable def linnikCollisionFiber (k r X : Nat) (hr : 0 < r)
    (h : Fin k -> Nat) : Finset (Fin (k * r) -> Fin X) :=
  (linnikMomentFiber k r X h).filter
    (fun v => Not (Function.Injective (linnikMomentPrefix k r X hr v)))

/-- Ordered distinct index pairs among the first k coordinates. -/
noncomputable def linnikCollisionIndexPairs (k : Nat) :
    Finset (Prod (Fin k) (Fin k)) :=
  ((Finset.univ : Finset (Fin k)).product Finset.univ).filter
    (fun ij => Not (ij.fst = ij.snd))

/-- The fixed power-sum fiber in which one specified pair of prefix
coordinates is equal. -/
noncomputable def linnikFixedCollisionFiber (k r X : Nat) (hr : 0 < r)
    (h : Fin k -> Nat) (ij : Prod (Fin k) (Fin k)) :
    Finset (Fin (k * r) -> Fin X) :=
  (linnikMomentFiber k r X h).filter (fun v =>
    linnikMomentPrefix k r X hr v ij.fst =
      linnikMomentPrefix k r X hr v ij.snd)

/-- Every collision in the first k coordinates is witnessed by an ordered
pair of distinct prefix indices. -/
theorem linnikCollisionFiber_subset_biUnion (k r X : Nat) (hr : 0 < r)
    (h : Fin k -> Nat) :
    linnikCollisionFiber k r X hr h <=
      (linnikCollisionIndexPairs k).biUnion
        (linnikFixedCollisionFiber k r X hr h) := by
  intro v hv
  have hparts := Finset.mem_filter.mp hv
  have hex := Function.not_injective_iff.mp hparts.2
  cases hex with
  | intro i hexi =>
    cases hexi with
    | intro j hij =>
      apply Finset.mem_biUnion.mpr
      refine Exists.intro (i, j) ?_
      constructor
      next =>
        apply Finset.mem_filter.mpr
        constructor
        next =>
          exact Finset.mem_product.mpr (And.intro (Finset.mem_univ i)
            (Finset.mem_univ j))
        next => exact hij.2
      next =>
        apply Finset.mem_filter.mpr
        exact And.intro hparts.1 hij.1

/-- The fixed-h collision count is bounded by the sum of its fixed-index
collision fibers. This is the finite union bound underlying R2(h). -/
theorem card_linnikCollisionFiber_le_sum_fixed
    (k r X : Nat) (hr : 0 < r) (h : Fin k -> Nat) :
    (linnikCollisionFiber k r X hr h).card <=
      Finset.sum (linnikCollisionIndexPairs k) (fun ij =>
        (linnikFixedCollisionFiber k r X hr h ij).card) := by
  calc
    (linnikCollisionFiber k r X hr h).card <=
        ((linnikCollisionIndexPairs k).biUnion
          (linnikFixedCollisionFiber k r X hr h)).card :=
      Finset.card_le_card (linnikCollisionFiber_subset_biUnion k r X hr h)
    _ <= Finset.sum (linnikCollisionIndexPairs k) (fun ij =>
        (linnikFixedCollisionFiber k r X hr h ij).card) := by
      simpa only [Finset.sum_filter] using
        (Finset.card_biUnion_le (s := linnikCollisionIndexPairs k)
          (t := linnikFixedCollisionFiber k r X hr h))

/-- The largest fixed-index collision fiber for one power-sum datum. -/
noncomputable def linnikMaxFixedCollisionCard
    (k r X : Nat) (hr : 0 < r) (h : Fin k -> Nat) : Nat :=
  (linnikCollisionIndexPairs k).sup (fun ij =>
    (linnikFixedCollisionFiber k r X hr h ij).card)

/-- There are at most k^2 ordered distinct prefix-index pairs. -/
theorem card_linnikCollisionIndexPairs_le_sq (k : Nat) :
    (linnikCollisionIndexPairs k).card <= k ^ 2 := by
  calc
    (linnikCollisionIndexPairs k).card <=
        ((Finset.univ : Finset (Fin k)).product Finset.univ).card := by
      apply Finset.card_le_card
      intro ij hij
      exact (Finset.mem_filter.mp hij).1
    _ = k ^ 2 := by simp [Nat.pow_two]

/-- The fixed-h collision fiber is bounded by the number of candidate
coordinate pairs times the largest fixed-pair fiber. -/
theorem card_linnikCollisionFiber_le_card_mul_max
    (k r X : Nat) (hr : 0 < r) (h : Fin k -> Nat) :
    (linnikCollisionFiber k r X hr h).card <=
      (linnikCollisionIndexPairs k).card *
        linnikMaxFixedCollisionCard k r X hr h := by
  calc
    (linnikCollisionFiber k r X hr h).card <=
        ((linnikCollisionIndexPairs k).biUnion
          (linnikFixedCollisionFiber k r X hr h)).card :=
      Finset.card_le_card (linnikCollisionFiber_subset_biUnion k r X hr h)
    _ <= (linnikCollisionIndexPairs k).card *
        linnikMaxFixedCollisionCard k r X hr h := by
      apply Finset.card_biUnion_le_card_mul
      intro ij hij
      exact Finset.le_sup
        (f := fun uv => (linnikFixedCollisionFiber k r X hr h uv).card) hij

/-- The source collision coefficient may be bounded uniformly by k^2. -/
theorem card_linnikCollisionFiber_le_sq_mul_max
    (k r X : Nat) (hr : 0 < r) (h : Fin k -> Nat) :
    (linnikCollisionFiber k r X hr h).card <=
      k ^ 2 * linnikMaxFixedCollisionCard k r X hr h := by
  exact le_trans (card_linnikCollisionFiber_le_card_mul_max k r X hr h)
    (Nat.mul_le_mul_right _ (card_linnikCollisionIndexPairs_le_sq k))

/-- Finite Cauchy-Schwarz for natural-valued sums. -/
theorem nat_sum_sq_le_card_mul_sum_sq {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (f : alpha -> Nat) :
    (Finset.sum s f) ^ 2 <=
      s.card * Finset.sum s (fun i => (f i) ^ 2) := by
  have hr := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun _i => (1 : Int)) (fun i => (f i : Int))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hr
  exact_mod_cast hr

/-- Squaring the collision union bound costs only the number of candidate
coordinate pairs, not its square. -/
theorem sq_card_linnikCollisionFiber_le_sq_mul_sum_fixed
    (k r X : Nat) (hr : 0 < r) (h : Fin k -> Nat) :
    (linnikCollisionFiber k r X hr h).card ^ 2 <=
      k ^ 2 * Finset.sum (linnikCollisionIndexPairs k) (fun ij =>
        (linnikFixedCollisionFiber k r X hr h ij).card ^ 2) := by
  calc
    (linnikCollisionFiber k r X hr h).card ^ 2 <=
        (Finset.sum (linnikCollisionIndexPairs k) (fun ij =>
          (linnikFixedCollisionFiber k r X hr h ij).card)) ^ 2 :=
      Nat.pow_le_pow_left
        (card_linnikCollisionFiber_le_sum_fixed k r X hr h) 2
    _ <= (linnikCollisionIndexPairs k).card *
        Finset.sum (linnikCollisionIndexPairs k) (fun ij =>
          (linnikFixedCollisionFiber k r X hr h ij).card ^ 2) :=
      nat_sum_sq_le_card_mul_sum_sq _ _
    _ <= k ^ 2 * Finset.sum (linnikCollisionIndexPairs k) (fun ij =>
        (linnikFixedCollisionFiber k r X hr h ij).card ^ 2) :=
      Nat.mul_le_mul_right _ (card_linnikCollisionIndexPairs_le_sq k)

/-- The finite set of power-sum data attained by length-k*r interval
tuples. This is the exact summation domain for S1 and S2. -/
noncomputable def linnikMomentPowerSumRange (k r X : Nat) :
    Finset (Fin k -> Nat) :=
  Finset.univ.image (linnikMomentPowerSumData k (k * r) X)

/-- The complete collision square sum S2 is bounded by the sum of the
fixed-index collision square sums, with the explicit k^2 coefficient. -/
theorem sum_sq_linnikCollisionFiber_le_sq_mul_sum_fixed
    (k r X : Nat) (hr : 0 < r) :
    Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
      (linnikCollisionFiber k r X hr h).card ^ 2) <=
      k ^ 2 * Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
        Finset.sum (linnikCollisionIndexPairs k) (fun ij =>
          (linnikFixedCollisionFiber k r X hr h ij).card ^ 2)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  exact sq_card_linnikCollisionFiber_le_sq_mul_sum_fixed k r X hr h

/-- The sum of squared fiber cardinalities equals the sum, over source
points, of the cardinality of the fiber containing that point. -/
theorem sum_sq_fiber_card_eq_sum_fiber_card
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    [Fintype beta] (s : Finset alpha) (g : alpha -> beta) :
    Finset.univ.sum (fun b : beta =>
      (s.filter (fun a => g a = b)).card ^ 2) =
      s.sum (fun a => (s.filter (fun x => g x = g a)).card) := by
  have h := Finset.sum_fiberwise s g
    (fun a => (s.filter (fun x => g x = g a)).card)
  rw [<- h]
  apply Finset.sum_congr rfl
  intro b hb
  have hinner :
      (s.filter (fun a => g a = b)).sum
          (fun a => (s.filter (fun x => g x = g a)).card) =
        (s.filter (fun a => g a = b)).sum
          (fun _a => (s.filter (fun x => g x = b)).card) := by
    apply Finset.sum_congr rfl
    intro a ha
    have hab : g a = b := (Finset.mem_filter.mp ha).2
    rw [hab]
  rw [hinner]
  simp [Nat.pow_two]

/-- All length-k*r tuples with one specified collision among the first k
coordinates. -/
noncomputable def linnikFixedCollisionTuples
    (k r X : Nat) (hr : 0 < r) (ij : Prod (Fin k) (Fin k)) :
    Finset (Fin (k * r) -> Fin X) :=
  Finset.univ.filter (fun v =>
    linnikMomentPrefix k r X hr v ij.fst =
      linnikMomentPrefix k r X hr v ij.snd)

/-- The attained power-sum datum of a tuple, regarded as an element of the
exact finite power-sum range. -/
noncomputable def linnikMomentPowerSumValue
    (k r X : Nat) (v : Fin (k * r) -> Fin X) :
    linnikMomentPowerSumRange k r X :=
  Subtype.mk (linnikMomentPowerSumData k (k * r) X v) (by
    apply Finset.mem_image.mpr
    exact Exists.intro v (And.intro (Finset.mem_univ v) rfl))

/-- Filtering the fixed-collision tuple set by an attained power-sum value
recovers the fixed collision fiber with that value. -/
theorem linnikFixedCollisionTuples_filter_value
    (k r X : Nat) (hr : 0 < r)
    (ij : Prod (Fin k) (Fin k))
    (h : linnikMomentPowerSumRange k r X) :
    (linnikFixedCollisionTuples k r X hr ij).filter
        (fun v => linnikMomentPowerSumValue k r X v = h) =
      linnikFixedCollisionFiber k r X hr h.val ij := by
  ext v
  constructor
  next =>
    intro hv
    have hvparts := Finset.mem_filter.mp hv
    have hfixed := Finset.mem_filter.mp hvparts.1
    apply Finset.mem_filter.mpr
    constructor
    next =>
      apply Finset.mem_filter.mpr
      exact And.intro (Finset.mem_univ v)
        (congrArg Subtype.val hvparts.2)
    next => exact hfixed.2
  next =>
    intro hv
    have hvparts := Finset.mem_filter.mp hv
    have hdata := Finset.mem_filter.mp hvparts.1
    apply Finset.mem_filter.mpr
    constructor
    next =>
      apply Finset.mem_filter.mpr
      exact And.intro (Finset.mem_univ v) hvparts.2
    next =>
      apply Subtype.ext
      exact hdata.2

/-- The fixed-pair square sum is exactly the repeated-coordinate
pointwise fiber count. This is the finite counting identity consumed by
the Holder step in the collision branch. -/
theorem sum_sq_fixedCollisionFiber_eq_pointwise
    (k r X : Nat) (hr : 0 < r)
    (ij : Prod (Fin k) (Fin k)) :
    Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
        (linnikFixedCollisionFiber k r X hr h ij).card ^ 2) =
      (linnikFixedCollisionTuples k r X hr ij).sum (fun v =>
        (linnikFixedCollisionFiber k r X hr
          (linnikMomentPowerSumData k (k * r) X v) ij).card) := by
  let A := linnikFixedCollisionTuples k r X hr ij
  let g := linnikMomentPowerSumValue k r X
  calc
    Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
        (linnikFixedCollisionFiber k r X hr h ij).card ^ 2) =
        Finset.univ.sum (fun h : linnikMomentPowerSumRange k r X =>
          (linnikFixedCollisionFiber k r X hr h.val ij).card ^ 2) := by
      exact (Finset.sum_coe_sort _ _).symm
    _ = Finset.univ.sum (fun h : linnikMomentPowerSumRange k r X =>
        (A.filter (fun v => g v = h)).card ^ 2) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [linnikFixedCollisionTuples_filter_value]
    _ = A.sum (fun v => (A.filter (fun w => g w = g v)).card) :=
      sum_sq_fiber_card_eq_sum_fiber_card A g
    _ = (linnikFixedCollisionTuples k r X hr ij).sum (fun v =>
        (linnikFixedCollisionFiber k r X hr
          (linnikMomentPowerSumData k (k * r) X v) ij).card) := by
      apply Finset.sum_congr rfl
      intro v hv
      change (A.filter (fun w => g w = g v)).card = _
      rw [linnikFixedCollisionTuples_filter_value]
      rfl

/-- A filtered Cartesian-product count is the sum of the corresponding
one-sided filtered cardinalities. -/
theorem card_filter_product_eq_sum_filter_card
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (s : Finset alpha) (t : Finset beta) (P : alpha -> beta -> Prop)
    [DecidablePred (fun z : Prod alpha beta => P z.fst z.snd)]
    [DecidableRel P] :
    ((s.product t).filter (fun z => P z.fst z.snd)).card =
      s.sum (fun a => (t.filter (fun b => P a b)).card) := by
  rw [Finset.product_eq_sprod]
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.card_filter]

/-- The actual repeated-coordinate pair count for one specified collision
among the first k coordinates. -/
noncomputable def linnikFixedCollisionPairCount
    (k r X : Nat) (hr : 0 < r) (ij : Prod (Fin k) (Fin k)) : Nat :=
  let A := linnikFixedCollisionTuples k r X hr ij
  ((A.product A).filter (fun vw =>
    linnikMomentPowerSumValue k r X vw.snd =
      linnikMomentPowerSumValue k r X vw.fst)).card

/-- The repeated-coordinate pair count is the pointwise fiber count. -/
theorem linnikFixedCollisionPairCount_eq_pointwise
    (k r X : Nat) (hr : 0 < r)
    (ij : Prod (Fin k) (Fin k)) :
    linnikFixedCollisionPairCount k r X hr ij =
      (linnikFixedCollisionTuples k r X hr ij).sum (fun v =>
        (linnikFixedCollisionFiber k r X hr
          (linnikMomentPowerSumData k (k * r) X v) ij).card) := by
  let A := linnikFixedCollisionTuples k r X hr ij
  calc
    linnikFixedCollisionPairCount k r X hr ij =
        A.sum (fun v => (A.filter (fun w =>
          linnikMomentPowerSumValue k r X w =
            linnikMomentPowerSumValue k r X v)).card) := by
      unfold linnikFixedCollisionPairCount
      exact card_filter_product_eq_sum_filter_card
        (s := A) (t := A)
        (P := fun v w => linnikMomentPowerSumValue k r X w =
          linnikMomentPowerSumValue k r X v)
    _ = (linnikFixedCollisionTuples k r X hr ij).sum (fun v =>
        (linnikFixedCollisionFiber k r X hr
          (linnikMomentPowerSumData k (k * r) X v) ij).card) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [linnikFixedCollisionTuples_filter_value]
      rfl

/-- The fixed-pair square sum is exactly the actual repeated-coordinate
pair count. -/
theorem sum_sq_fixedCollisionFiber_eq_pairCount
    (k r X : Nat) (hr : 0 < r)
    (ij : Prod (Fin k) (Fin k)) :
    Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
        (linnikFixedCollisionFiber k r X hr h ij).card ^ 2) =
      linnikFixedCollisionPairCount k r X hr ij := by
  exact (sum_sq_fixedCollisionFiber_eq_pointwise k r X hr ij).trans
    (linnikFixedCollisionPairCount_eq_pointwise k r X hr ij).symm

/-- A uniform digit ceiling for every attained Vinogradov power-sum vector. -/
noncomputable def linnikMomentDigitCeiling (k r X : Nat) : Nat :=
  (linnikMomentPowerSumRange k r X).sup (fun h =>
    (Finset.univ : Finset (Fin k)).sup h)

/-- A mixed-radix base strictly larger than every attained power-sum digit. -/
noncomputable def linnikMomentFrequencyBase (k r X : Nat) : Nat :=
  linnikMomentDigitCeiling k r X + 2

/-- Every component of an attained power-sum vector is below the encoding base. -/
theorem linnikMomentPowerSumValue_lt_base (k r X : Nat)
    (v : Fin (k * r) -> Fin X) (j : Fin k) :
    (linnikMomentPowerSumValue k r X v).val j <
      linnikMomentFrequencyBase k r X := by
  have hj :
      (linnikMomentPowerSumValue k r X v).val j <=
        (Finset.univ : Finset (Fin k)).sup
          (linnikMomentPowerSumValue k r X v).val :=
    Finset.le_sup (f := (linnikMomentPowerSumValue k r X v).val)
      (Finset.mem_univ j)
  have hrange :
      (Finset.univ : Finset (Fin k)).sup
          (linnikMomentPowerSumValue k r X v).val <=
        linnikMomentDigitCeiling k r X := by
    unfold linnikMomentDigitCeiling
    exact Finset.le_sup
      (s := linnikMomentPowerSumRange k r X)
      (f := fun h : Fin k -> Nat =>
        (Finset.univ : Finset (Fin k)).sup h)
      (b := (linnikMomentPowerSumValue k r X v).val)
      (linnikMomentPowerSumValue k r X v).property
  exact lt_of_le_of_lt (le_trans hj hrange) (by
    unfold linnikMomentFrequencyBase linnikMomentDigitCeiling
    omega)

/-- Mixed-radix encoding of the complete Vinogradov power-sum vector. -/
noncomputable def linnikMomentFrequency (k r X : Nat)
    (v : Fin (k * r) -> Fin X) : Nat :=
  Nat.ofDigits (linnikMomentFrequencyBase k r X)
    (List.ofFn (linnikMomentPowerSumData k (k * r) X v))

/-- Equality of mixed-radix frequencies is exactly simultaneous equality of
all k power sums. This is the lossless bridge to one-dimensional Fourier
orthogonality. -/
theorem linnikMomentFrequency_eq_iff (k r X : Nat)
    (v w : Fin (k * r) -> Fin X) :
    linnikMomentFrequency k r X v = linnikMomentFrequency k r X w <->
      linnikMomentPowerSumData k (k * r) X v =
        linnikMomentPowerSumData k (k * r) X w := by
  constructor
  next =>
    intro heq
    apply List.ofFn_injective
    apply Nat.ofDigits_inj_of_len_eq
      (b := linnikMomentFrequencyBase k r X) (by
        unfold linnikMomentFrequencyBase
        omega)
    next => simp
    next =>
      intro d hd
      cases List.mem_ofFn.mp hd with
      | intro i hi =>
        rw [<- hi]
        exact linnikMomentPowerSumValue_lt_base k r X v i
    next =>
      intro d hd
      cases List.mem_ofFn.mp hd with
      | intro i hi =>
        rw [<- hi]
        exact linnikMomentPowerSumValue_lt_base k r X w i
    next => exact heq
  next =>
    intro heq
    unfold linnikMomentFrequency
    rw [heq]

end Finset
