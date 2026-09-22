/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LinnikResidueTail

/-!
# Prime-band covering for Linnik's distinct branch

This module formalizes the finite covering step between the integer-distinct
prefix branch and the modulus-distinct packet `I(p)`.  It splits a full
length-`k*r` tuple into its prefix and tail blocks, defines the fixed-power-sum
packet fibers for a modulus, and prepares the exact finite sum used in the
prime-band Cauchy argument.
-/

set_option autoImplicit false

namespace Finset

/-- Split a full length-`k*r` tuple into its first `k` coordinates and its
remaining `k*(r-1)` coordinates. -/
def linnikSplitTuple (k r X : Nat) (hr : 0 < r)
    (v : Fin (k * r) -> Fin X) :
    Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X) :=
  (fun i => v (linnikBlockEquiv k r hr (Sum.inl i)),
    fun i => v (linnikBlockEquiv k r hr (Sum.inr i)))

/-- Joining after splitting recovers the full tuple. -/
theorem linnikJoinTuple_splitTuple
    (k r X : Nat) (hr : 0 < r) (v : Fin (k * r) -> Fin X) :
    linnikJoinTuple k r X hr (linnikSplitTuple k r X hr v) = v := by
  funext i
  cases (linnikBlockEquiv k r hr).surjective i with
  | intro s hs =>
      subst i
      cases s <;> simp [linnikJoinTuple, linnikSplitTuple]

/-- Splitting after joining recovers the prefix-tail packet. -/
theorem linnikSplitTuple_joinTuple
    (k r X : Nat) (hr : 0 < r)
    (vu : Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X)) :
    linnikSplitTuple k r X hr (linnikJoinTuple k r X hr vu) = vu := by
  apply Prod.ext
  next =>
    funext i
    simp [linnikJoinTuple, linnikSplitTuple]
  next =>
    funext i
    simp [linnikJoinTuple, linnikSplitTuple]

/-- The first block selected by `linnikSplitTuple` is the prefix used in
the distinct branch. -/
theorem fst_linnikSplitTuple_eq_linnikMomentPrefix
    (k r X : Nat) (hr : 0 < r) (v : Fin (k * r) -> Fin X) :
    (linnikSplitTuple k r X hr v).fst =
      linnikMomentPrefix k r X hr v := by
  funext i
  rfl

/-- Joining a packet preserves its prefix block. -/
theorem linnikMomentPrefix_joinTuple
    (k r X : Nat) (hr : 0 < r)
    (vu : Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X)) :
    linnikMomentPrefix k r X hr (linnikJoinTuple k r X hr vu) = vu.fst := by
  rw [<- fst_linnikSplitTuple_eq_linnikMomentPrefix]
  exact congrArg Prod.fst (linnikSplitTuple_joinTuple k r X hr vu)

/-- The split and join maps form an equivalence. -/
def linnikTupleBlockEquiv (k r X : Nat) (hr : 0 < r) :
    Equiv (Fin (k * r) -> Fin X)
      (Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X)) :=
  { toFun := linnikSplitTuple k r X hr
    invFun := linnikJoinTuple k r X hr
    left_inv := linnikJoinTuple_splitTuple k r X hr
    right_inv := linnikSplitTuple_joinTuple k r X hr }

/-- The modulus-distinct packet fiber above one full power-sum datum. -/
noncomputable def linnikModDistinctPowerSumFiber
    (p k r X : Nat) (hp : 0 < p) (hr : 0 < r) (h : Fin k -> Nat) :
    Finset (Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X)) :=
  (linnikModDistinctPacket p k X (k * (r - 1)) hp).filter (fun vu =>
    linnikMomentPowerSumData k (k * r) X
      (linnikJoinTuple k r X hr vu) = h)

/-- The attained full-tuple power-sum datum of a prefix-tail packet. -/
noncomputable def linnikModDistinctPacketPowerSumValue
    (k r X : Nat) (hr : 0 < r)
    (vu : Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X)) :
    linnikMomentPowerSumRange k r X :=
  Subtype.mk
    (linnikMomentPowerSumData k (k * r) X
      (linnikJoinTuple k r X hr vu)) (by
        apply Finset.mem_image.mpr
        exact Exists.intro (linnikJoinTuple k r X hr vu)
          (And.intro (Finset.mem_univ _) rfl))

/-- Filtering a modulus-distinct packet by its attained datum recovers the
corresponding packet power-sum fiber. -/
theorem linnikModDistinctPacket_filter_powerSumValue
    (p k r X : Nat) (hp : 0 < p) (hr : 0 < r)
    (h : linnikMomentPowerSumRange k r X) :
    (linnikModDistinctPacket p k X (k * (r - 1)) hp).filter (fun vu =>
        linnikModDistinctPacketPowerSumValue k r X hr vu = h) =
      linnikModDistinctPowerSumFiber p k r X hp hr h.val := by
  ext vu
  simp only [linnikModDistinctPowerSumFiber, Finset.mem_filter]
  constructor
  next =>
    intro hv
    exact And.intro hv.1 (congrArg Subtype.val hv.2)
  next =>
    intro hv
    refine And.intro hv.1 ?_
    apply Subtype.ext
    exact hv.2

/-- Full tuples above one power-sum datum whose prefix is distinct modulo
`p`.  This is the full-tuple presentation of the packet fiber. -/
noncomputable def linnikModDistinctTupleFiber
    (p k r X : Nat) (hp : 0 < p) (hr : 0 < r) (h : Fin k -> Nat) :
    Finset (Fin (k * r) -> Fin X) :=
  (linnikMomentFiber k r X h).filter (fun v =>
    Function.Injective (fun i : Fin k =>
      linnikResidueIndex p X hp (linnikMomentPrefix k r X hr v i)))

/-- The block equivalence sends the full-tuple modulus fiber exactly onto
the corresponding prefix-tail packet fiber. -/
theorem map_linnikModDistinctTupleFiber_eq_powerSumFiber
    (p k r X : Nat) (hp : 0 < p) (hr : 0 < r) (h : Fin k -> Nat) :
    (linnikModDistinctTupleFiber p k r X hp hr h).map
        (linnikTupleBlockEquiv k r X hr).toEmbedding =
      linnikModDistinctPowerSumFiber p k r X hp hr h := by
  classical
  ext vu
  simp only [Finset.mem_map, linnikModDistinctTupleFiber,
    linnikModDistinctPowerSumFiber, Finset.mem_filter]
  constructor
  next =>
    intro hv
    cases hv with
    | intro v hv =>
        cases hv with
        | intro hv hsplit =>
            subst vu
            refine And.intro ?_ ?_
            next =>
              have hinj := hv.2
              rw [<- fst_linnikSplitTuple_eq_linnikMomentPrefix] at hinj
              simpa [linnikTupleBlockEquiv, linnikModDistinctPacket,
                linnikModDistinctPrefixTuples] using hinj
            next =>
              unfold linnikMomentFiber at hv
              simpa [linnikTupleBlockEquiv, linnikJoinTuple_splitTuple]
                using hv.1
  next =>
    intro hv
    refine Exists.intro (linnikJoinTuple k r X hr vu) ?_
    refine And.intro ?_ (linnikSplitTuple_joinTuple k r X hr vu)
    refine And.intro ?_ ?_
    next =>
      simpa [linnikMomentFiber] using hv.2
    next =>
      have hinj : Function.Injective (fun i : Fin k =>
          linnikResidueIndex p X hp (vu.fst i)) := by
        simpa [linnikModDistinctPacket, linnikModDistinctPrefixTuples]
          using hv.1
      rw [linnikMomentPrefix_joinTuple]
      exact hinj

/-- The full-tuple and packet presentations of one modulus fiber have the
same finite cardinality. -/
theorem card_linnikModDistinctTupleFiber_eq_powerSumFiber
    (p k r X : Nat) (hp : 0 < p) (hr : 0 < r) (h : Fin k -> Nat) :
    (linnikModDistinctTupleFiber p k r X hp hr h).card =
      (linnikModDistinctPowerSumFiber p k r X hp hr h).card := by
  rw [<- map_linnikModDistinctTupleFiber_eq_powerSumFiber]
  exact (Finset.card_map (linnikTupleBlockEquiv k r X hr).toEmbedding).symm

/-- If every integer-distinct tuple in one power-sum fiber is separated by
some modulus in `P`, then that fiber is covered by the corresponding packet
fibers.  This is the exact finite `R1(h) <= sum_p R4(h,p)` step. -/
theorem card_linnikDistinctFiber_le_sum_modDistinctPowerSumFiber
    (P : Finset {p : Nat // 0 < p}) (k r X : Nat) (hr : 0 < r)
    (h : Fin k -> Nat)
    (hcover : forall v,
      Membership.mem (linnikDistinctFiber k r X hr h) v ->
        exists p, exists _hpP : Membership.mem P p,
          Function.Injective (fun i : Fin k =>
            linnikResidueIndex p.val X p.property
              (linnikMomentPrefix k r X hr v i))) :
    (linnikDistinctFiber k r X hr h).card <=
      P.sum (fun p =>
        (linnikModDistinctPowerSumFiber p.val k r X
          p.property hr h).card) := by
  classical
  let R := fun (p : {p : Nat // 0 < p}) =>
    linnikModDistinctTupleFiber p.val k r X p.property hr h
  have hsubset : forall v,
      Membership.mem (linnikDistinctFiber k r X hr h) v ->
        Membership.mem (P.biUnion fun p => R p) v := by
    intro v hv
    cases hcover v hv with
    | intro p hpExists =>
        cases hpExists with
        | intro hpP hinj =>
            rw [Finset.mem_biUnion]
            refine Exists.intro p (And.intro hpP ?_)
            unfold R linnikModDistinctTupleFiber
            rw [Finset.mem_filter]
            exact And.intro (Finset.mem_filter.mp hv).1 hinj
  calc
    (linnikDistinctFiber k r X hr h).card <=
        (P.biUnion fun p => R p).card :=
      Finset.card_le_card hsubset
    _ <= P.sum (fun p => (R p).card) :=
      Finset.card_biUnion_le
    _ = P.sum (fun p =>
        (linnikModDistinctPowerSumFiber p.val k r X
          p.property hr h).card) := by
      apply Finset.sum_congr rfl
      intro p hpP
      exact card_linnikModDistinctTupleFiber_eq_powerSumFiber
        p.val k r X p.property hr h

/-- Squaring the one-fiber prime-band cover costs only the number of
available moduli. -/
theorem sq_card_linnikDistinctFiber_le_card_mul_sum_sq_modDistinct
    (P : Finset {p : Nat // 0 < p}) (k r X : Nat) (hr : 0 < r)
    (h : Fin k -> Nat)
    (hcover : forall v,
      Membership.mem (linnikDistinctFiber k r X hr h) v ->
        exists p, exists _hpP : Membership.mem P p,
          Function.Injective (fun i : Fin k =>
            linnikResidueIndex p.val X p.property
              (linnikMomentPrefix k r X hr v i))) :
    (linnikDistinctFiber k r X hr h).card ^ 2 <=
      P.card * P.sum (fun p =>
        (linnikModDistinctPowerSumFiber p.val k r X
          p.property hr h).card ^ 2) := by
  calc
    (linnikDistinctFiber k r X hr h).card ^ 2 <=
        (P.sum (fun p =>
          (linnikModDistinctPowerSumFiber p.val k r X
            p.property hr h).card)) ^ 2 :=
      Nat.pow_le_pow_left
        (card_linnikDistinctFiber_le_sum_modDistinctPowerSumFiber
          P k r X hr h hcover) 2
    _ <= P.card * P.sum (fun p =>
        (linnikModDistinctPowerSumFiber p.val k r X
          p.property hr h).card ^ 2) :=
      nat_sum_sq_le_card_mul_sum_sq _ _

/-- Equal-power-sum pairs in the modulus-distinct packet. -/
noncomputable def linnikModDistinctEqualPairs
    (p k r X : Nat) (hp : 0 < p) (hr : 0 < r) :
    Finset (Prod
      (Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X))
      (Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X))) :=
  ((linnikModDistinctPacket p k X (k * (r - 1)) hp).product
      (linnikModDistinctPacket p k X (k * (r - 1)) hp)).filter (fun vw =>
    linnikMomentPowerSumData k (k * r) X
        (linnikJoinTuple k r X hr vw.fst) =
      linnikMomentPowerSumData k (k * r) X
        (linnikJoinTuple k r X hr vw.snd))

/-- Summing the squares of all modulus-distinct packet fibers gives exactly
the modulus packet's equal-power-sum pair count. -/
theorem sum_sq_linnikModDistinctPowerSumFiber_eq_card_equalPairs
    (p k r X : Nat) (hp : 0 < p) (hr : 0 < r) :
    (linnikMomentPowerSumRange k r X).sum (fun h =>
        (linnikModDistinctPowerSumFiber p k r X hp hr h).card ^ 2) =
      (linnikModDistinctEqualPairs p k r X hp hr).card := by
  classical
  let A := linnikModDistinctPacket p k X (k * (r - 1)) hp
  let g := linnikModDistinctPacketPowerSumValue k r X hr
  calc
    (linnikMomentPowerSumRange k r X).sum (fun h =>
        (linnikModDistinctPowerSumFiber p k r X hp hr h).card ^ 2) =
        Finset.univ.sum (fun h : linnikMomentPowerSumRange k r X =>
          (linnikModDistinctPowerSumFiber p k r X hp hr h.val).card ^ 2) := by
      exact (Finset.sum_coe_sort _ _).symm
    _ = Finset.univ.sum (fun h : linnikMomentPowerSumRange k r X =>
        (A.filter (fun vu => g vu = h)).card ^ 2) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [linnikModDistinctPacket_filter_powerSumValue]
    _ = A.sum (fun vu => (A.filter (fun w => g w = g vu)).card) :=
      sum_sq_fiber_card_eq_sum_fiber_card A g
    _ = ((A.product A).filter (fun vw => g vw.snd = g vw.fst)).card := by
      symm
      exact card_filter_product_eq_sum_filter_card
        (s := A) (t := A) (P := fun v w => g w = g v)
    _ = (linnikModDistinctEqualPairs p k r X hp hr).card := by
      unfold linnikModDistinctEqualPairs
      apply congrArg Finset.card
      ext vw
      simp only [Finset.mem_filter]
      constructor
      next =>
        intro hv
        refine And.intro hv.1 ?_
        have hval := congrArg Subtype.val hv.2
        exact hval.symm
      next =>
        intro hv
        refine And.intro hv.1 ?_
        apply Subtype.ext
        exact hv.2.symm

/-- Summing the squared prime-band cover over all attained power-sum data
gives the complete distinct-branch bound by the modulus packet pair counts. -/
theorem linnikDistinctSquareSum_le_card_mul_sum_equalPairs
    (P : Finset {p : Nat // 0 < p}) (k r X : Nat) (hr : 0 < r)
    (hcover : forall h,
      Membership.mem (linnikMomentPowerSumRange k r X) h ->
        forall v, Membership.mem (linnikDistinctFiber k r X hr h) v ->
          exists p, exists _hpP : Membership.mem P p,
            Function.Injective (fun i : Fin k =>
              linnikResidueIndex p.val X p.property
                (linnikMomentPrefix k r X hr v i))) :
    linnikDistinctSquareSum k r X hr <=
      P.card * P.sum (fun p =>
        (linnikModDistinctEqualPairs p.val k r X p.property hr).card) := by
  unfold linnikDistinctSquareSum
  calc
    (linnikMomentPowerSumRange k r X).sum (fun h =>
        (linnikDistinctFiber k r X hr h).card ^ 2) <=
        (linnikMomentPowerSumRange k r X).sum (fun h =>
          P.card * P.sum (fun p =>
            (linnikModDistinctPowerSumFiber p.val k r X
              p.property hr h).card ^ 2)) := by
      apply Finset.sum_le_sum
      intro h hh
      exact sq_card_linnikDistinctFiber_le_card_mul_sum_sq_modDistinct
        P k r X hr h (hcover h hh)
    _ = P.card * (linnikMomentPowerSumRange k r X).sum (fun h =>
        P.sum (fun p =>
          (linnikModDistinctPowerSumFiber p.val k r X
            p.property hr h).card ^ 2)) := by
      rw [Finset.mul_sum]
    _ = P.card * P.sum (fun p =>
        (linnikMomentPowerSumRange k r X).sum (fun h =>
          (linnikModDistinctPowerSumFiber p.val k r X
            p.property hr h).card ^ 2)) := by
      rw [Finset.sum_comm]
    _ = P.card * P.sum (fun p =>
        (linnikModDistinctEqualPairs p.val k r X p.property hr).card) := by
      apply congrArg (fun z => P.card * z)
      apply Finset.sum_congr rfl
      intro p hpP
      exact sum_sq_linnikModDistinctPowerSumFiber_eq_card_equalPairs
        p.val k r X p.property hr

/-- A strict bound for the bad moduli of every distinct prefix supplies the
covering hypothesis and hence the complete distinct-branch square-sum bound. -/
theorem linnikDistinctSquareSum_le_card_mul_sum_equalPairs_of_bad_card_lt
    (P : Finset {p : Nat // 0 < p}) (k r X : Nat) (hr : 0 < r)
    (hbad : forall h,
      Membership.mem (linnikMomentPowerSumRange k r X) h ->
        forall v, Membership.mem (linnikDistinctFiber k r X hr h) v ->
          (P.filter (fun p => Not (Function.Injective (fun i : Fin k =>
            linnikResidueIndex p.val X p.property
              (linnikMomentPrefix k r X hr v i))))).card < P.card) :
    linnikDistinctSquareSum k r X hr <=
      P.card * P.sum (fun p =>
        (linnikModDistinctEqualPairs p.val k r X p.property hr).card) := by
  apply linnikDistinctSquareSum_le_card_mul_sum_equalPairs P k r X hr
  intro h hh v hv
  by_contra hgood
  have hnot : forall p, Membership.mem P p ->
      Not (Function.Injective (fun i : Fin k =>
        linnikResidueIndex p.val X p.property
          (linnikMomentPrefix k r X hr v i))) := by
    intro p hpP hinj
    apply hgood
    exact Exists.intro p (Exists.intro hpP hinj)
  have hall : P.filter (fun p => Not (Function.Injective (fun i : Fin k =>
      linnikResidueIndex p.val X p.property
        (linnikMomentPrefix k r X hr v i)))) = P := by
    apply Finset.filter_eq_self.mpr
    intro p hpP
    exact hnot p hpP
  have hlt := hbad h hh v hv
  rw [hall] at hlt
  exact (Nat.lt_irrefl P.card) hlt

/-- The packet frequency pair count is the cardinality of the corresponding
equal-power-sum pair set. -/
theorem linnikModDistinctPacketPairCount_eq_card_equalPairs
    (p k r X : Nat) (hp : 0 < p) (hr : 0 < r) :
    linnikModDistinctPacketPairCount p k r X (k * (r - 1)) hp =
      (linnikModDistinctEqualPairs p k r X hp hr).card := by
  classical
  unfold linnikModDistinctPacketPairCount linnikModDistinctEqualPairs
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
      have hfreq : linnikModDistinctPacketFrequency k r X
          (k * (r - 1)) v =
        linnikModDistinctPacketFrequency k r X (k * (r - 1)) w :=
        Int.ofNat_inj.mp (sub_eq_zero.mp h)
      exact (linnikModDistinctPacketFrequency_eq_iff_powerSums
        k r X hr v w).mp hfreq
    next =>
      intro h
      have hfreq : linnikModDistinctPacketFrequency k r X
          (k * (r - 1)) v =
        linnikModDistinctPacketFrequency k r X (k * (r - 1)) w :=
        (linnikModDistinctPacketFrequency_eq_iff_powerSums
          k r X hr v w).mpr h
      exact sub_eq_zero.mpr (congrArg Int.ofNat hfreq)
  next => rfl
  next => rfl

end Finset
