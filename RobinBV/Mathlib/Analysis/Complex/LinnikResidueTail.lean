/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LinnikResidueArithmetic

/-!
# Compatible residue tails in Linnik's recurrence

This module sends a tuple lying in one residue class modulo `p` to its
coordinatewise quotient by `p`.  On the fixed residue-class packet this
quotient map is injective, and its image lies in an interval of length
`1 + X / p`.  These are the arithmetic inputs for bounding the remaining
compatible-tail fibers by the lower-level Vinogradov mean value.
-/

set_option autoImplicit false

namespace Finset

/-- Coordinatewise quotient of an interval tuple by `p`. -/
def linnikResidueTailQuotient (p X L : Nat) (u : Fin L -> Fin X) :
    Fin L -> Fin (1 + X / p) := fun i =>
  Fin.mk ((u i).val / p) (by
    have hle : (u i).val / p <= X / p :=
      Nat.div_le_div_right (Nat.le_of_lt (u i).isLt)
    omega)

/-- Equal raw residue indices force equal predecessor residues modulo `p`. -/
theorem mod_eq_of_linnikResidueIndex_eq
    (p X : Nat) (hp : 0 < p) (a : Fin p) (x y : Fin X)
    (hx : linnikResidueIndex p X hp x = a)
    (hy : linnikResidueIndex p X hp y = a) :
    x.val % p = y.val % p := by
  letI : NeZero p := NeZero.mk (Nat.ne_of_gt hp)
  have hxval := congrArg Fin.val hx
  have hyval := congrArg Fin.val hy
  have hxyPlus : (((x.val + 1 : Nat) : ZMod p)) =
      (((y.val + 1 : Nat) : ZMod p)) := by
    apply ZMod.val_injective p
    simpa only [linnikResidueIndex, ZMod.val_natCast] using hxval.trans hyval.symm
  have hxy : ((x.val : Nat) : ZMod p) = ((y.val : Nat) : ZMod p) := by
    apply add_right_cancel (b := (1 : ZMod p))
    simpa only [Nat.cast_add, Nat.cast_one] using hxyPlus
  have hval := congrArg ZMod.val hxy
  simpa only [ZMod.val_natCast] using hval

/-- Division and the common residue reconstruct every coordinate exactly. -/
theorem linnikResidueTailQuotient_reconstruct
    (p X L : Nat) (u : Fin L -> Fin X) (i : Fin L) :
    p * (linnikResidueTailQuotient p X L u i).val + (u i).val % p =
      (u i).val := by
  change p * ((u i).val / p) + (u i).val % p = (u i).val
  rw [Nat.add_comm]
  exact Nat.mod_add_div (u i).val p

/-- The quotient map is injective on tuples contained in one residue class. -/
theorem linnikResidueTailQuotient_injective_on
    (p X L : Nat) (hp : 0 < p) (a : Fin p)
    (u v : Fin L -> Fin X)
    (hu : Membership.mem (linnikResidueTailTuples p X L hp a) u)
    (hv : Membership.mem (linnikResidueTailTuples p X L hp a) v)
    (hquot : linnikResidueTailQuotient p X L u =
      linnikResidueTailQuotient p X L v) :
    u = v := by
  funext i
  apply Fin.ext
  have hui := (Fintype.mem_piFinset.mp hu) i
  have hvi := (Fintype.mem_piFinset.mp hv) i
  have hures := (Finset.mem_filter.mp hui).2
  have hvres := (Finset.mem_filter.mp hvi).2
  have hmod := mod_eq_of_linnikResidueIndex_eq p X hp a (u i) (v i)
    hures hvres
  have hdiv := congrArg (fun w => (w i).val) hquot
  change (u i).val / p = (v i).val / p at hdiv
  have huRec := linnikResidueTailQuotient_reconstruct p X L u i
  have hvRec := linnikResidueTailQuotient_reconstruct p X L v i
  change p * ((u i).val / p) + (u i).val % p = (u i).val at huRec
  change p * ((v i).val / p) + (v i).val % p = (v i).val at hvRec
  calc
    (u i).val = p * ((u i).val / p) + (u i).val % p := huRec.symm
    _ = p * ((v i).val / p) + (v i).val % p := by rw [hdiv, hmod]
    _ = (v i).val := hvRec

/-- Equal-frequency pairs of tails lying in one fixed residue class. -/
noncomputable def linnikResidueTailEqualPairs
    (p k r X L : Nat) (hp : 0 < p) (a : Fin p) :
    Finset (Prod (Fin L -> Fin X) (Fin L -> Fin X)) :=
  ((linnikResidueTailTuples p X L hp a).product
      (linnikResidueTailTuples p X L hp a)).filter (fun uv =>
    linnikTailFrequency k r X L uv.fst =
      linnikTailFrequency k r X L uv.snd)

/-- The compatible-tail count is an integer-frequency correlation at the
shift determined by the fixed prefix pair. -/
theorem card_linnikCompatibleTailPairs_eq_integerPairCount
    (p k r X : Nat) (hp : 0 < p) (hx : X < p ^ k) (a : Fin p)
    (b : linnikShiftedCongruencePairs p k a.val X hp hx) :
    ((linnikCompatibleTailPairs p k r X hp hx a b).card : Real) =
      AddCircle.integerPairCount
        (linnikResidueTailTuples p X (k * (r - 1)) hp a)
        (fun u => (linnikTailFrequency k r X (k * (r - 1)) u : Int))
        ((linnikPrefixFrequency k r X b.val.snd : Int) -
          (linnikPrefixFrequency k r X b.val.fst : Int)) := by
  classical
  unfold linnikCompatibleTailPairs AddCircle.integerPairCount
  rw [Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]
  norm_cast
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  apply if_congr
  next =>
    constructor
    next =>
      intro h
      change (linnikPrefixFrequency k r X b.val.fst +
          linnikTailFrequency k r X (k * (r - 1)) u =
        linnikPrefixFrequency k r X b.val.snd +
          linnikTailFrequency k r X (k * (r - 1)) v) at h
      have hcast := congrArg Int.ofNat h
      push_cast at hcast
      rw [Int.subNatNat_eq_coe]
      change (linnikTailFrequency k r X (k * (r - 1)) u : Int) -
          (linnikTailFrequency k r X (k * (r - 1)) v : Int) =
        (linnikPrefixFrequency k r X b.val.snd : Int) -
          (linnikPrefixFrequency k r X b.val.fst : Int)
      omega
    next =>
      intro h
      rw [Int.subNatNat_eq_coe] at h
      change (linnikTailFrequency k r X (k * (r - 1)) u : Int) -
          (linnikTailFrequency k r X (k * (r - 1)) v : Int) =
        (linnikPrefixFrequency k r X b.val.snd : Int) -
          (linnikPrefixFrequency k r X b.val.fst : Int) at h
      change (linnikPrefixFrequency k r X b.val.fst +
          linnikTailFrequency k r X (k * (r - 1)) u =
        linnikPrefixFrequency k r X b.val.snd +
          linnikTailFrequency k r X (k * (r - 1)) v)
      apply Int.ofNat_inj.mp
      push_cast
      omega
  next => rfl
  next => rfl

/-- The zero integer-frequency correlation is exactly the equal-tail-pair
cardinality. -/
theorem card_linnikResidueTailEqualPairs_eq_integerPairCount_zero
    (p k r X L : Nat) (hp : 0 < p) (a : Fin p) :
    ((linnikResidueTailEqualPairs p k r X L hp a).card : Real) =
      AddCircle.integerPairCount (linnikResidueTailTuples p X L hp a)
        (fun u => (linnikTailFrequency k r X L u : Int)) 0 := by
  classical
  unfold linnikResidueTailEqualPairs AddCircle.integerPairCount
  rw [Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]
  norm_cast
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  apply if_congr
  next =>
    constructor
    next =>
      intro h
      exact sub_eq_zero.mpr (congrArg Int.ofNat h)
    next =>
      intro h
      exact Int.ofNat_inj.mp (sub_eq_zero.mp h)
  next => rfl
  next => rfl

/-- A fixed inhomogeneous compatible-tail correlation is no larger than
the homogeneous equal-frequency tail energy. -/
theorem card_linnikCompatibleTailPairs_le_equalPairs
    (p k r X : Nat) (hp : 0 < p) (hx : X < p ^ k) (a : Fin p)
    (b : linnikShiftedCongruencePairs p k a.val X hp hx) :
    (linnikCompatibleTailPairs p k r X hp hx a b).card <=
      (linnikResidueTailEqualPairs p k r X (k * (r - 1)) hp a).card := by
  have h := AddCircle.integerPairCount_le_zero
    (linnikResidueTailTuples p X (k * (r - 1)) hp a)
    (fun u => (linnikTailFrequency k r X (k * (r - 1)) u : Int))
    ((linnikPrefixFrequency k r X b.val.snd : Int) -
      (linnikPrefixFrequency k r X b.val.fst : Int))
  rw [<- card_linnikCompatibleTailPairs_eq_integerPairCount
    p k r X hp hx a b] at h
  rw [<- card_linnikResidueTailEqualPairs_eq_integerPairCount_zero
    p k r X (k * (r - 1)) hp a] at h
  exact_mod_cast h

/-- Equality of the one-dimensional tail frequencies recovers equality of
all power sums carried by the tail block. -/
theorem linnikTailPowerSums_eq_of_frequency_eq
    (k r X : Nat) (hr : 0 < r) (hX : 0 < X)
    (u v : Fin (k * (r - 1)) -> Fin X)
    (hfreq : linnikTailFrequency k r X (k * (r - 1)) u =
      linnikTailFrequency k r X (k * (r - 1)) v) :
    forall j : Fin k,
      Finset.univ.sum (fun i => (u i).val ^ (j.val + 1)) =
        Finset.univ.sum (fun i => (v i).val ^ (j.val + 1)) := by
  let z : Fin k -> Fin X := fun _i => Fin.mk 0 hX
  let U : Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X) := (z, u)
  let V : Prod (Fin k -> Fin X) (Fin (k * (r - 1)) -> Fin X) := (z, v)
  have hpacket :
      linnikModDistinctPacketFrequency k r X (k * (r - 1)) U =
        linnikModDistinctPacketFrequency k r X (k * (r - 1)) V := by
    unfold linnikModDistinctPacketFrequency
    dsimp only [U, V]
    rw [hfreq]
  have hdata := (linnikModDistinctPacketFrequency_eq_iff_powerSums
    k r X hr U V).mp hpacket
  intro j
  have hj := congrFun hdata j
  unfold linnikMomentPowerSumData at hj
  have huSplit := sum_linnikJoinTuple k r X hr U
    (fun x => x.val ^ (j.val + 1))
  have hvSplit := sum_linnikJoinTuple k r X hr V
    (fun x => x.val ^ (j.val + 1))
  rw [huSplit, hvSplit] at hj
  exact Nat.add_left_cancel hj

/-- Equal-frequency residue tails yield equal power sums after division by
the common modulus. -/
theorem linnikResidueTailQuotient_powerSums_eq
    (p k r X : Nat) (hp : 0 < p) (hk : 0 < k) (hr : 1 < r)
    (hX : 0 < X) (a : Fin p)
    (u v : Fin (k * (r - 1)) -> Fin X)
    (hu : Membership.mem
      (linnikResidueTailTuples p X (k * (r - 1)) hp a) u)
    (hv : Membership.mem
      (linnikResidueTailTuples p X (k * (r - 1)) hp a) v)
    (hfreq : linnikTailFrequency k r X (k * (r - 1)) u =
      linnikTailFrequency k r X (k * (r - 1)) v) :
    forall j : Fin k,
      Finset.univ.sum (fun i =>
        (linnikResidueTailQuotient p X (k * (r - 1)) u i).val ^
          (j.val + 1)) =
      Finset.univ.sum (fun i =>
        (linnikResidueTailQuotient p X (k * (r - 1)) v i).val ^
          (j.val + 1)) := by
  have hL : 0 < k * (r - 1) := Nat.mul_pos hk (Nat.sub_pos_of_lt hr)
  let i0 : Fin (k * (r - 1)) := Fin.mk 0 hL
  let rem : Nat := (u i0).val % p
  have huRes : forall i, linnikResidueIndex p X hp (u i) = a := by
    intro i
    exact (Finset.mem_filter.mp ((Fintype.mem_piFinset.mp hu) i)).2
  have hvRes : forall i, linnikResidueIndex p X hp (v i) = a := by
    intro i
    exact (Finset.mem_filter.mp ((Fintype.mem_piFinset.mp hv) i)).2
  have hremU : forall i, (u i).val % p = rem := by
    intro i
    exact mod_eq_of_linnikResidueIndex_eq p X hp a (u i) (u i0)
      (huRes i) (huRes i0)
  have hremV : forall i, (v i).val % p = rem := by
    intro i
    exact mod_eq_of_linnikResidueIndex_eq p X hp a (v i) (u i0)
      (hvRes i) (huRes i0)
  have hrecU : forall i,
      p * (linnikResidueTailQuotient p X (k * (r - 1)) u i).val + rem =
        (u i).val := by
    intro i
    rw [<- hremU i]
    exact linnikResidueTailQuotient_reconstruct p X (k * (r - 1)) u i
  have hrecV : forall i,
      p * (linnikResidueTailQuotient p X (k * (r - 1)) v i).val + rem =
        (v i).val := by
    intro i
    rw [<- hremV i]
    exact linnikResidueTailQuotient_reconstruct p X (k * (r - 1)) v i
  have horig := linnikTailPowerSums_eq_of_frequency_eq
    k r X (lt_trans (by omega) hr) hX u v hfreq
  have haff : forall j : Fin k,
      Finset.univ.sum (fun i =>
        (p * (linnikResidueTailQuotient p X (k * (r - 1)) u i).val +
          rem) ^ (j.val + 1)) =
      Finset.univ.sum (fun i =>
        (p * (linnikResidueTailQuotient p X (k * (r - 1)) v i).val +
          rem) ^ (j.val + 1)) := by
    intro j
    calc
      Finset.univ.sum (fun i =>
          (p * (linnikResidueTailQuotient p X (k * (r - 1)) u i).val +
            rem) ^ (j.val + 1)) =
          Finset.univ.sum (fun i => (u i).val ^ (j.val + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hrecU i]
      _ = Finset.univ.sum (fun i => (v i).val ^ (j.val + 1)) := horig j
      _ = Finset.univ.sum (fun i =>
          (p * (linnikResidueTailQuotient p X (k * (r - 1)) v i).val +
            rem) ^ (j.val + 1)) := by
        symm
        apply Finset.sum_congr rfl
        intro i hi
        rw [hrecV i]
  exact power_sums_eq_of_affine_nat_power_sums_eq_general
    (k * (r - 1)) k p rem hp
    (fun i => (linnikResidueTailQuotient p X (k * (r - 1)) u i).val)
    (fun i => (linnikResidueTailQuotient p X (k * (r - 1)) v i).val)
    haff

/-- The homogeneous equal-frequency residue-tail energy injects into the
lower-level Vinogradov mean-value solution set. -/
theorem card_linnikResidueTailEqualPairs_le_vinogradovMeanValue
    (p k r X : Nat) (hp : 0 < p) (hk : 0 < k) (hr : 1 < r)
    (a : Fin p) :
    (linnikResidueTailEqualPairs p k r X (k * (r - 1)) hp a).card <=
      vinogradovMeanValue k (k * (r - 1)) (1 + X / p) := by
  classical
  have hL : 0 < k * (r - 1) := Nat.mul_pos hk (Nat.sub_pos_of_lt hr)
  unfold linnikResidueTailEqualPairs vinogradovMeanValue
  apply Finset.card_le_card_of_injOn (fun uv =>
    (linnikResidueTailQuotient p X (k * (r - 1)) uv.fst,
      linnikResidueTailQuotient p X (k * (r - 1)) uv.snd))
  next =>
    intro uv huv
    have hfilter := Finset.mem_filter.mp huv
    have hprod := Finset.mem_product.mp hfilter.1
    apply Finset.mem_filter.mpr
    constructor
    next =>
      exact Finset.mem_product.mpr
        (And.intro (Finset.mem_univ _) (Finset.mem_univ _))
    next =>
      by_cases hX : 0 < X
      next =>
        exact linnikResidueTailQuotient_powerSums_eq
          p k r X hp hk hr hX a uv.fst uv.snd hprod.1 hprod.2 hfilter.2
      next =>
        have hxzero : X = 0 := Nat.eq_zero_of_not_pos hX
        subst X
        let i0 : Fin (k * (r - 1)) := Fin.mk 0 hL
        exact Fin.elim0 (uv.fst i0)
  next =>
    intro u hu v hv huv
    have huProd := Finset.mem_product.mp (Finset.mem_filter.mp hu).1
    have hvProd := Finset.mem_product.mp (Finset.mem_filter.mp hv).1
    apply Prod.ext
    next =>
      exact linnikResidueTailQuotient_injective_on
        p X (k * (r - 1)) hp a u.fst v.fst huProd.1 hvProd.1
          (congrArg Prod.fst huv)
    next =>
      exact linnikResidueTailQuotient_injective_on
        p X (k * (r - 1)) hp a u.snd v.snd huProd.2 hvProd.2
          (congrArg Prod.snd huv)

/-- Every actual compatible-tail multiplicity is bounded by the lower-level
Vinogradov mean value on an interval of length `1 + X / p`. -/
theorem linnikResidueCompatibleTailCount_le_vinogradovMeanValue
    (p k r X : Nat) (hp : 0 < p) (hk : 0 < k) (hr : 1 < r)
    (hx : X < p ^ k) (a : Fin p)
    (b : linnikShiftedCongruencePairs p k a.val X hp hx) :
    linnikResidueCompatibleTailCount p k r X hp hk
        (lt_trans (by omega) hr) hx a b <=
      vinogradovMeanValue k (k * (r - 1)) (1 + X / p) := by
  calc
    linnikResidueCompatibleTailCount p k r X hp hk
        (lt_trans (by omega) hr) hx a b <=
        (linnikCompatibleTailPairs p k r X hp hx a b).card :=
      linnikResidueCompatibleTailCount_le_card_compatibleTailPairs
        p k r X hp hk (lt_trans (by omega) hr) hx a b
    _ <= (linnikResidueTailEqualPairs p k r X
        (k * (r - 1)) hp a).card :=
      card_linnikCompatibleTailPairs_le_equalPairs p k r X hp hx a b
    _ <= vinogradovMeanValue k (k * (r - 1)) (1 + X / p) :=
      card_linnikResidueTailEqualPairs_le_vinogradovMeanValue
        p k r X hp hk hr a

/-- The actual distinct-prefix packet count now has the complete source
recurrence bound; no abstract compatible-tail parameter remains. -/
theorem exists_residue_linnikModDistinctPairCount_le_vinogradovMeanValue
    (p k r X : Nat) (hp : p.Prime) (hk : 0 < k) (hkp : k < p)
    (hr : 1 < r) (hx : X < p ^ k) :
    exists a : Fin p,
      linnikModDistinctPacketPairCount p k r X (k * (r - 1)) hp.pos <=
        (p : Real) ^ (2 * (k * (r - 1))) *
          ((X ^ k * (k.factorial * p ^ (k * (k - 1) / 2))) *
            vinogradovMeanValue k (k * (r - 1)) (1 + X / p) : Nat) := by
  exact exists_residue_linnikModDistinctPairCount_le_explicit
    p k r X (vinogradovMeanValue k (k * (r - 1)) (1 + X / p))
    hp hk hkp hr hx (fun a b =>
      linnikResidueCompatibleTailCount_le_vinogradovMeanValue
        p k r X hp.pos hk hr hx a b)

end Finset
