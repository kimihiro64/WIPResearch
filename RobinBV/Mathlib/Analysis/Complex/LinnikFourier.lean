/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.List.Indexes
import RobinBV.Mathlib.Analysis.Complex.FiniteCircleEnergy
import RobinBV.Mathlib.NumberTheory.LinnikInduction

/-!
# Fourier encoding for Linnik collision counts

This module connects the exact repeated-coordinate collision count in Linnik's
Vinogradov mean-value induction to the integer-frequency pair count on the
additive circle. The mixed-radix encoding is lossless: equality of its single
integer frequency is equivalent to simultaneous equality of every power sum.
-/

set_option autoImplicit false

namespace Finset

/-- The fixed-collision pair count is exactly the zero-difference integer
frequency pair count. No collision is added or discarded by the encoding. -/
theorem linnikFixedCollisionPairCount_eq_integerPairCount
    (k r X : Nat) (hr : 0 < r)
    (ij : Prod (Fin k) (Fin k)) :
    (linnikFixedCollisionPairCount k r X hr ij : Real) =
      AddCircle.integerPairCount
        (linnikFixedCollisionTuples k r X hr ij)
        (fun v => (linnikMomentFrequency k r X v : Int)) 0 := by
  classical
  dsimp [linnikFixedCollisionPairCount, AddCircle.integerPairCount]
  rw [Finset.card_filter, Finset.sum_product]
  norm_cast
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  apply if_congr
  next =>
    constructor
    next =>
      intro hdata
      have hfreq : linnikMomentFrequency k r X v =
          linnikMomentFrequency k r X w := by
        apply (linnikMomentFrequency_eq_iff k r X v w).2
        exact congrArg Subtype.val hdata.symm
      rw [Int.subNatNat_eq_coe]
      exact sub_eq_zero.mpr (by exact_mod_cast hfreq)
    next =>
      intro hsub
      rw [Int.subNatNat_eq_coe] at hsub
      have hint : (linnikMomentFrequency k r X v : Int) =
          (linnikMomentFrequency k r X w : Int) := sub_eq_zero.mp hsub
      have hfreq : linnikMomentFrequency k r X v =
          linnikMomentFrequency k r X w := by
        exact_mod_cast hint
      have hdata := (linnikMomentFrequency_eq_iff k r X v w).1 hfreq
      exact Subtype.ext hdata.symm
  next => rfl
  next => rfl

/-- The complete Vinogradov mean-value count at length `k * r` is exactly the
zero-difference pair count for the same lossless integer frequency. -/
theorem vinogradovMeanValue_eq_integerPairCount (k r X : Nat) :
    (vinogradovMeanValue k (k * r) X : Real) =
      AddCircle.integerPairCount
        (Finset.univ : Finset (Fin (k * r) -> Fin X))
        (fun v => (linnikMomentFrequency k r X v : Int)) 0 := by
  classical
  dsimp [vinogradovMeanValue, AddCircle.integerPairCount]
  rw [Finset.card_filter]
  rw [<- Finset.univ_product_univ, Finset.sum_product]
  norm_cast
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  apply if_congr
  next =>
    constructor
    next =>
      intro hdata
      have hpower : linnikMomentPowerSumData k (k * r) X v =
          linnikMomentPowerSumData k (k * r) X w := by
        funext j
        exact hdata j
      have hfreq := (linnikMomentFrequency_eq_iff k r X v w).2 hpower
      rw [Int.subNatNat_eq_coe]
      exact sub_eq_zero.mpr (by exact_mod_cast hfreq)
    next =>
      intro hsub
      rw [Int.subNatNat_eq_coe] at hsub
      have hint : (linnikMomentFrequency k r X v : Int) =
          (linnikMomentFrequency k r X w : Int) := sub_eq_zero.mp hsub
      have hfreq : linnikMomentFrequency k r X v =
          linnikMomentFrequency k r X w := by
        exact_mod_cast hint
      have hpower := (linnikMomentFrequency_eq_iff k r X v w).1 hfreq
      intro j
      exact congrFun hpower j
  next => rfl
  next => rfl

/-- The frequency contributed by one coordinate to the mixed-radix encoding. -/
noncomputable def linnikMomentAtomFrequency
    (k r X : Nat) (x : Fin X) : Nat :=
  Finset.univ.sum (fun j : Fin k =>
    x.val ^ (j.val + 1) * linnikMomentFrequencyBase k r X ^ j.val)

/-- The mixed-radix frequency of a tuple is the sum of its coordinate
frequencies. This is the exact factorization input for the Fourier moment. -/
theorem linnikMomentFrequency_eq_sum_atom
    (k r X : Nat) (v : Fin (k * r) -> Fin X) :
    linnikMomentFrequency k r X v =
      Finset.univ.sum (fun i => linnikMomentAtomFrequency k r X (v i)) := by
  unfold linnikMomentFrequency linnikMomentAtomFrequency
    linnikMomentPowerSumData
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]

/-- The one-coordinate exponential sum whose `k * r`-th power is the full
tuple Fourier sum. -/
noncomputable def linnikMomentAtomFourierSum
    (k r X : Nat) (t : AddCircle (1 : Real)) : Complex :=
  Finset.univ.sum (fun x : Fin X =>
    fourier (linnikMomentAtomFrequency k r X x : Int) t)

/-- The complete tuple Fourier sum factors as the `k * r`-th power of the
one-coordinate exponential sum. -/
theorem linnikMomentFullFourierSum_eq_pow
    (k r X : Nat) (t : AddCircle (1 : Real)) :
    (Finset.univ : Finset (Fin (k * r) -> Fin X)).sum
        (fun v => fourier (linnikMomentFrequency k r X v : Int) t) =
      linnikMomentAtomFourierSum k r X t ^ (k * r) := by
  calc
    _ = Finset.univ.sum (fun v : Fin (k * r) -> Fin X =>
        Finset.univ.prod (fun i => fourier
          (linnikMomentAtomFrequency k r X (v i) : Int) t)) := by
      apply Finset.sum_congr rfl
      intro v hv
      symm
      rw [linnikMomentFrequency_eq_sum_atom]
      induction (Finset.univ : Finset (Fin (k * r))) using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi]
          push_cast at ih
          push_cast
          rw [fourier_add, ih]
    _ = linnikMomentAtomFourierSum k r X t ^ (k * r) := by
      unfold linnikMomentAtomFourierSum
      exact (Fintype.sum_pow (fun x : Fin X =>
        fourier (linnikMomentAtomFrequency k r X x : Int) t) (k * r)).symm

/-- After fixing the common value at two distinct coordinates, a weighted
sum over functions factors into two fixed weights and the unrestricted
contribution from every other coordinate. -/
theorem sum_product_pair_fiber
    {I K R : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] [CommSemiring R]
    (f : K -> R) (a b : I) (hab : Not (a = b)) (x : K) :
    ((((Finset.univ : Finset (I -> K)).filter (fun v => v a = v b)).filter
        (fun v => v a = x)).sum
          (fun v => Finset.univ.prod (fun i => f (v i)))) =
      f x ^ 2 * (Finset.univ.sum f) ^ (Fintype.card I - 2) := by
  have hset :
      ((Finset.univ : Finset (I -> K)).filter (fun v => v a = v b)).filter
          (fun v => v a = x) =
        Fintype.piFinset
          (fun i : I => if i = a \/ i = b then {x} else Finset.univ) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]
    constructor
    next =>
      intro hv i
      have heq := hv.1
      have hax := hv.2
      by_cases hia : i = a
      next => subst i; simp [hax]
      by_cases hib : i = b
      next => subst i; simp [hia, heq.symm.trans hax]
      next => simp [hia, hib]
    next =>
      intro h
      have ha := h a
      have hb := h b
      simp only [true_or, if_true, Finset.mem_singleton] at ha
      simp only [or_true, if_true, Finset.mem_singleton] at hb
      exact And.intro (ha.trans hb.symm) ha
  rw [hset, <- Finset.prod_univ_sum]
  have hcoord : (fun i : I => Finset.sum
      (if i = a \/ i = b then {x} else Finset.univ) f) =
      (fun i : I => if i = a \/ i = b then f x else Finset.univ.sum f) := by
    funext i
    by_cases h : i = a \/ i = b <;> simp [h]
  rw [hcoord, Finset.prod_ite]
  simp only [Finset.prod_const]
  have hfilter :
      (Finset.univ.filter (fun i : I => i = a \/ i = b)) = {a, b} := by
    ext i
    simp [eq_comm]
  have hneg :
      (Finset.univ.filter (fun i : I => Not (i = a \/ i = b))) =
        Finset.univ \ ({a, b} : Finset I) := by
    ext i
    simp [eq_comm]
  rw [hfilter, hneg, Finset.card_sdiff]
  simp [hab]

/-- A weighted sum over all functions with two distinct coordinates equal
factors into a squared one-coordinate sum and the unrestricted contribution
of the remaining coordinates. -/
theorem sum_product_pair_equal
    {I K R : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] [CommSemiring R]
    (f : K -> R) (a b : I) (hab : Not (a = b)) :
    (((Finset.univ : Finset (I -> K)).filter (fun v => v a = v b)).sum
        (fun v => Finset.univ.prod (fun i => f (v i)))) =
      (Finset.univ.sum (fun x => f x ^ 2)) *
        (Finset.univ.sum f) ^ (Fintype.card I - 2) := by
  let A := (Finset.univ : Finset (I -> K)).filter (fun v => v a = v b)
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := A) (t := (Finset.univ : Finset K)) (g := fun v => v a)
    (fun v hv => Finset.mem_univ (v a))
    (fun v => Finset.univ.prod (fun i => f (v i)))
  rw [<- hfiber]
  unfold A
  simp_rw [sum_product_pair_fiber f a b hab]
  rw [Finset.sum_mul]

/-- The Fourier sum over tuples with one specified repeated prefix pair
factors into the doubled-coordinate sum and the unrestricted contribution
of every remaining coordinate. -/
theorem linnikFixedCollisionFourierSum_eq
    (k r X : Nat) (hr : 0 < r)
    (ij : Prod (Fin k) (Fin k))
    (hij : Membership.mem (linnikCollisionIndexPairs k) ij)
    (t : AddCircle (1 : Real)) :
    (linnikFixedCollisionTuples k r X hr ij).sum
        (fun v => fourier (linnikMomentFrequency k r X v : Int) t) =
      (Finset.univ.sum (fun x : Fin X =>
        fourier (linnikMomentAtomFrequency k r X x : Int) t ^ 2)) *
      linnikMomentAtomFourierSum k r X t ^ (k * r - 2) := by
  let emb : Fin k -> Fin (k * r) :=
    Fin.castLE (Nat.le_mul_of_pos_right k hr)
  have hne : Not (ij.fst = ij.snd) := by
    rw [linnikCollisionIndexPairs, Finset.mem_filter] at hij
    exact hij.2
  have hab : Not (emb ij.fst = emb ij.snd) := by
    intro h
    exact hne (Fin.castLE_inj.mp h)
  have hset : linnikFixedCollisionTuples k r X hr ij =
      (Finset.univ : Finset (Fin (k * r) -> Fin X)).filter
        (fun v => v (emb ij.fst) = v (emb ij.snd)) := by
    rfl
  rw [hset]
  calc
    _ = ((Finset.univ : Finset (Fin (k * r) -> Fin X)).filter
        (fun v => v (emb ij.fst) = v (emb ij.snd))).sum
        (fun v => Finset.univ.prod (fun i => fourier
          (linnikMomentAtomFrequency k r X (v i) : Int) t)) := by
      apply Finset.sum_congr rfl
      intro v hv
      symm
      rw [linnikMomentFrequency_eq_sum_atom]
      induction (Finset.univ : Finset (Fin (k * r))) using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi]
          push_cast at ih
          push_cast
          rw [fourier_add, ih]
    _ = _ := by
      simpa only [Fintype.card_fin, linnikMomentAtomFourierSum] using
        (sum_product_pair_equal
          (fun x : Fin X => fourier
            (linnikMomentAtomFrequency k r X x : Int) t)
          (emb ij.fst) (emb ij.snd) hab)

/-- Squaring each one-coordinate Fourier term is exactly evaluation of the
same exponential sum at the doubled circle argument. -/
theorem linnikMomentAtomSquareSum_eq_double
    (k r X : Nat) (t : AddCircle (1 : Real)) :
    Finset.univ.sum (fun x : Fin X =>
      fourier (linnikMomentAtomFrequency k r X x : Int) t ^ 2) =
      linnikMomentAtomFourierSum k r X (t + t) := by
  unfold linnikMomentAtomFourierSum
  apply Finset.sum_congr rfl
  intro x hx
  simp_rw [fourier_apply]
  rw [zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, pow_two]

end Finset

namespace ENNReal

/-- Three-factor Holder inequality with weights summing to one. This is the
form used for the doubled factor, the remaining-coordinate factor, and the
unit factor in Linnik's collision estimate. -/
theorem lintegral_three_norm_pow_le
    {alpha : Type*} [MeasurableSpace alpha] {mu : MeasureTheory.Measure alpha}
    {f0 f1 f2 : alpha -> ENNReal}
    (hf0 : AEMeasurable f0 mu)
    (hf1 : AEMeasurable f1 mu)
    (hf2 : AEMeasurable f2 mu)
    {p0 p1 p2 : Real} (hsum : p0 + p1 + p2 = 1)
    (hp0 : 0 <= p0) (hp1 : 0 <= p1) (hp2 : 0 <= p2) :
    MeasureTheory.lintegral mu
        (fun x => f0 x ^ p0 * f1 x ^ p1 * f2 x ^ p2) <=
      (MeasureTheory.lintegral mu f0) ^ p0 *
        (MeasureTheory.lintegral mu f1) ^ p1 *
        (MeasureTheory.lintegral mu f2) ^ p2 := by
  let f : Fin 3 -> alpha -> ENNReal :=
    Fin.cases f0 (Fin.cases f1 (Fin.cases f2 Fin.elim0))
  let p : Fin 3 -> Real :=
    Fin.cases p0 (Fin.cases p1 (Fin.cases p2 Fin.elim0))
  have ff0 : f 0 = f0 := rfl
  have ff1 : f 1 = f1 := by
    change (Fin.cases f0 (Fin.cases f1 (Fin.cases f2 Fin.elim0)) :
      Fin 3 -> alpha -> ENNReal) (Fin.succ (0 : Fin 2)) = f1
    rfl
  have ff2 : f 2 = f2 := by
    change (Fin.cases f0 (Fin.cases f1 (Fin.cases f2 Fin.elim0)) :
      Fin 3 -> alpha -> ENNReal)
        (Fin.succ (Fin.succ (0 : Fin 1))) = f2
    rfl
  have pp0 : p 0 = p0 := rfl
  have pp1 : p 1 = p1 := by
    change (Fin.cases p0 (Fin.cases p1 (Fin.cases p2 Fin.elim0)) :
      Fin 3 -> Real) (Fin.succ (0 : Fin 2)) = p1
    rfl
  have pp2 : p 2 = p2 := by
    change (Fin.cases p0 (Fin.cases p1 (Fin.cases p2 Fin.elim0)) :
      Fin 3 -> Real) (Fin.succ (Fin.succ (0 : Fin 1))) = p2
    rfl
  have h := ENNReal.lintegral_prod_norm_pow_le
    (s := (Finset.univ : Finset (Fin 3)))
    (f := f) (p := p) (fun i hi => by
      fin_cases i
      next => exact hf0
      next => exact hf1
      next => exact hf2) (by
        simpa only [Fin.sum_univ_three, pp0, pp1, pp2] using hsum)
      (fun i hi => by
        fin_cases i
        next => exact hp0
        next => exact hp1
        next => exact hp2)
  simpa only [Fin.prod_univ_three, ff0, ff1, ff2, pp0, pp1, pp2] using h

/-- Taking the reciprocal-`m` real power of a `2*m` natural power leaves
the square. -/
theorem rpow_two_mul_inv_natCast
    (x : ENNReal) (m : Nat) (hm : 0 < m) :
    (x ^ (2 * m)) ^ (1 / (m : Real)) = x ^ 2 := by
  rw [<- ENNReal.rpow_natCast]
  rw [<- ENNReal.rpow_mul]
  have hm0 : Not ((m : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have he : ((2 * m : Nat) : Real) * (1 / (m : Real)) = 2 := by
    push_cast
    field_simp
  rw [he]
  exact ENNReal.rpow_natCast x 2

/-- The complementary Holder weight turns a `2*m` natural power into the
`2*(m-2)` power. -/
theorem rpow_two_mul_sub_two_div_natCast
    (x : ENNReal) (m : Nat) (hm : 0 < m) :
    (x ^ (2 * m)) ^ ((m - 2 : Nat) / (m : Real)) =
      x ^ (2 * (m - 2)) := by
  rw [<- ENNReal.rpow_natCast]
  rw [<- ENNReal.rpow_mul]
  have hm0 : Not ((m : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have he : ((2 * m : Nat) : Real) *
      (((m - 2 : Nat) : Real) / (m : Real)) =
        ((2 * (m - 2) : Nat) : Real) := by
    push_cast
    field_simp
  rw [he]
  exact ENNReal.rpow_natCast x (2 * (m - 2))

/-- Probability-space Holder bound for one squared factor and `m-2`
remaining coordinate pairs. -/
theorem lintegral_sq_mul_pow_le_moments
    {alpha : Type*} [MeasurableSpace alpha]
    {mu : MeasureTheory.Measure alpha} [MeasureTheory.IsProbabilityMeasure mu]
    {A B : alpha -> ENNReal}
    (hA : AEMeasurable A mu) (hB : AEMeasurable B mu)
    (m : Nat) (hm : 2 <= m) :
    MeasureTheory.lintegral mu
        (fun x => A x ^ 2 * B x ^ (2 * (m - 2))) <=
      (MeasureTheory.lintegral mu (fun x => A x ^ (2 * m))) ^
          (1 / (m : Real)) *
        (MeasureTheory.lintegral mu (fun x => B x ^ (2 * m))) ^
          ((m - 2 : Nat) / (m : Real)) := by
  have hmpos : 0 < m := lt_of_lt_of_le (by omega) hm
  have hsum : (1 / (m : Real)) +
      ((m - 2 : Nat) / (m : Real)) + (1 / (m : Real)) = 1 := by
    have hmreal : Not ((m : Real) = 0) := by
      exact_mod_cast (Nat.ne_of_gt hmpos)
    rw [Nat.cast_sub hm]
    norm_num
    field_simp
    ring
  have h := ENNReal.lintegral_three_norm_pow_le
    (mu := mu)
    (f0 := fun x => A x ^ (2 * m))
    (f1 := fun x => B x ^ (2 * m))
    (f2 := fun _ => 1)
    (p0 := 1 / (m : Real))
    (p1 := (m - 2 : Nat) / (m : Real))
    (p2 := 1 / (m : Real))
    (hA.pow_const (2 * m)) (hB.pow_const (2 * m))
    aemeasurable_const hsum (by positivity) (by positivity) (by positivity)
  simp_rw [ENNReal.rpow_two_mul_inv_natCast _ m hmpos,
    ENNReal.rpow_two_mul_sub_two_div_natCast _ m hmpos] at h
  simpa using h

end ENNReal

namespace Finset

/-- Holder bounds the actual fixed-collision pair count by the two exact full
Vinogradov moments, with no discarded tuple or relaxed power-sum equality. -/
theorem ofReal_linnikFixedCollisionPairCount_le
    (k r X : Nat) (hr : 0 < r)
    (ij : Prod (Fin k) (Fin k))
    (hij : Membership.mem (linnikCollisionIndexPairs k) ij)
    (hm : 2 <= k * r) :
    ENNReal.ofReal (linnikFixedCollisionPairCount k r X hr ij : Real) <=
      ENNReal.ofReal (vinogradovMeanValue k (k * r) X : Real) ^
          (1 / ((k * r : Nat) : Real)) *
        ENNReal.ofReal (vinogradovMeanValue k (k * r) X : Real) ^
          (((k * r - 2 : Nat) : Real) / ((k * r : Nat) : Real)) := by
  let S := linnikMomentAtomFourierSum k r X
  have hS : Continuous S := by
    unfold S linnikMomentAtomFourierSum
    exact AddCircle.finite_fourier_continuous
      (Finset.univ : Finset (Fin X))
      (fun x => (linnikMomentAtomFrequency k r X x : Int))
  have hA : Continuous
      (fun t : AddCircle (1 : Real) => norm (S (t + t))) :=
    hS.comp (continuous_id.add continuous_id) |>.norm
  have hB : Continuous
      (fun t : AddCircle (1 : Real) => norm (S t)) := hS.norm
  have hHolder := ENNReal.lintegral_sq_mul_pow_le_moments
    (mu := AddCircle.haarAddCircle)
    (A := fun t : AddCircle (1 : Real) => ENNReal.ofReal (norm (S (t + t))))
    (B := fun t : AddCircle (1 : Real) => ENNReal.ofReal (norm (S t)))
    ((ENNReal.continuous_ofReal.comp hA).aemeasurable)
    ((ENNReal.continuous_ofReal.comp hB).aemeasurable)
    (k * r) hm
  have hLeftInt : MeasureTheory.Integrable
      (fun t : AddCircle (1 : Real) =>
        norm (S (t + t)) ^ 2 * norm (S t) ^ (2 * (k * r - 2)))
      AddCircle.haarAddCircle :=
    (hA.pow 2 |>.mul (hB.pow (2 * (k * r - 2)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLeft := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hLeftInt
    (Filter.Eventually.of_forall (fun t =>
      mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)))
  have hPair := AddCircle.integerPairCount_zero_integral
    (linnikFixedCollisionTuples k r X hr ij)
    (fun v => (linnikMomentFrequency k r X v : Int))
  rw [<- linnikFixedCollisionPairCount_eq_integerPairCount] at hPair
  simp_rw [linnikFixedCollisionFourierSum_eq k r X hr ij hij,
    linnikMomentAtomSquareSum_eq_double] at hPair
  simp_rw [norm_mul, norm_pow, mul_pow] at hPair
  have hPair' : MeasureTheory.integral AddCircle.haarAddCircle
      (fun t : AddCircle (1 : Real) =>
        norm (linnikMomentAtomFourierSum k r X (t + t)) ^ 2 *
          norm (linnikMomentAtomFourierSum k r X t) ^
            (2 * (k * r - 2))) =
      (linnikFixedCollisionPairCount k r X hr ij : Real) := by
    simpa only [pow_mul'] using hPair
  rw [hPair'] at hLeft
  have hMomInt : MeasureTheory.Integrable
      (fun t : AddCircle (1 : Real) => norm (S t) ^ (2 * (k * r)))
      AddCircle.haarAddCircle :=
    (hB.pow (2 * (k * r))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hMom := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hMomInt
    (Filter.Eventually.of_forall (fun t => pow_nonneg (norm_nonneg _) _))
  have hMomentCount := AddCircle.integerPairCount_zero_integral
    (Finset.univ : Finset (Fin (k * r) -> Fin X))
    (fun v => (linnikMomentFrequency k r X v : Int))
  rw [<- vinogradovMeanValue_eq_integerPairCount] at hMomentCount
  simp_rw [linnikMomentFullFourierSum_eq_pow, norm_pow, <- pow_mul]
    at hMomentCount
  have hMomentReal : MeasureTheory.integral AddCircle.haarAddCircle
      (fun t : AddCircle (1 : Real) =>
        norm (linnikMomentAtomFourierSum k r X t) ^ (2 * (k * r))) =
      (vinogradovMeanValue k (k * r) X : Real) := by
    simpa only [Nat.mul_comm] using hMomentCount
  rw [hMomentReal] at hMom
  have hDoubleInt : MeasureTheory.Integrable
      (fun t : AddCircle (1 : Real) =>
        norm (S (t + t)) ^ (2 * (k * r)))
      AddCircle.haarAddCircle :=
    (hA.pow (2 * (k * r))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDouble := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hDoubleInt
    (Filter.Eventually.of_forall (fun t => pow_nonneg (norm_nonneg _) _))
  have hScale : AddCircle.integerPairCount
      (Finset.univ : Finset (Fin (k * r) -> Fin X))
      (fun v => 2 * (linnikMomentFrequency k r X v : Int)) 0 =
      AddCircle.integerPairCount
        (Finset.univ : Finset (Fin (k * r) -> Fin X))
        (fun v => (linnikMomentFrequency k r X v : Int)) 0 := by
    classical
    unfold AddCircle.integerPairCount
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply if_congr
    next =>
      rw [show 2 * (linnikMomentFrequency k r X i : Int) -
          2 * (linnikMomentFrequency k r X j : Int) =
          2 * ((linnikMomentFrequency k r X i : Int) -
            (linnikMomentFrequency k r X j : Int)) by ring]
      simp
    next => rfl
    next => rfl
  have hDoubleCount := AddCircle.integerPairCount_zero_integral
    (Finset.univ : Finset (Fin (k * r) -> Fin X))
    (fun v => 2 * (linnikMomentFrequency k r X v : Int))
  rw [hScale] at hDoubleCount
  rw [<- vinogradovMeanValue_eq_integerPairCount] at hDoubleCount
  have hDoubleSum (t : AddCircle (1 : Real)) :
      (Finset.univ : Finset (Fin (k * r) -> Fin X)).sum
          (fun v => fourier
            (2 * (linnikMomentFrequency k r X v : Int)) t) =
        linnikMomentAtomFourierSum k r X (t + t) ^ (k * r) := by
    rw [<- linnikMomentFullFourierSum_eq_pow]
    apply Finset.sum_congr rfl
    intro v hv
    rw [show 2 * (linnikMomentFrequency k r X v : Int) =
      (linnikMomentFrequency k r X v : Int) +
        (linnikMomentFrequency k r X v : Int) by ring]
    rw [fourier_add]
    simp_rw [fourier_apply]
    rw [zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  simp_rw [hDoubleSum, norm_pow, <- pow_mul] at hDoubleCount
  have hDoubleReal : MeasureTheory.integral AddCircle.haarAddCircle
      (fun t : AddCircle (1 : Real) =>
        norm (linnikMomentAtomFourierSum k r X (t + t)) ^
          (2 * (k * r))) =
      (vinogradovMeanValue k (k * r) X : Real) := by
    simpa only [Nat.mul_comm] using hDoubleCount
  rw [hDoubleReal] at hDouble
  unfold S at hLeft hMom hDouble hHolder
  rw [hLeft]
  nth_rewrite 1 [hDouble]
  nth_rewrite 1 [hMom]
  simpa only [ENNReal.ofReal_pow, norm_nonneg, ENNReal.ofReal_mul,
    sq_nonneg, pow_nonneg] using hHolder

/-- Polynomial form of the fixed-collision Holder estimate. If `m = k*r`,
then the `m`-th power of the actual collision count is at most the
`(m-1)`-st power of the full Vinogradov mean value. -/
theorem pow_linnikFixedCollisionPairCount_le
    (k r X : Nat) (hr : 0 < r)
    (ij : Prod (Fin k) (Fin k))
    (hij : Membership.mem (linnikCollisionIndexPairs k) ij)
    (hm : 2 <= k * r) :
    linnikFixedCollisionPairCount k r X hr ij ^ (k * r) <=
      vinogradovMeanValue k (k * r) X ^ (k * r - 1) := by
  let m := k * r
  have h := ofReal_linnikFixedCollisionPairCount_le k r X hr ij hij hm
  have hmpos : 0 < m := lt_of_lt_of_le (by omega) hm
  have hp := ENNReal.rpow_le_rpow h
    (show (0 : Real) <= (m : Real) by positivity)
  rw [ENNReal.mul_rpow_of_nonneg _ _
    (show (0 : Real) <= (m : Real) by positivity)] at hp
  rw [<- ENNReal.rpow_mul, <- ENNReal.rpow_mul] at hp
  have hm0 : Not ((m : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt hmpos)
  have he1 : (1 / (m : Real)) * (m : Real) = 1 := by
    field_simp
  have he2 : (((m - 2 : Nat) : Real) / (m : Real)) * (m : Real) =
      ((m - 2 : Nat) : Real) := by
    field_simp
  rw [he1, he2, ENNReal.rpow_one, ENNReal.rpow_natCast,
    ENNReal.rpow_natCast] at hp
  unfold m at hp
  simp only [ENNReal.ofReal_natCast] at hp
  have hpNat : linnikFixedCollisionPairCount k r X hr ij ^ (k * r) <=
      vinogradovMeanValue k (k * r) X *
        vinogradovMeanValue k (k * r) X ^ (k * r - 2) := by
    exact_mod_cast hp
  have hsub : k * r - 1 = (k * r - 2) + 1 := by
    omega
  rw [hsub, pow_succ]
  simpa [mul_comm] using hpNat

/-- Complete fixed-fiber consumer of the polynomial Holder estimate. -/
theorem pow_sum_sq_linnikFixedCollisionFiber_le
    (k r X : Nat) (hr : 0 < r)
    (ij : Prod (Fin k) (Fin k))
    (hij : Membership.mem (linnikCollisionIndexPairs k) ij)
    (hm : 2 <= k * r) :
    (Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
      (linnikFixedCollisionFiber k r X hr h ij).card ^ 2)) ^ (k * r) <=
        vinogradovMeanValue k (k * r) X ^ (k * r - 1) := by
  rw [sum_sq_fixedCollisionFiber_eq_pairCount]
  exact pow_linnikFixedCollisionPairCount_le k r X hr ij hij hm

/-- Natural-number Jensen consequence for a finite family whose `m`-th
powers have a common upper bound. -/
theorem pow_sum_le_card_pow_mul_of_pow_le
    {I : Type*} [DecidableEq I] (s : Finset I) (f : I -> Nat)
    (m B : Nat) (hm : 0 < m)
    (hf : forall i, Membership.mem s i -> f i ^ m <= B) :
    (s.sum f) ^ m <= s.card ^ m * B := by
  have hj := pow_sum_le_card_mul_sum_pow
    (s := s) (f := fun i => (f i : Real))
    (fun i hi => Nat.cast_nonneg _) (m - 1)
  have hmexp : m - 1 + 1 = m :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))
  rw [hmexp] at hj
  have hterms : s.sum (fun i => ((f i : Real) ^ m)) <=
      s.sum (fun _ => (B : Real)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact_mod_cast hf i hi
  have hreal : ((s.sum f : Nat) : Real) ^ m <=
      ((s.card : Nat) : Real) ^ m * (B : Real) := by
    calc
      ((s.sum f : Nat) : Real) ^ m =
          (s.sum (fun i => (f i : Real))) ^ m := by
        norm_cast
      _ <= (s.card : Real) ^ (m - 1) *
          s.sum (fun i => (f i : Real) ^ m) := hj
      _ <= (s.card : Real) ^ (m - 1) *
          s.sum (fun _ => (B : Real)) := by
        gcongr
      _ = (s.card : Real) ^ (m - 1) *
          ((s.card : Real) * (B : Real)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((s.card : Real) ^ (m - 1) * (s.card : Real)) *
          (B : Real) := by
        ring
      _ = (s.card : Real) ^ m * (B : Real) := by
        rw [<- pow_succ, hmexp]
  exact_mod_cast hreal

/-- Complete collision-branch consumer: the `m = k*r` power of the full
collision square sum is bounded by the explicit index and prefix factors
times `J_k(X,m)^(m-1)`. -/
theorem pow_sum_sq_linnikCollisionFiber_le
    (k r X : Nat) (hr : 0 < r) (hm : 2 <= k * r) :
    (Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
      (linnikCollisionFiber k r X hr h).card ^ 2)) ^ (k * r) <=
      (k ^ 2) ^ (k * r) *
        (linnikCollisionIndexPairs k).card ^ (k * r) *
          vinogradovMeanValue k (k * r) X ^ (k * r - 1) := by
  let I := linnikCollisionIndexPairs k
  let A : Prod (Fin k) (Fin k) -> Nat := fun ij =>
    Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
      (linnikFixedCollisionFiber k r X hr h ij).card ^ 2)
  let S2 := Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
    (linnikCollisionFiber k r X hr h).card ^ 2)
  have hbase := sum_sq_linnikCollisionFiber_le_sq_mul_sum_fixed k r X hr
  have hbase' : S2 <= k ^ 2 * I.sum A := by
    unfold S2 I A
    rw [Finset.sum_comm]
    exact hbase
  have hmpos : 0 < k * r := lt_of_lt_of_le (by omega) hm
  have hA : forall ij, Membership.mem I ij ->
      A ij ^ (k * r) <=
        vinogradovMeanValue k (k * r) X ^ (k * r - 1) := by
    intro ij hij
    unfold A
    exact pow_sum_sq_linnikFixedCollisionFiber_le k r X hr ij hij hm
  have hagg := pow_sum_le_card_pow_mul_of_pow_le I A (k * r)
    (vinogradovMeanValue k (k * r) X ^ (k * r - 1)) hmpos hA
  have hpow := Nat.pow_le_pow_left hbase' (k * r)
  unfold S2 I A at hpow hagg
  rw [mul_pow] at hpow
  calc
    _ <= (k ^ 2) ^ (k * r) *
        (Finset.sum (linnikCollisionIndexPairs k) (fun ij =>
          Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
            (linnikFixedCollisionFiber k r X hr h ij).card ^ 2))) ^
          (k * r) := hpow
    _ <= (k ^ 2) ^ (k * r) *
        ((linnikCollisionIndexPairs k).card ^ (k * r) *
          vinogradovMeanValue k (k * r) X ^ (k * r - 1)) := by
      gcongr
    _ = _ := by ring

/-- Explicit collision-branch bound after eliminating the remaining index
cardinality by `#collisionPairs <= k^2`. -/
theorem pow_sum_sq_linnikCollisionFiber_le_explicit
    (k r X : Nat) (hr : 0 < r) (hm : 2 <= k * r) :
    (Finset.sum (linnikMomentPowerSumRange k r X) (fun h =>
      (linnikCollisionFiber k r X hr h).card ^ 2)) ^ (k * r) <=
      k ^ (4 * (k * r)) *
        vinogradovMeanValue k (k * r) X ^ (k * r - 1) := by
  have h := pow_sum_sq_linnikCollisionFiber_le k r X hr hm
  have hcard := Nat.pow_le_pow_left
    (card_linnikCollisionIndexPairs_le_sq k) (k * r)
  calc
    _ <= (k ^ 2) ^ (k * r) *
        (linnikCollisionIndexPairs k).card ^ (k * r) *
          vinogradovMeanValue k (k * r) X ^ (k * r - 1) := h
    _ <= (k ^ 2) ^ (k * r) * (k ^ 2) ^ (k * r) *
          vinogradovMeanValue k (k * r) X ^ (k * r - 1) := by
      gcongr
    _ = k ^ (4 * (k * r)) *
          vinogradovMeanValue k (k * r) X ^ (k * r - 1) := by
      rw [<- pow_add, <- pow_mul]
      congr 2
      omega

end Finset

namespace AddCircle

/-- Doubling every integer frequency preserves the zero-difference pair
count. -/
theorem integerPairCount_zero_two_mul
    {I : Type*} (A : Finset I) (q : I -> Int) :
    integerPairCount A (fun i => 2 * q i) 0 = integerPairCount A q 0 := by
  classical
  unfold integerPairCount
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply if_congr
  next =>
    rw [show 2 * q i - 2 * q j = 2 * (q i - q j) by ring]
    simp
  next => rfl
  next => rfl

end AddCircle

namespace Finset

/-- Doubling every tuple frequency is the full Fourier sum evaluated at the
doubled circle argument. -/
theorem linnikMomentDoubleFullFourierSum_eq_pow
    (k r X : Nat) (t : AddCircle (1 : Real)) :
    (Finset.univ : Finset (Fin (k * r) -> Fin X)).sum
        (fun v => fourier
          (2 * (linnikMomentFrequency k r X v : Int)) t) =
      linnikMomentAtomFourierSum k r X (t + t) ^ (k * r) := by
  rw [<- linnikMomentFullFourierSum_eq_pow]
  apply Finset.sum_congr rfl
  intro v hv
  rw [show 2 * (linnikMomentFrequency k r X v : Int) =
    (linnikMomentFrequency k r X v : Int) +
      (linnikMomentFrequency k r X v : Int) by ring]
  rw [fourier_add]
  simp_rw [fourier_apply]
  rw [zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- The full `2 * k * r` moment of the one-coordinate sum is exactly the
Vinogradov mean-value count. -/
theorem integral_norm_linnikMomentAtomFourierSum_pow
    (k r X : Nat) :
    MeasureTheory.integral AddCircle.haarAddCircle
        (fun t : AddCircle (1 : Real) =>
          norm (linnikMomentAtomFourierSum k r X t) ^ (2 * (k * r))) =
      (vinogradovMeanValue k (k * r) X : Real) := by
  have h := AddCircle.integerPairCount_zero_integral
    (Finset.univ : Finset (Fin (k * r) -> Fin X))
    (fun v => (linnikMomentFrequency k r X v : Int))
  rw [<- vinogradovMeanValue_eq_integerPairCount] at h
  simp_rw [linnikMomentFullFourierSum_eq_pow, norm_pow, <- pow_mul] at h
  simpa only [Nat.mul_comm] using h

/-- The same full moment at the doubled circle argument is also exactly the
Vinogradov mean-value count. -/
theorem integral_norm_linnikMomentAtomFourierSum_add_self_pow
    (k r X : Nat) :
    MeasureTheory.integral AddCircle.haarAddCircle
        (fun t : AddCircle (1 : Real) =>
          norm (linnikMomentAtomFourierSum k r X (t + t)) ^
            (2 * (k * r))) =
      (vinogradovMeanValue k (k * r) X : Real) := by
  have h := AddCircle.integerPairCount_zero_integral
    (Finset.univ : Finset (Fin (k * r) -> Fin X))
    (fun v => 2 * (linnikMomentFrequency k r X v : Int))
  rw [AddCircle.integerPairCount_zero_two_mul] at h
  rw [<- vinogradovMeanValue_eq_integerPairCount] at h
  simp_rw [linnikMomentDoubleFullFourierSum_eq_pow, norm_pow, <- pow_mul] at h
  simpa only [Nat.mul_comm] using h

/-- The actual fixed-collision pair count is the mixed Fourier moment to
which the Holder estimate is applied. -/
theorem integral_linnikFixedCollision_eq_pairCount
    (k r X : Nat) (hr : 0 < r)
    (ij : Prod (Fin k) (Fin k))
    (hij : Membership.mem (linnikCollisionIndexPairs k) ij) :
    MeasureTheory.integral AddCircle.haarAddCircle
        (fun t : AddCircle (1 : Real) =>
          norm (linnikMomentAtomFourierSum k r X (t + t)) ^ 2 *
            norm (linnikMomentAtomFourierSum k r X t) ^
              (2 * (k * r - 2))) =
      (linnikFixedCollisionPairCount k r X hr ij : Real) := by
  have h := AddCircle.integerPairCount_zero_integral
    (linnikFixedCollisionTuples k r X hr ij)
    (fun v => (linnikMomentFrequency k r X v : Int))
  rw [<- linnikFixedCollisionPairCount_eq_integerPairCount] at h
  simp_rw [linnikFixedCollisionFourierSum_eq k r X hr ij hij,
    linnikMomentAtomSquareSum_eq_double] at h
  simp_rw [norm_mul, norm_pow, mul_pow] at h
  simpa only [pow_mul'] using h

end Finset
