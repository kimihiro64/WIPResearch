/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.LinnikFourier
import RobinBV.Mathlib.Analysis.Complex.LinnikResidueHolder
import RobinBV.Sieve.Proof.LinnikVMTechKernelProduct

/-!
# Holder expansions for Vinogradov's technical estimate

This module supplies the two exact algebraic steps surrounding the
degree-by-degree kernel product in Theorem 24.7: the outer finite Holder
inequality and the paired tuple expansion of an even moment.  No asymptotic
constant or coefficient packet is discarded.
-/

open Complex

theorem linnik_vmtech_outer_holder
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (f : I -> J -> Complex) (b : Nat) (hb : 0 < b) :
    norm (Finset.univ.sum (fun i => Finset.univ.sum (f i))) ^ (2 * b) <=
      Fintype.card I ^ (2 * b - 1) *
        Finset.univ.sum (fun i =>
          norm (Finset.univ.sum (f i)) ^ (2 * b)) := by
  exact Finset.norm_sum_pow_le_card_pow_mul_sum_norm_pow
    (fun i => Finset.univ.sum (f i)) (2 * b) (Nat.mul_pos (by omega) hb)

theorem linnik_vmtech_even_moment_tuple_expansion
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I -> Complex) (b : Nat) :
    ((norm (Finset.univ.sum f) ^ (2 * b) : Real) : Complex) =
      (Finset.univ.sum (fun u : Fin b -> I =>
        Finset.univ.prod (fun i => f (u i)))) *
      (Finset.univ.sum (fun v : Fin b -> I =>
        Finset.univ.prod (fun i => star (f (v i))))) := by
  let S : Complex := Finset.univ.sum f
  have hconj : Finset.univ.sum (fun i => star (f i)) = star S := by
    simp [S]
  have hleft :
      ((norm S ^ (2 * b) : Real) : Complex) =
        S ^ b * (star S) ^ b := by
    calc
      ((norm S ^ (2 * b) : Real) : Complex) =
          (((norm S ^ 2 : Real) : Complex)) ^ b := by
        rw [pow_mul]
        norm_cast
      _ = (S * star S) ^ b := by
        congr 1
        calc
          (((norm S ^ 2 : Real) : Complex)) =
              ((norm S : Real) : Complex) ^ 2 := by norm_cast
          _ = S * star S := (Complex.mul_conj' S).symm
      _ = S ^ b * (star S) ^ b := by
        rw [mul_pow]
  rw [hleft, <- hconj]
  rw [Fintype.sum_pow, Fintype.sum_pow]

theorem linnik_vmtech_star_exp_I_mul_real (x : Real) :
    star (Complex.exp (Complex.I * (x : Complex))) =
      Complex.exp (Complex.I * ((-x : Real) : Complex)) := by
  have h := (Complex.exp_conj (x := Complex.I * (x : Complex))).symm
  simpa using h

theorem linnik_vmtech_exp_pair_product
    {I : Type*} [Fintype I] [DecidableEq I]
    (phase : I -> Real) (b : Nat)
    (u v : Fin b -> I) :
    (Finset.univ.prod (fun i =>
      Complex.exp (Complex.I * (phase (u i) : Complex)))) *
      (Finset.univ.prod (fun i =>
        star (Complex.exp (Complex.I * (phase (v i) : Complex))))) =
      Complex.exp (Complex.I *
        ((Finset.univ.sum (fun i => phase (u i)) -
          Finset.univ.sum (fun i => phase (v i)) : Real) : Complex)) := by
  have hu :
      Finset.univ.prod (fun i =>
        Complex.exp (Complex.I * (phase (u i) : Complex))) =
      Complex.exp (Complex.I *
        (Finset.univ.sum (fun i => phase (u i)) : Complex)) := by
    rw [<- Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
  have hv :
      Finset.univ.prod (fun i =>
        star (Complex.exp (Complex.I * (phase (v i) : Complex)))) =
      Complex.exp (Complex.I *
        ((-Finset.univ.sum (fun i => phase (v i)) : Real) : Complex)) := by
    simp_rw [linnik_vmtech_star_exp_I_mul_real]
    rw [<- Complex.exp_sum]
    congr 1
    push_cast
    calc
      Finset.univ.sum (fun i =>
          Complex.I * -((phase (v i) : Real) : Complex)) =
          Finset.univ.sum (fun i =>
            -(Complex.I * ((phase (v i) : Real) : Complex))) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = -Finset.univ.sum (fun i =>
          Complex.I * ((phase (v i) : Real) : Complex)) := by
        simp
      _ = -(Complex.I * Finset.univ.sum (fun i =>
          ((phase (v i) : Real) : Complex))) := by
        rw [Finset.mul_sum]
      _ = Complex.I * -Finset.univ.sum (fun i =>
          ((phase (v i) : Real) : Complex)) := by ring
  rw [hu, hv, <- Complex.exp_add]
  congr 1
  push_cast
  ring

theorem linnik_vmtech_even_moment_expansion
    {I : Type*} [Fintype I] [DecidableEq I]
    (phase : I -> Real) (b : Nat) :
    ((norm (Finset.univ.sum (fun i =>
        Complex.exp (Complex.I * (phase i : Complex)))) ^
          (2 * b) : Real) : Complex) =
      Finset.univ.sum (fun u : Fin b -> I =>
        Finset.univ.sum (fun v : Fin b -> I =>
          Complex.exp (Complex.I *
            ((Finset.univ.sum (fun i => phase (u i)) -
              Finset.univ.sum (fun i => phase (v i)) : Real) : Complex)))) := by
  rw [linnik_vmtech_even_moment_tuple_expansion]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  exact linnik_vmtech_exp_pair_product phase b u v

noncomputable def linnikVMTechPolynomialPhase
    {k : Nat} (alpha : Fin k -> Real) (n : Nat) : Real :=
  Finset.univ.sum (fun j => alpha j * (n : Real) ^ (j.val + 1))

noncomputable def linnikVMTechPowerDifferenceReal
    {I : Type*} [Fintype I] {b k : Nat}
    (m : I -> Nat) (u v : Fin b -> I) (j : Fin k) : Real :=
  Finset.univ.sum (fun i => (m (u i) : Real) ^ (j.val + 1)) -
    Finset.univ.sum (fun i => (m (v i) : Real) ^ (j.val + 1))

noncomputable def linnikVMTechPowerDifference
    {I : Type*} [Fintype I] {b k : Nat}
    (m : I -> Nat) (u v : Fin b -> I) (j : Fin k) : Int :=
  (Finset.univ.sum (fun i => m (u i) ^ (j.val + 1)) : Nat) -
    (Finset.univ.sum (fun i => m (v i) ^ (j.val + 1)) : Nat)

theorem linnikVMTechPowerDifference_cast
    {I : Type*} [Fintype I] {b k : Nat}
    (m : I -> Nat) (u v : Fin b -> I) (j : Fin k) :
    (linnikVMTechPowerDifference m u v j : Real) =
      linnikVMTechPowerDifferenceReal m u v j := by
  simp only [linnikVMTechPowerDifference, linnikVMTechPowerDifferenceReal]
  push_cast
  rfl

theorem linnik_vmtech_frequency_shift_count_le_vmvt
    (k r X : Nat) (h : Int) :
    AddCircle.integerPairCount
        (Finset.univ : Finset (Fin (k * r) -> Fin X))
        (fun v => (Finset.linnikMomentFrequency k r X v : Int)) h <=
      (Finset.vinogradovMeanValue k (k * r) X : Real) := by
  calc
    AddCircle.integerPairCount
        (Finset.univ : Finset (Fin (k * r) -> Fin X))
        (fun v => (Finset.linnikMomentFrequency k r X v : Int)) h <=
      AddCircle.integerPairCount
        (Finset.univ : Finset (Fin (k * r) -> Fin X))
        (fun v => (Finset.linnikMomentFrequency k r X v : Int)) 0 :=
      AddCircle.integerPairCount_le_zero _ _ _
    _ = (Finset.vinogradovMeanValue k (k * r) X : Real) :=
      (Finset.vinogradovMeanValue_eq_integerPairCount k r X).symm

theorem linnik_vmtech_frequency_difference_eq
    (k r X : Nat)
    (v w : Fin (k * r) -> Fin X) :
    (Finset.linnikMomentFrequency k r X v : Int) -
        (Finset.linnikMomentFrequency k r X w : Int) =
      Finset.univ.sum (fun j : Fin k =>
        linnikVMTechPowerDifference (fun x : Fin X => x.val) v w j *
          (Finset.linnikMomentFrequencyBase k r X : Int) ^ j.val) := by
  rw [Finset.linnikMomentFrequency_eq_sum_atom,
    Finset.linnikMomentFrequency_eq_sum_atom]
  unfold Finset.linnikMomentAtomFrequency linnikVMTechPowerDifference
  push_cast
  rw [Finset.sum_comm]
  conv_lhs =>
    rhs
    rw [Finset.sum_comm]
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [<- Finset.sum_mul, <- Finset.sum_mul]
  ring

noncomputable def linnikVMTechDifferenceFiber
    (k r X : Nat) (h : Fin k -> Int) :
    Finset (Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X)) :=
  ((Finset.univ : Finset (Fin (k * r) -> Fin X)).product Finset.univ).filter
    (fun vw =>
      (fun j => linnikVMTechPowerDifference
        (fun x : Fin X => x.val) vw.fst vw.snd j) = h)

noncomputable def linnikVMTechFrequencyDifferenceFiber
    (k r X : Nat) (shift : Int) :
    Finset (Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X)) :=
  ((Finset.univ : Finset (Fin (k * r) -> Fin X)).product Finset.univ).filter
    (fun vw =>
      (Finset.linnikMomentFrequency k r X vw.fst : Int) -
        (Finset.linnikMomentFrequency k r X vw.snd : Int) = shift)

theorem linnikVMTechDifferenceFiber_subset_frequencyFiber_of_mem
    (k r X : Nat) (h : Fin k -> Int)
    (uv : Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X))
    (huv : Membership.mem (linnikVMTechDifferenceFiber k r X h) uv) :
    linnikVMTechDifferenceFiber k r X h <=
      linnikVMTechFrequencyDifferenceFiber k r X
        ((Finset.linnikMomentFrequency k r X uv.fst : Int) -
          (Finset.linnikMomentFrequency k r X uv.snd : Int)) := by
  intro zw hzw
  have huvParts := Finset.mem_filter.mp huv
  have hzwParts := Finset.mem_filter.mp hzw
  apply Finset.mem_filter.mpr
  constructor
  next => exact hzwParts.1
  next =>
    rw [linnik_vmtech_frequency_difference_eq,
      linnik_vmtech_frequency_difference_eq]
    apply Finset.sum_congr rfl
    intro j hj
    have hzwj := congrFun hzwParts.2 j
    have huvj := congrFun huvParts.2 j
    rw [hzwj, huvj]

theorem linnikVMTechFrequencyDifferenceFiber_card_eq_integerPairCount
    (k r X : Nat) (shift : Int) :
    ((linnikVMTechFrequencyDifferenceFiber k r X shift).card : Real) =
      AddCircle.integerPairCount
        (Finset.univ : Finset (Fin (k * r) -> Fin X))
        (fun v => (Finset.linnikMomentFrequency k r X v : Int)) shift := by
  unfold linnikVMTechFrequencyDifferenceFiber
    AddCircle.integerPairCount
  rw [Finset.card_filter]
  norm_cast
  simp only [Int.subNatNat_eq_coe]
  change
    (Finset.univ.product Finset.univ).sum (fun vw =>
      if (Finset.linnikMomentFrequency k r X vw.fst : Int) -
          (Finset.linnikMomentFrequency k r X vw.snd : Int) = shift then
        1
      else 0) =
    Finset.univ.sum (fun i =>
      Finset.univ.sum (fun j =>
        if (Finset.linnikMomentFrequency k r X i : Int) -
            (Finset.linnikMomentFrequency k r X j : Int) = shift then
          1
        else 0))
  exact Finset.sum_product
    (s := (Finset.univ : Finset (Fin (k * r) -> Fin X)))
    (t := (Finset.univ : Finset (Fin (k * r) -> Fin X)))
    (f := fun vw =>
      if (Finset.linnikMomentFrequency k r X vw.fst : Int) -
          (Finset.linnikMomentFrequency k r X vw.snd : Int) = shift then
        (1 : Nat)
      else 0)

theorem linnikVMTechDifferenceFiber_card_le_vmvt
    (k r X : Nat) (h : Fin k -> Int) :
    ((linnikVMTechDifferenceFiber k r X h).card : Real) <=
      (Finset.vinogradovMeanValue k (k * r) X : Real) := by
  by_cases hempty : linnikVMTechDifferenceFiber k r X h = {}
  next =>
    rw [hempty]
    simp
  next =>
    have hnonempty :
        (linnikVMTechDifferenceFiber k r X h).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    choose uv huv using hnonempty
    have hsub :=
      linnikVMTechDifferenceFiber_subset_frequencyFiber_of_mem
        k r X h uv huv
    have hcardNat := Finset.card_le_card hsub
    have hcardReal :
        ((linnikVMTechDifferenceFiber k r X h).card : Real) <=
          ((linnikVMTechFrequencyDifferenceFiber k r X
            ((Finset.linnikMomentFrequency k r X uv.fst : Int) -
              (Finset.linnikMomentFrequency k r X uv.snd : Int))).card :
                Real) := by
      exact_mod_cast hcardNat
    calc
      ((linnikVMTechDifferenceFiber k r X h).card : Real) <=
          ((linnikVMTechFrequencyDifferenceFiber k r X
            ((Finset.linnikMomentFrequency k r X uv.fst : Int) -
              (Finset.linnikMomentFrequency k r X uv.snd : Int))).card :
                Real) := hcardReal
      _ = AddCircle.integerPairCount
          (Finset.univ : Finset (Fin (k * r) -> Fin X))
          (fun v => (Finset.linnikMomentFrequency k r X v : Int))
          ((Finset.linnikMomentFrequency k r X uv.fst : Int) -
            (Finset.linnikMomentFrequency k r X uv.snd : Int)) :=
        linnikVMTechFrequencyDifferenceFiber_card_eq_integerPairCount
          k r X _
      _ <= (Finset.vinogradovMeanValue k (k * r) X : Real) :=
        linnik_vmtech_frequency_shift_count_le_vmvt k r X _

noncomputable def linnikVMTechDifferenceRange
    (k r X : Nat) : Finset (Fin k -> Int) :=
  ((Finset.univ : Finset (Fin (k * r) -> Fin X)).product Finset.univ).image
    (fun vw j => linnikVMTechPowerDifference
      (fun x : Fin X => x.val) vw.fst vw.snd j)

theorem linnik_vmtech_sum_group_by_power_difference
    (k r X : Nat) (weight : (Fin k -> Int) -> Complex) :
    ((Finset.univ : Finset (Fin (k * r) -> Fin X)).product Finset.univ).sum
        (fun vw => weight (fun j => linnikVMTechPowerDifference
          (fun x : Fin X => x.val) vw.fst vw.snd j)) =
      (linnikVMTechDifferenceRange k r X).sum (fun h =>
        ((linnikVMTechDifferenceFiber k r X h).card : Complex) * weight h) := by
  let pairs :=
    (Finset.univ : Finset (Fin (k * r) -> Fin X)).product
      (Finset.univ : Finset (Fin (k * r) -> Fin X))
  let diff :
      Prod (Fin (k * r) -> Fin X) (Fin (k * r) -> Fin X) ->
        (Fin k -> Int) :=
    fun vw j => linnikVMTechPowerDifference
      (fun x : Fin X => x.val) vw.fst vw.snd j
  have hmaps : forall vw, Membership.mem pairs vw ->
      Membership.mem (pairs.image diff) (diff vw) := by
    intro vw hvw
    exact Finset.mem_image.mpr (Exists.intro vw (And.intro hvw rfl))
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun vw => weight (diff vw))
  rw [<- hfiber]
  change (pairs.image diff).sum (fun h =>
      (pairs.filter (fun vw => diff vw = h)).sum
        (fun vw => weight (diff vw))) =
    (pairs.image diff).sum (fun h =>
      ((pairs.filter (fun vw => diff vw = h)).card : Complex) * weight h)
  apply Finset.sum_congr rfl
  intro h hh
  calc
    (pairs.filter (fun vw => diff vw = h)).sum
        (fun vw => weight (diff vw)) =
      (pairs.filter (fun vw => diff vw = h)).sum
        (fun _ => weight h) := by
      apply Finset.sum_congr rfl
      intro vw hvw
      rw [(Finset.mem_filter.mp hvw).2]
    _ = ((pairs.filter (fun vw => diff vw = h)).card : Complex) *
        weight h := by simp

theorem linnik_vmtech_pair_sum_norm_le_vmvt_mul_sum_norm
    (k r X : Nat) (weight : (Fin k -> Int) -> Complex) :
    norm (((Finset.univ : Finset (Fin (k * r) -> Fin X)).product
      (Finset.univ : Finset (Fin (k * r) -> Fin X))).sum (fun vw =>
        weight (fun j => linnikVMTechPowerDifference
          (fun x : Fin X => x.val) vw.fst vw.snd j))) <=
      (Finset.vinogradovMeanValue k (k * r) X : Real) *
        (linnikVMTechDifferenceRange k r X).sum (fun h =>
          norm (weight h)) := by
  rw [linnik_vmtech_sum_group_by_power_difference]
  calc
    norm ((linnikVMTechDifferenceRange k r X).sum (fun h =>
        ((linnikVMTechDifferenceFiber k r X h).card : Complex) * weight h)) <=
      (linnikVMTechDifferenceRange k r X).sum (fun h =>
        norm (((linnikVMTechDifferenceFiber k r X h).card : Complex) *
          weight h)) := norm_sum_le _ _
    _ = (linnikVMTechDifferenceRange k r X).sum (fun h =>
        ((linnikVMTechDifferenceFiber k r X h).card : Real) *
          norm (weight h)) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [norm_mul]
      simp
    _ <= (linnikVMTechDifferenceRange k r X).sum (fun h =>
        (Finset.vinogradovMeanValue k (k * r) X : Real) *
          norm (weight h)) := by
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_right
        (linnikVMTechDifferenceFiber_card_le_vmvt k r X h)
        (norm_nonneg (weight h))
    _ = (Finset.vinogradovMeanValue k (k * r) X : Real) *
        (linnikVMTechDifferenceRange k r X).sum (fun h =>
          norm (weight h)) := by
      rw [Finset.mul_sum]

theorem linnik_vmtech_polynomial_pair_phase
    {I : Type*} [Fintype I] [DecidableEq I]
    {b k : Nat} (alpha : Fin k -> Real) (m : I -> Nat)
    (l : Nat) (u v : Fin b -> I) :
    Finset.univ.sum (fun i =>
        linnikVMTechPolynomialPhase alpha (l * m (u i))) -
      Finset.univ.sum (fun i =>
        linnikVMTechPolynomialPhase alpha (l * m (v i))) =
      Finset.univ.sum (fun j =>
        alpha j * (l : Real) ^ (j.val + 1) *
          linnikVMTechPowerDifferenceReal m u v j) := by
  unfold linnikVMTechPolynomialPhase linnikVMTechPowerDifferenceReal
  simp_rw [Nat.cast_mul, mul_pow]
  rw [Finset.sum_comm]
  rw [show Finset.univ.sum (fun i =>
      Finset.univ.sum (fun j =>
        alpha j * ((l : Real) ^ (j.val + 1) *
          (m (v i) : Real) ^ (j.val + 1)))) =
      Finset.univ.sum (fun j =>
        Finset.univ.sum (fun i =>
          alpha j * ((l : Real) ^ (j.val + 1) *
            (m (v i) : Real) ^ (j.val + 1)))) by
        exact Finset.sum_comm]
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [<- mul_assoc]
  rw [<- Finset.mul_sum, <- Finset.mul_sum]
  ring

theorem linnik_vmtech_polynomial_even_moment_expansion
    {I : Type*} [Fintype I] [DecidableEq I]
    {b k : Nat} (alpha : Fin k -> Real) (m : I -> Nat) (l : Nat) :
    ((norm (Finset.univ.sum (fun x =>
        Complex.exp (Complex.I *
          (linnikVMTechPolynomialPhase alpha (l * m x) : Complex)))) ^
          (2 * b) : Real) : Complex) =
      Finset.univ.sum (fun u : Fin b -> I =>
        Finset.univ.sum (fun v : Fin b -> I =>
          Complex.exp (Complex.I *
            (Finset.univ.sum (fun j =>
              alpha j * (l : Real) ^ (j.val + 1) *
                linnikVMTechPowerDifferenceReal m u v j) : Complex)))) := by
  rw [linnik_vmtech_even_moment_expansion]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [linnik_vmtech_polynomial_pair_phase]
  congr 1
  push_cast
  rfl
