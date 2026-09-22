/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
/-
# Unit-scale energy identities

This module packages finite unit-scale quadratic energies and the comparison
lemmas needed by the analytic sieve arguments.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Reciprocal-frequency bounds from unit-scale energy

For nonnegative weights on a finite set of real frequencies in [-U,U],
the full reciprocal-distance quadratic form is at most
(5+2*log(2*U+2)) times the form retaining distances at most one.

The proof groups frequencies by integer floor, retains the exact diagonal
bin mass, and bounds the complete symmetric discrete kernel by a harmonic
sum. The quadruple specialization applies to pair sums of frequencies.
All finite domains, repeated frequencies, signed heights and weights remain
explicit; no arithmetic density or zero-energy estimate is assumed.
-/

set_option autoImplicit false

namespace Real

/- The finite Schur proof is adapted (namespace, ASCII notation and narrow
imports) from BombieriVinogradov.LargeSieve.schurBoundFinset, Apache-2.0,
kimihiro64/bombieri-vinogradov at a3e854cfb406150a07e56d85105215fe863fe240,
BombieriVinogradov/Proof/LargeSieve/Schur.lean. -/
private theorem symmetric_kernel_sum_le {I : Type*} (A : Finset I)
    (k : I -> I -> Real)
    (hk : forall i, (A : Set I) i -> forall j, (A : Set I) j -> 0 <= k i j)
    (hs : forall i, (A : Set I) i -> forall j, (A : Set I) j -> k i j = k j i)
    {B : Real} (hrow : forall i, (A : Set I) i -> Finset.sum A (k i) <= B)
    (b : I -> Real) :
    Finset.sum A (fun i => Finset.sum A (fun j => b i*b j*k i j)) <=
      B*Finset.sum A (fun i => b i^2) := by
  have hpoint (i : I) (hi : (A : Set I) i) (j : I) (hj : (A : Set I) j) :
      2*(b i*b j*k i j) <= b i^2*k i j+b j^2*k i j := by
    have hab : 2*(b i*b j) <= b i^2+b j^2 := by
      nlinarith [sq_nonneg (b i-b j)]
    nlinarith [mul_le_mul_of_nonneg_right hab (hk i hi j hj)]
  have hcol (j : I) (hj : (A : Set I) j) :
      Finset.sum A (fun i => k i j) <= B := by
    calc
      _ = Finset.sum A (fun i => k j i) :=
        Finset.sum_congr rfl (fun i hi => hs i hi j hj)
      _ <= B := hrow j hj
  have hdouble :
      2*Finset.sum A (fun i => Finset.sum A (fun j => b i*b j*k i j)) <=
      2*(B*Finset.sum A (fun i => b i^2)) := by
    calc
      _ = Finset.sum A (fun i => Finset.sum A (fun j => 2*(b i*b j*k i j))) := by
        simp_rw [Finset.mul_sum]
      _ <= Finset.sum A (fun i => Finset.sum A (fun j =>
          b i^2*k i j+b j^2*k i j)) :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpoint i hi j hj))
      _ = Finset.sum A (fun i => b i^2*Finset.sum A (k i))+
          Finset.sum A (fun i => Finset.sum A (fun j => b j^2*k i j)) := by
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = Finset.sum A (fun i => b i^2*Finset.sum A (k i))+
          Finset.sum A (fun j => b j^2*Finset.sum A (fun i => k i j)) := by
        congr 1
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ <= Finset.sum A (fun i => b i^2*B)+Finset.sum A (fun j => b j^2*B) :=
        add_le_add
          (Finset.sum_le_sum (fun i hi =>
            mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg (b i))))
          (Finset.sum_le_sum (fun j hj =>
            mul_le_mul_of_nonneg_left (hcol j hj) (sq_nonneg (b j))))
      _ = _ := by
        simp_rw [<- Finset.sum_mul]
        ring
  linarith

noncomputable def unitBinKernel (m : Int) : Real :=
  1 / max 1 (abs (m : Real)-1)

theorem unitBinKernel_nonneg (m : Int) : 0 <= unitBinKernel m :=
  div_nonneg (by norm_num) (le_trans (by norm_num : (0 : Real) <= 1) (le_max_left _ _))

theorem unitBinKernel_neg (m : Int) : unitBinKernel (-m) = unitBinKernel m := by
  simp only [unitBinKernel, Int.cast_neg, abs_neg]

theorem reciprocal_frequency_le_unitBinKernel (x y : Real) :
    1 / max 1 (abs (x-y)) <= unitBinKernel (Int.floor x-Int.floor y) := by
  have hf : abs ((Int.floor x : Real)-(Int.floor y : Real)) <= abs (x-y)+1 := by
    apply abs_le.mpr
    constructor
    next =>
      linarith [Int.floor_le y, Int.lt_floor_add_one x, neg_abs_le (x-y)]
    next =>
      linarith [Int.floor_le x, Int.lt_floor_add_one y, le_abs_self (x-y)]
  have hden : max 1 (abs ((Int.floor x : Real)-(Int.floor y : Real))-1) <=
      max 1 (abs (x-y)) := by
    apply max_le (le_max_left _ _)
    exact (by linarith : abs ((Int.floor x : Real)-(Int.floor y : Real))-1 <=
      abs (x-y)).trans (le_max_right _ _)
  unfold unitBinKernel
  rw [Int.cast_sub]
  exact div_le_div_of_nonneg_left (by norm_num)
    (lt_of_lt_of_le (by norm_num : (0 : Real) < 1) (le_max_left _ _)) hden

theorem unitBinKernel_nat_add_two (n : Nat) :
    unitBinKernel ((n+2 : Nat) : Int) = 1/((n : Real)+1) := by
  have hn : (0 : Real) <= n := Nat.cast_nonneg n
  simp only [unitBinKernel]
  push_cast
  rw [abs_of_nonneg (by linarith), show (n : Real)+2-1 = (n : Real)+1 by ring,
    max_eq_right (by linarith)]

theorem sum_unitBinKernel_interval (n : Nat) :
    Finset.sum (Finset.Icc (-((n+1 : Nat) : Int)) ((n+1 : Nat) : Int))
      unitBinKernel = 3+2*(harmonic n : Real) := by
  induction n with
  | zero =>
    norm_num [Int.Icc_eq_finset_map, Finset.sum_map, Finset.sum_range_succ,
      unitBinKernel, harmonic]
    change Finset.sum (Finset.range 3)
      (fun x : Nat => Inv.inv (max (1 : Real) (abs (-1+(x : Real))-1))) = 3
    norm_num [Finset.sum_range_succ]
  | succ n ih =>
    have hsplit :
        Finset.Icc (-((n+2 : Nat) : Int)) ((n+2 : Nat) : Int) =
        Union.union
          (Finset.Icc (-((n+1 : Nat) : Int)) ((n+1 : Nat) : Int))
          ({-((n+2 : Nat) : Int), ((n+2 : Nat) : Int)} : Finset Int) := by
      convert Finset.Icc_succ_succ (n+1) (n+1) using 1 <;> push_cast <;> ring
    have hd : Disjoint
        (Finset.Icc (-((n+1 : Nat) : Int)) ((n+1 : Nat) : Int))
        ({-((n+2 : Nat) : Int), ((n+2 : Nat) : Int)} : Finset Int) := by
      apply Finset.disjoint_left.mpr
      intro m hm hm2
      simp only [Finset.mem_Icc] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm2
      have hn : (0 : Int) <= n := Int.natCast_nonneg n
      push_cast at hm hm2
      rcases hm2 with h | h <;> omega
    have hne : Not (-((n+2 : Nat) : Int) = ((n+2 : Nat) : Int)) := by omega
    change Finset.sum (Finset.Icc (-((n+2 : Nat) : Int)) ((n+2 : Nat) : Int))
      unitBinKernel = _
    rw [hsplit, Finset.sum_union hd, Finset.sum_pair hne, ih, unitBinKernel_neg,
      unitBinKernel_nat_add_two, harmonic_succ]
    push_cast
    ring


theorem unitBinKernel_row_le_harmonic (A : Finset Int) {R : Nat} (hR : 1 <= R)
    (hA : forall m, (A : Set Int) m -> -(R : Int) <= m /\ m <= (R : Int))
    {r : Int} (hr : -(R : Int) <= r /\ r <= (R : Int)) :
    Finset.sum A (fun s => unitBinKernel (r-s)) <=
      3+2*(harmonic (2*R-1) : Real) := by
  classical
  have hsub : Finset.image (fun s : Int => r-s) A <=
      Finset.Icc (-((2*R-1+1 : Nat) : Int)) ((2*R-1+1 : Nat) : Int) := by
    intro d hd
    obtain h := Finset.mem_image.mp hd
    have hs := hA h.choose h.choose_spec.1
    rw [<- h.choose_spec.2]
    have hM : 2*R-1+1 = 2*R := by omega
    rw [hM]
    simp only [Finset.mem_Icc]
    constructor <;> omega
  calc
    _ = Finset.sum (Finset.image (fun s : Int => r-s) A) unitBinKernel := by
      symm
      apply Finset.sum_image (s := A) (g := fun s : Int => r-s) (f := unitBinKernel)
      intro a ha b hb hab
      change r-a = r-b at hab
      omega
    _ <= Finset.sum
        (Finset.Icc (-((2*R-1+1 : Nat) : Int)) ((2*R-1+1 : Nat) : Int))
        unitBinKernel :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => unitBinKernel_nonneg d)
    _ = _ := sum_unitBinKernel_interval (2*R-1)

private theorem sum_fiber_mass_mul {I J : Type*} [DecidableEq J]
    (A : Finset I) (f : I -> J) (w : I -> Real) (g : J -> Real) :
    Finset.sum (Finset.image f A) (fun r =>
      Finset.sum (Finset.filter (fun i => f i = r) A) w * g r) =
      Finset.sum A (fun i => w i*g (f i)) := by
  classical
  calc
    _ = Finset.sum (Finset.image f A) (fun r =>
        Finset.sum (Finset.filter (fun i => f i = r) A) (fun i => w i*g (f i))) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image_of_mem f hi) (fun i => w i*g (f i))

theorem sum_reciprocal_frequency_le_unit_scale {I : Type*}
    (A : Finset I) (frequency weight : I -> Real)
    (hw : forall i, (A : Set I) i -> 0 <= weight i)
    {U : Real} (hU : 1 <= U)
    (hf : forall i, (A : Set I) i -> abs (frequency i) <= U) :
    Finset.sum A (fun i => Finset.sum A (fun j =>
      weight i*weight j/max 1 (abs (frequency i-frequency j)))) <=
      (5+2*Real.log (2*U+2))*Finset.sum A (fun i => Finset.sum A (fun j =>
        if abs (frequency i-frequency j) <= 1 then weight i*weight j else 0)) := by
  classical
  let f : I -> Int := fun i => Int.floor (frequency i)
  let B : Finset Int := Finset.image f A
  let b : Int -> Real := fun r => Finset.sum (Finset.filter (fun i => f i = r) A) weight
  let R : Nat := Nat.ceil U
  have hU0 : 0 < U := by linarith
  have hR : 1 <= R := Nat.one_le_of_lt (Nat.ceil_pos.mpr hU0)
  have hceil : U <= (R : Real) := Nat.le_ceil U
  have hceil2 : (R : Real) < U+1 := Nat.ceil_lt_add_one hU0.le
  have hfloor (i : I) (hi : (A : Set I) i) :
      -(R : Int) <= f i /\ f i <= (R : Int) := by
    have hfi := abs_le.mp (hf i hi)
    constructor
    next =>
      apply Int.le_floor.mpr
      push_cast
      linarith
    next =>
      have hle : (Int.floor (frequency i) : Real) <= (R : Real) :=
        (Int.floor_le _).trans (hfi.2.trans hceil)
      exact_mod_cast hle
  have hB : forall r, (B : Set Int) r -> -(R : Int) <= r /\ r <= (R : Int) := by
    intro r hr
    obtain h := Finset.mem_image.mp hr
    rw [<- h.choose_spec.2]
    exact hfloor h.choose h.choose_spec.1
  have hM : 1 <= 2*R-1 := by omega
  have hlog : Real.log ((2*R-1 : Nat) : Real) <= Real.log (2*U+2) := by
    apply Real.log_le_log
    next =>
      exact_mod_cast (by omega : 0 < 2*R-1)
    next =>
      have hRm : ((2*R-1 : Nat) : Real) = 2*(R : Real)-1 := by
        rw [Nat.cast_sub (by omega : 1 <= 2*R)]
        push_cast
        ring
      rw [hRm]
      linarith
  have hrow (r : Int) (hr : (B : Set Int) r) :
      Finset.sum B (fun s => unitBinKernel (r-s)) <= 5+2*Real.log (2*U+2) := by
    have h0 := unitBinKernel_row_le_harmonic B hR hB (hB r hr)
    have h1 := harmonic_le_one_add_log (2*R-1)
    linarith
  have hsym (r s : Int) : unitBinKernel (r-s) = unitBinKernel (s-r) := by
    rw [show r-s = -(s-r) by omega, unitBinKernel_neg]
  have hschur := symmetric_kernel_sum_le B (fun r s => unitBinKernel (r-s))
    (fun r _ s _ => unitBinKernel_nonneg _) (fun r _ s _ => hsym r s) hrow b
  have hgroup :
      Finset.sum B (fun r => Finset.sum B (fun s => b r*b s*unitBinKernel (r-s))) =
      Finset.sum A (fun i => Finset.sum A (fun j =>
        weight i*weight j*unitBinKernel (f i-f j))) := by
    calc
      _ = Finset.sum B (fun r => b r*Finset.sum B (fun s => b s*unitBinKernel (r-s))) := by
        simp_rw [Finset.mul_sum, mul_assoc]
      _ = Finset.sum A (fun i =>
          weight i*Finset.sum B (fun s => b s*unitBinKernel (f i-s))) :=
        sum_fiber_mass_mul A f weight (fun r =>
          Finset.sum B (fun s => b s*unitBinKernel (r-s)))
      _ = Finset.sum A (fun i =>
          weight i*Finset.sum A (fun j => weight j*unitBinKernel (f i-f j))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [sum_fiber_mass_mul A f weight (fun s => unitBinKernel (f i-s))]
      _ = _ := by simp_rw [Finset.mul_sum, mul_assoc]
  have hdiag : Finset.sum B (fun r => b r^2) =
      Finset.sum A (fun i => weight i*b (f i)) := by
    simpa only [pow_two] using sum_fiber_mass_mul A f weight b
  have hnear : Finset.sum B (fun r => b r^2) <=
      Finset.sum A (fun i => Finset.sum A (fun j =>
        if abs (frequency i-frequency j) <= 1 then weight i*weight j else 0)) := by
    rw [hdiag]
    apply Finset.sum_le_sum
    intro i hi
    change weight i * Finset.sum (Finset.filter (fun j => f j = f i) A) weight <= _
    rw [Finset.mul_sum]
    calc
      _ <= Finset.sum (Finset.filter (fun j => abs (frequency i-frequency j) <= 1) A)
          (fun j => weight i*weight j) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        next =>
          intro j hj
          have hjA := (Finset.mem_filter.mp hj).1
          have he : (Int.floor (frequency j) : Real) = (Int.floor (frequency i) : Real) :=
            congrArg (fun z : Int => (z : Real)) (Finset.mem_filter.mp hj).2
          apply Finset.mem_filter.mpr (And.intro hjA ?_)
          apply abs_le.mpr
          constructor <;> linarith [Int.floor_le (frequency i),
            Int.floor_le (frequency j), Int.lt_floor_add_one (frequency i),
            Int.lt_floor_add_one (frequency j)]
        next =>
          intro j hj _
          exact mul_nonneg (hw i hi) (hw j (Finset.mem_filter.mp hj).1)
      _ = _ := Finset.sum_filter _ _
  have hC : 0 <= 5+2*Real.log (2*U+2) := by
    have hlog0 := Real.log_nonneg (by linarith : 1 <= 2*U+2)
    linarith
  calc
    _ <= Finset.sum A (fun i => Finset.sum A (fun j =>
        weight i*weight j*unitBinKernel (f i-f j))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ = (weight i*weight j)*(1/max 1 (abs (frequency i-frequency j))) := by ring
        _ <= _ := mul_le_mul_of_nonneg_left
          (reciprocal_frequency_le_unitBinKernel (frequency i) (frequency j))
          (mul_nonneg (hw i hi) (hw j hj))
    _ <= (5+2*Real.log (2*U+2))*Finset.sum B (fun r => b r^2) := by
      rw [<- hgroup]
      exact hschur
    _ <= _ := mul_le_mul_of_nonneg_left hnear hC


theorem sum_quadruple_reciprocal_frequency_le_unit_scale {I : Type*}
    (A : Finset I) (frequency weight : I -> Real)
    (hw : forall i, (A : Set I) i -> 0 <= weight i)
    {T : Real} (hT : 1 <= T)
    (hf : forall i, (A : Set I) i -> abs (frequency i) <= T) :
    Finset.sum A (fun i => Finset.sum A (fun j => Finset.sum A (fun k =>
      Finset.sum A (fun l =>
        ((weight i*weight j)*(weight k*weight l))/
          max 1 (abs (frequency i+frequency j-frequency k-frequency l)))))) <=
      (5+2*Real.log (4*T+2))*Finset.sum A (fun i => Finset.sum A (fun j =>
        Finset.sum A (fun k => Finset.sum A (fun l =>
          if abs (frequency i+frequency j-frequency k-frequency l) <= 1
          then (weight i*weight j)*(weight k*weight l) else 0)))) := by
  have hp : forall p, ((SProd.sprod A A : Finset (Prod I I)) : Set (Prod I I)) p ->
      abs (frequency p.1+frequency p.2) <= 2*T := by
    intro p hp
    have hi := (Finset.mem_product.mp hp).1
    have hj := (Finset.mem_product.mp hp).2
    calc
      _ <= abs (frequency p.1)+abs (frequency p.2) := abs_add_le _ _
      _ <= _ := by linarith [hf p.1 hi, hf p.2 hj]
  have h := sum_reciprocal_frequency_le_unit_scale
    (SProd.sprod A A : Finset (Prod I I))
    (fun p => frequency p.1+frequency p.2) (fun p => weight p.1*weight p.2)
    (fun p hp => mul_nonneg (hw p.1 (Finset.mem_product.mp hp).1)
      (hw p.2 (Finset.mem_product.mp hp).2))
    (by linarith : 1 <= 2*T) hp
  have he (i j k l : I) :
      frequency i+frequency j-(frequency k+frequency l) =
      frequency i+frequency j-frequency k-frequency l := by ring
  simp only [Finset.sum_product] at h
  simp_rw [he] at h
  rw [show 2*(2*T)+2 = 4*T+2 by ring] at h
  exact h

end Real
