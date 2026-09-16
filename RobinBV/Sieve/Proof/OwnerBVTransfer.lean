import BombieriVinogradov.Assembly.WeightedBombieriVinogradov.Main
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalPrimePowerFringe

/-!
# BV transfer with complete branch-coefficient budgets

This is a consequence of the dependency's centered maximal weighted BV
theorem. Classes and cutoffs may vary from branch to branch. The hypothesis
bounds the sum of absolute coefficients at EACH PRODUCT MODULUS, not each
individual coefficient. Constructing a sieve expansion with this budget is
a separate arithmetic obligation. A second-moment alternative below keeps
the full squared coefficient fibers and an explicit discrepancy majorant.
Neither budget is assumed for a proposed owner expansion. No RH sign or improved distribution level
is asserted here.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

open BombieriVinogradov.WeightedBombieriVinogradov

/-- A single reduced-class error is bounded by the actual BV maximal error. -/
theorem abs_progressionError_le_maximal
    {X : Real} {q y : Nat} (a : Units (ZMod q))
    (hy : y <= Nat.floor X) :
    abs (psiProgression y q (a : ZMod q) -
      psiGlobal y / (q.totient : Real)) <= maximalWeightedDiscrepancy X q := by
  let F : Units (ZMod q) -> Real := fun b =>
    iSup (fun z : Fin (Nat.floor X + 1) =>
      abs (psiProgression z.val q (b : ZMod q) -
        psiGlobal z.val / (q.totient : Real)))
  let G : Fin (Nat.floor X + 1) -> Real := fun z =>
    abs (psiProgression z.val q (a : ZMod q) -
      psiGlobal z.val / (q.totient : Real))
  let z : Fin (Nat.floor X + 1) := {
    val := y
    isLt := Nat.lt_succ_of_le hy
  }
  have hInner : G z <= iSup G := le_ciSup (Set.finite_range G).bddAbove z
  have hOuter : F a <= iSup F := le_ciSup (Set.finite_range F).bddAbove a
  exact hInner.trans hOuter

/-- The total absolute error of finitely many weighted branches at each modulus. -/
noncomputable def branchWeightedDiscrepancy (Q : Nat)
    (branches : Nat -> Finset Nat) (c : Nat -> Nat -> Real)
    (a : (q : Nat) -> Nat -> Units (ZMod q)) (y : Nat -> Nat -> Nat) : Real :=
  Finset.sum (Finset.Icc 1 Q) (fun q =>
    abs (Finset.sum (branches q) (fun i => c q i *
      (psiProgression (y q i) q (a q i : ZMod q) -
        psiGlobal (y q i) / (q.totient : Real)))))

/-- Exact finite transfer retaining the complete coefficient fiber. -/
theorem branchWeightedDiscrepancy_le
    {X M : Real} {Q : Nat}
    (branches : Nat -> Finset Nat) (c : Nat -> Nat -> Real)
    (a : (q : Nat) -> Nat -> Units (ZMod q)) (y : Nat -> Nat -> Nat)
    (hy : forall q, Membership.mem (Finset.Icc 1 Q) q ->
      forall i, Membership.mem (branches q) i -> y q i <= Nat.floor X)
    (hBudget : forall q, Membership.mem (Finset.Icc 1 Q) q ->
      Finset.sum (branches q) (fun i => abs (c q i)) <= M) :
    branchWeightedDiscrepancy Q branches c a y <=
      M * averageWeightedDiscrepancy X Q := by
  unfold branchWeightedDiscrepancy averageWeightedDiscrepancy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  calc
    abs (Finset.sum (branches q) (fun i => c q i *
        (psiProgression (y q i) q (a q i : ZMod q) -
          psiGlobal (y q i) / (q.totient : Real)))) <=
        Finset.sum (branches q) (fun i => abs (c q i *
          (psiProgression (y q i) q (a q i : ZMod q) -
            psiGlobal (y q i) / (q.totient : Real)))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum (branches q) (fun i =>
        abs (c q i) * maximalWeightedDiscrepancy X q) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_progressionError_le_maximal (a q i) (hy q hq i hi)) (abs_nonneg _)
    _ = Finset.sum (branches q) (fun i => abs (c q i)) *
        maximalWeightedDiscrepancy X q := (Finset.sum_mul _ _ _).symm
    _ <= M * maximalWeightedDiscrepancy X q :=
      mul_le_mul_of_nonneg_right (hBudget q hq)
        (maximalWeightedDiscrepancy_nonneg X q)

/-- A polylogarithmic complete coefficient budget costs only logarithmic
saving. The BV constant is uniform in every branch, class, and cutoff choice. -/
theorem ownerWeightedBVTransfer
    (theta A B : Real) (hTheta : theta < 1 / 2) (hA : 1 <= A) (hB : 0 <= B) :
    exists C : Real, And (0 < C) (forall {X : Real}, 3 <= X ->
      forall (branches : Nat -> Finset Nat) (c : Nat -> Nat -> Real)
        (a : (q : Nat) -> Nat -> Units (ZMod q)) (y : Nat -> Nat -> Nat),
      (forall q, Membership.mem (Finset.Icc 1 (Nat.floor (X ^ theta))) q ->
        forall i, Membership.mem (branches q) i -> y q i <= Nat.floor X) ->
      (forall q, Membership.mem (Finset.Icc 1 (Nat.floor (X ^ theta))) q ->
        Finset.sum (branches q) (fun i => abs (c q i)) <= (Real.log X) ^ B) ->
      branchWeightedDiscrepancy (Nat.floor (X ^ theta)) branches c a y <=
        C * (X / (Real.log X) ^ A)) := by
  have hBV := weighted_bombieri_vinogradov theta hTheta (A + B) (by linarith)
  let C := Classical.choose hBV
  have hData := Classical.choose_spec hBV
  refine Exists.intro C (And.intro hData.1 ?_)
  intro X hX branches c a y hy hBudget
  have hLog : 0 < Real.log X := Real.log_pos (by linarith)
  have hPowA : Not ((Real.log X) ^ A = 0) := (Real.rpow_pos_of_pos hLog A).ne'
  have hPowB : Not ((Real.log X) ^ B = 0) := (Real.rpow_pos_of_pos hLog B).ne'
  calc
    branchWeightedDiscrepancy (Nat.floor (X ^ theta)) branches c a y <=
        (Real.log X) ^ B * averageWeightedDiscrepancy X (Nat.floor (X ^ theta)) :=
      branchWeightedDiscrepancy_le branches c a y hy hBudget
    _ <= (Real.log X) ^ B * (C * (X / (Real.log X) ^ (A + B))) :=
      mul_le_mul_of_nonneg_left (hData.2 hX) (Real.rpow_pos_of_pos hLog B).le
    _ = C * (X / (Real.log X) ^ A) := by
      rw [Real.rpow_add hLog]
      field_simp

/-- The complete squared coefficient-fiber mass weighted by the actual maximal discrepancy. -/
noncomputable def branchCoefficientEnergy (X : Real) (Q : Nat)
    (branches : Nat -> Finset Nat) (c : Nat -> Nat -> Real) : Real :=
  Finset.sum (Finset.Icc 1 Q) (fun q =>
    (Finset.sum (branches q) (fun i => abs (c q i)))^2*maximalWeightedDiscrepancy X q)

/-- Finite weighted Cauchy gives an alternative to a uniform maximum coefficient-fiber budget. -/
theorem branchWeightedDiscrepancy_sq_le_energy {X : Real} {Q : Nat}
    (branches : Nat -> Finset Nat) (c : Nat -> Nat -> Real)
    (a : (q : Nat) -> Nat -> Units (ZMod q)) (y : Nat -> Nat -> Nat)
    (hy : forall q, Membership.mem (Finset.Icc 1 Q) q ->
      forall i, Membership.mem (branches q) i -> y q i <= Nat.floor X) :
    (branchWeightedDiscrepancy Q branches c a y)^2 <=
      averageWeightedDiscrepancy X Q*branchCoefficientEnergy X Q branches c := by
  have hpoint (q : Nat) (hq : Membership.mem (Finset.Icc 1 Q) q) :
      abs (Finset.sum (branches q) (fun i => c q i*
        (psiProgression (y q i) q (a q i : ZMod q)-psiGlobal (y q i)/(q.totient : Real)))) <=
      Finset.sum (branches q) (fun i => abs (c q i))*maximalWeightedDiscrepancy X q := by
    calc
      _ <= Finset.sum (branches q) (fun i => abs (c q i*
          (psiProgression (y q i) q (a q i : ZMod q)-psiGlobal (y q i)/(q.totient : Real)))) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum (branches q) (fun i => abs (c q i)*maximalWeightedDiscrepancy X q) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (abs_progressionError_le_maximal (a q i) (hy q hq i hi)) (abs_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  unfold branchWeightedDiscrepancy averageWeightedDiscrepancy branchCoefficientEnergy
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.Icc 1 Q)
  next => intro q hq; exact maximalWeightedDiscrepancy_nonneg X q
  next => intro q hq; exact mul_nonneg (sq_nonneg _) (maximalWeightedDiscrepancy_nonneg X q)
  next =>
    intro q hq
    have hW : 0 <= Finset.sum (branches q) (fun i => abs (c q i)) :=
      Finset.sum_nonneg (fun i _ => abs_nonneg (c q i))
    have hp := mul_le_mul (hpoint q hq) (hpoint q hq) (abs_nonneg _)
      (mul_nonneg hW (maximalWeightedDiscrepancy_nonneg X q))
    nlinarith only [hp]

/-- Any proved pointwise discrepancy majorant yields a corresponding full quadratic coefficient budget. -/
theorem branchWeightedDiscrepancy_sq_le_majorant {X : Real} {Q : Nat}
    (branches : Nat -> Finset Nat) (c : Nat -> Nat -> Real)
    (a : (q : Nat) -> Nat -> Units (ZMod q)) (y : Nat -> Nat -> Nat) (V : Nat -> Real)
    (hy : forall q, Membership.mem (Finset.Icc 1 Q) q ->
      forall i, Membership.mem (branches q) i -> y q i <= Nat.floor X)
    (hV : forall q, Membership.mem (Finset.Icc 1 Q) q -> maximalWeightedDiscrepancy X q <= V q) :
    (branchWeightedDiscrepancy Q branches c a y)^2 <=
      averageWeightedDiscrepancy X Q*
        Finset.sum (Finset.Icc 1 Q) (fun q => (Finset.sum (branches q) (fun i => abs (c q i)))^2*V q) := by
  have henergy : branchCoefficientEnergy X Q branches c <=
      Finset.sum (Finset.Icc 1 Q) (fun q => (Finset.sum (branches q) (fun i => abs (c q i)))^2*V q) := by
    apply Finset.sum_le_sum
    intro q hq
    exact mul_le_mul_of_nonneg_left (hV q hq) (sq_nonneg _)
  have hnonneg : 0 <= averageWeightedDiscrepancy X Q :=
    Finset.sum_nonneg (fun q _ => maximalWeightedDiscrepancy_nonneg X q)
  exact le_trans (branchWeightedDiscrepancy_sq_le_energy branches c a y hy)
    (mul_le_mul_of_nonneg_left henergy hnonneg)

noncomputable local instance unitClassFintype (q : Nat) : Fintype (Units (ZMod q)) :=
  Fintype.ofFinite _

/-- The exact mean of the globally centered errors over all finite unit classes. -/
noncomputable def unitMeanProgressionError (y q : Nat) : Real :=
  (Finset.sum Finset.univ (fun a : Units (ZMod q) =>
    psiProgression y q (a : ZMod q)-psiGlobal y/(q.totient : Real))) /
      (Fintype.card (Units (ZMod q)) : Real)

/-- Remove only the unit-class mean; its signed branch sum remains a separate exact correction. -/
noncomputable def unitCenteredProgressionError (y q : Nat) (a : Units (ZMod q)) : Real :=
  psiProgression y q (a : ZMod q)-psiGlobal y/(q.totient : Real)-unitMeanProgressionError y q

/-- The exact unit-class mean is bounded by the original maximal discrepancy. -/
theorem abs_unitMeanProgressionError_le {X : Real} {y q : Nat}
    (hy : y <= Nat.floor X) : abs (unitMeanProgressionError y q) <= maximalWeightedDiscrepancy X q := by
  have hcard : (0:Real) < (Fintype.card (Units (ZMod q)) : Real) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsum : abs (Finset.sum Finset.univ (fun a : Units (ZMod q) =>
      psiProgression y q (a : ZMod q)-psiGlobal y/(q.totient : Real))) <=
      (Fintype.card (Units (ZMod q)) : Real)*maximalWeightedDiscrepancy X q := by
    calc
      _ <= Finset.sum Finset.univ (fun a : Units (ZMod q) =>
          abs (psiProgression y q (a : ZMod q)-psiGlobal y/(q.totient : Real))) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum Finset.univ (fun _ : Units (ZMod q) => maximalWeightedDiscrepancy X q) :=
        Finset.sum_le_sum (fun a _ => abs_progressionError_le_maximal a hy)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold unitMeanProgressionError
  rw [abs_div, abs_of_pos hcard]
  have hquot : abs (Finset.sum Finset.univ (fun a : Units (ZMod q) =>
      psiProgression y q (a : ZMod q)-psiGlobal y/(q.totient : Real))) /
      (Fintype.card (Units (ZMod q)) : Real) * (Fintype.card (Units (ZMod q)) : Real) =
      abs (Finset.sum Finset.univ (fun a : Units (ZMod q) =>
        psiProgression y q (a : ZMod q)-psiGlobal y/(q.totient : Real))) := by field_simp
  by_contra hnot
  have hstrict := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) hcard
  nlinarith only [hsum, hquot, hstrict]

/-- Removing the unit-class mean costs at most a factor two in the original bound. -/
theorem abs_unitCenteredProgressionError_le {X : Real} {y q : Nat}
    (a : Units (ZMod q)) (hy : y <= Nat.floor X) :
    abs (unitCenteredProgressionError y q a) <= 2*maximalWeightedDiscrepancy X q := by
  unfold unitCenteredProgressionError
  have htri := abs_sub_le (psiProgression y q (a : ZMod q)-psiGlobal y/(q.totient : Real))
    0 (unitMeanProgressionError y q)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  have h := abs_progressionError_le_maximal a hy
  have hm := abs_unitMeanProgressionError_le hy (q := q)
  linarith

/-- The recentered errors have exactly zero sum over the unit classes. -/
theorem unitCenteredProgressionError_sum_zero (y q : Nat) :
    Finset.sum Finset.univ (fun a : Units (ZMod q) => unitCenteredProgressionError y q a) = 0 := by
  have hcard : Not ((Fintype.card (Units (ZMod q)) : Real) = 0) :=
    (Nat.cast_pos.mpr Fintype.card_pos).ne'
  simp only [unitCenteredProgressionError, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, unitMeanProgressionError]
  field_simp
  ring

/-- Maximal deviation from the actual unit-class average over the full endpoint range. -/
noncomputable def maximalUnitCenteredDiscrepancy (X : Real) (q : Nat) : Real :=
  iSup (fun a : Units (ZMod q) => iSup (fun y : Fin (Nat.floor X+1) =>
    abs (unitCenteredProgressionError y.val q a)))

/-- The recentered maximal discrepancy is at most twice the completed BV discrepancy. -/
theorem maximalUnitCenteredDiscrepancy_le (X : Real) (q : Nat) :
    maximalUnitCenteredDiscrepancy X q <= 2*maximalWeightedDiscrepancy X q := by
  unfold maximalUnitCenteredDiscrepancy
  apply ciSup_le
  intro a
  apply ciSup_le
  intro y
  exact abs_unitCenteredProgressionError_le a (by have := y.isLt; omega)

/-- Recentering uses the actual mean of the unit progressions, not the all-prime-power mean. -/
theorem unitCenteredProgressionError_eq_unitAverage (y q : Nat) (a : Units (ZMod q)) :
    unitCenteredProgressionError y q a = psiProgression y q (a : ZMod q) -
      (Finset.sum Finset.univ (fun b : Units (ZMod q) => psiProgression y q (b : ZMod q))) /
        (Fintype.card (Units (ZMod q)) : Real) := by
  have hcard : Not ((Fintype.card (Units (ZMod q)) : Real) = 0) :=
    (Nat.cast_pos.mpr Fintype.card_pos).ne'
  simp only [unitCenteredProgressionError, unitMeanProgressionError, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- The full signed branch identity retains the removed mean at every original endpoint. -/
theorem sum_progressionError_eq_unitCentered_add_mean (q : Nat) (s : Finset Nat)
    (c : Nat -> Real) (a : Nat -> Units (ZMod q)) (y : Nat -> Nat) :
    Finset.sum s (fun i => c i*(psiProgression (y i) q (a i : ZMod q)-
      psiGlobal (y i)/(q.totient : Real))) =
      Finset.sum s (fun i => c i*unitCenteredProgressionError (y i) q (a i)) +
      Finset.sum s (fun i => c i*unitMeanProgressionError (y i) q) := by
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold unitCenteredProgressionError
  ring

/-- Summing the recentered errors keeps the same modulus range with a factor two. -/
theorem averageUnitCenteredDiscrepancy_le (X : Real) (Q : Nat) :
    Finset.sum (Finset.Icc 1 Q) (maximalUnitCenteredDiscrepancy X) <=
      2*averageWeightedDiscrepancy X Q := by
  unfold averageWeightedDiscrepancy
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun q _ => maximalUnitCenteredDiscrepancy_le X q)

/-- Completed BV transfers to unit-average centering at the same level and logarithmic saving. -/
theorem weighted_bombieri_vinogradov_unit_centered
    (theta A : Real) (hTheta : theta < 1/2) (hA : 1 <= A) :
    exists C : Real, 0 < C /\ forall {X : Real}, 3 <= X ->
      Finset.sum (Finset.Icc 1 (Nat.floor (X^theta))) (maximalUnitCenteredDiscrepancy X) <=
        C*(X/(Real.log X)^A) := by
  choose C hC using weighted_bombieri_vinogradov theta hTheta A hA
  refine Exists.intro (2*C) (And.intro (by linarith [hC.1]) ?_)
  intro X hX
  have h := averageUnitCenteredDiscrepancy_le X (Nat.floor (X^theta))
  have hBV := hC.2 hX
  nlinarith only [h, hBV]

open scoped Classical

/-- Summing the unit progressions covers exactly the indices coprime to the modulus. -/
theorem sum_units_psiProgression_eq_coprime (y q : Nat) :
    Finset.sum Finset.univ (fun a : Units (ZMod q) => psiProgression y q (a : ZMod q)) =
      Finset.sum ((Finset.Icc 1 y).filter (fun n => Nat.Coprime n q)) ArithmeticFunction.vonMangoldt := by
  simp only [psiProgression, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : Nat.Coprime n q
  next =>
    have H := (ZMod.isUnit_iff_coprime n q).mpr hc
    let a := H.unit
    have ha : (a : ZMod q) = (n : ZMod q) := H.unit_spec
    rw [if_pos hc, Finset.sum_eq_single a]
    next => simp only [if_pos ha]
    next =>
      intro b hb hba
      have hnot : Not ((b : ZMod q) = (n : ZMod q)) := by
        intro heq
        exact hba (Units.ext (heq.trans ha.symm))
      exact if_neg hnot
    next => intro hnot; exact False.elim (hnot (Finset.mem_univ a))
  next =>
    rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro a ha
    have hnot : Not ((a : ZMod q) = (n : ZMod q)) := by
      intro heq
      apply hc
      apply (ZMod.isUnit_iff_coprime n q).mp
      rw [<- heq]
      exact a.isUnit
    exact if_neg hnot

/-- The removed mean is exactly the negative noncoprime Mangoldt mass, with no discarded term. -/
theorem unitMeanProgressionError_eq_noncoprime (y q : Nat) [NeZero q] :
    unitMeanProgressionError y q =
      -(Finset.sum ((Finset.Icc 1 y).filter (fun n => Not (Nat.Coprime n q)))
        ArithmeticFunction.vonMangoldt)/(q.totient : Real) := by
  have hcard : Not ((q.totient : Real) = 0) :=
    (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))).ne'
  have hsplit : Finset.sum ((Finset.Icc 1 y).filter (fun n => Nat.Coprime n q)) ArithmeticFunction.vonMangoldt +
      Finset.sum ((Finset.Icc 1 y).filter (fun n => Not (Nat.Coprime n q))) ArithmeticFunction.vonMangoldt =
      psiGlobal y := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  simp only [unitMeanProgressionError, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ZMod.card_units_eq_totient, sum_units_psiProgression_eq_coprime]
  field_simp
  nlinarith only [hsplit]

/-- The unweighted local unit mean is nonpositive; later signed weights still require their own analysis. -/
theorem unitMeanProgressionError_nonpos (y q : Nat) [NeZero q] : unitMeanProgressionError y q <= 0 := by
  rw [unitMeanProgressionError_eq_noncoprime]
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)))
    (Nat.cast_nonneg _)

open Nat.PrimeSieve

/-- The exact removed mean is an ordinary prefix of noncoprime Mangoldt weights. -/
theorem unitMeanProgressionError_eq_squarePrefix (y q : Nat) [NeZero q] :
    unitMeanProgressionError y q =
      -(squarePrefix (fun r => if Nat.Coprime r q then 0 else ArithmeticFunction.vonMangoldt r) y) /
        (q.totient : Real) := by
  rw [unitMeanProgressionError_eq_noncoprime,
    squarePrefix_eq_Icc_of_zero _ _ (by simp)]
  congr 2
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hc : Nat.Coprime r q
  all_goals simp [hc]

/-- The full signed endpoint correction for the actual divisor-three quadratic rows. -/
noncomputable def squareThirdUnitMeanCorrection (n q : Nat) : Real :=
  Finset.sum (squareThirdEndpointSupport n) (fun x =>
    (squareThirdEndpointCoefficient n x : Real)*unitMeanProgressionError x.2 q)

/-- Complete endpoint merging yields the negative actual noncoprime fringe mass. -/
theorem squareThirdUnitMeanCorrection_eq {n q : Nat} (hn : 100 <= n) [NeZero q] :
    squareThirdUnitMeanCorrection n q = -squareThirdNoncoprimeMass n q/(q.totient : Real) := by
  unfold squareThirdUnitMeanCorrection
  simp_rw [unitMeanProgressionError_eq_squarePrefix]
  simp only [mul_div, mul_neg]
  rw [<- Finset.sum_div, Finset.sum_neg_distrib]
  rw [sum_squareThirdEndpointPrefix_eq_supported_fringe hn]
  rfl

/-- The complete row correction is nonpositive before any outer signed coefficient. -/
theorem squareThirdUnitMeanCorrection_nonpos {n q : Nat} (hn : 100 <= n) [NeZero q] :
    squareThirdUnitMeanCorrection n q <= 0 := by
  rw [squareThirdUnitMeanCorrection_eq hn]
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (squareThirdNoncoprimeMass_nonneg n q)) (Nat.cast_nonneg _)

/-- The actual BV unit-mean correction obeys the supported prime-power capacity bound. -/
theorem abs_squareThirdUnitMeanCorrection_le {n q : Nat} (hn : 100 <= n) [NeZero q] :
    abs (squareThirdUnitMeanCorrection n q) <=
      (Finset.sum q.primeFactors (fun p =>
        Finset.sum (squareThirdPrimePowerIndices n p) (fun k =>
          (2*(n/(3*p^k)+1) : Nat)*Real.log p))) / (q.totient : Real) := by
  rw [squareThirdUnitMeanCorrection_eq hn, abs_div, abs_neg,
    abs_of_nonneg (squareThirdNoncoprimeMass_nonneg n q),
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right
    (squareThirdNoncoprimeMass_le_supported_primePowers hn (NeZero.ne q)) (Nat.cast_nonneg _)

/-- Explicit logarithmic bound for the complete BV unit-mean endpoint correction. -/
theorem abs_squareThirdUnitMeanCorrection_le_log {n q : Nat} (hn : 100 <= n) [NeZero q] :
    abs (squareThirdUnitMeanCorrection n q) <=
      ((q.primeFactors.card : Real)*
        (2*(n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1) : Nat)*Real.log n)/(q.totient : Real) := by
  rw [squareThirdUnitMeanCorrection_eq hn, abs_div, abs_neg,
    abs_of_nonneg (squareThirdNoncoprimeMass_nonneg n q),
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (squareThirdNoncoprimeMass_le_log hn (NeZero.ne q)) (Nat.cast_nonneg _)

/-- At the actual modulus six, only two prime bases and totient two remain. -/
theorem abs_squareThirdUnitMeanCorrection_six_le_log {n : Nat} (hn : 100 <= n) :
    abs (squareThirdUnitMeanCorrection n 6) <=
      (2*(n/(3*(Nat.nthRoot 3 (n*n+2*n)-4))+1) : Nat)*Real.log n := by
  have hf : (6:Nat).primeFactors = ({2,3} : Finset Nat) := by
    apply Finset.ext
    intro p
    constructor
    next =>
      intro hp
      have hd := Nat.mem_primeFactors.mp hp
      have hsplit := hd.1.dvd_mul.mp (show Dvd.dvd p (2*3) from hd.2.1)
      have hp2 := hd.1.two_le
      have heq : p = 2 \/ p = 3 := by
        rcases hsplit with htwo | hthree
        next => have h := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp htwo; omega
        next => have h := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hthree; omega
      simpa using heq
    next =>
      intro hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with htwo | hthree
      next => subst p; exact Nat.mem_primeFactors.mpr (And.intro (by decide) (And.intro (by decide) (by decide)))
      next => subst p; exact Nat.mem_primeFactors.mpr (And.intro (by decide) (And.intro (by decide) (by decide)))
  have ht : (6:Nat).totient = 2 := by decide
  have h := abs_squareThirdUnitMeanCorrection_le_log (q := 6) hn
  norm_num [hf, ht] at h
  push_cast
  nlinarith only [h]

end RobinBV.Sieve
