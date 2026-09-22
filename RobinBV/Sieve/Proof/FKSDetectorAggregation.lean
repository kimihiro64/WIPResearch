/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Mathlib.Analysis.Complex.FiniteMultiplicityCopies
import RobinBV.Sieve.Assembly.ZetaZeroDetection

/-!
# Finite aggregation of the proved Type-I/Type-II zero detector

This module connects the actual-zero detector to a finite zero-count estimate.
The two detector second moments remain explicit hypotheses; no density theorem
is imported or hidden.
-/

set_option autoImplicit false

open scoped BigOperators

namespace RobinBV.Sieve

/-- The single absolute constant supplied by the proved zero detector.
Its existence is unconditional; no effective numerical value is asserted. -/
noncomputable def fksDetectorConstant : Real :=
  nontrivial_zero_dirichlet_typeI_or_typeII.choose

/-- A finite admissible detector threshold, chosen after `b` and before the
height or zero family. It does not quantify over arbitrary detector constants. -/
noncomputable def fksDetectorHeight (b : Real) : Real :=
  max 1 (max (fksDetectorConstant ^ (1 / ((1 / 4 : Real) - 2*b)))
    ((4 : Real) ^ (1/b)))

theorem fks_finite_two_detector_count_from_moments
    {alpha : Type*} (S : Finset alpha)
    (f g : alpha -> Complex) (L MF MG : Real)
    (hL : 0 < L)
    (hcover : forall z, Membership.mem S z ->
      L <= norm (f z) \/ L <= norm (g z))
    (hF : S.sum (fun z => norm (f z)^2) <= MF)
    (hG : S.sum (fun z => norm (g z)^2) <= MG) :
    (S.card : Real) <= (MF + MG) / L^2 := by
  have hpoint : forall z, Membership.mem S z ->
      L^2 <= norm (f z)^2 + norm (g z)^2 := by
    intro z hz
    rcases hcover z hz with hf | hg
    next =>
      have hsq : L^2 <= norm (f z)^2 := by
        nlinarith [sq_nonneg (L - norm (f z))]
      nlinarith [sq_nonneg (norm (g z))]
    next =>
      have hsq : L^2 <= norm (g z)^2 := by
        nlinarith [sq_nonneg (L - norm (g z))]
      nlinarith [sq_nonneg (norm (f z))]
  have hsum : S.sum (fun _ => L^2) <=
      S.sum (fun z => norm (f z)^2 + norm (g z)^2) := by
    exact Finset.sum_le_sum (fun z hz => hpoint z hz)
  have hleft : (S.card : Real) * L^2 <= MF + MG := by
    calc
      (S.card : Real) * L^2 = S.sum (fun _ => L^2) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ <= S.sum (fun z => norm (f z)^2 + norm (g z)^2) := hsum
      _ = S.sum (fun z => norm (f z)^2) +
          S.sum (fun z => norm (g z)^2) := by
        rw [Finset.sum_add_distrib]
      _ <= MF + MG := add_le_add hF hG
  have hLsq : 0 < L^2 := sq_pos_of_pos hL
  apply le_of_mul_le_mul_right _ hLsq
  have hcancel : (MF + MG) / L^2 * L^2 = MF + MG := by
    field_simp [ne_of_gt hLsq]
  rw [hcancel]
  exact hleft

theorem fks_detector_count_from_moment_bounds
    (S : Finset Complex) (a b T MF MG : Real)
    (hba : 0 < b) (hbb : b < a) (ha : a < 1)
    (hb : b < (1 / 8 : Real))
    (hT : fksDetectorHeight b <= T)
    (hzero : forall s, Membership.mem S s -> Zeta23.IsNontrivialZero s)
    (hhalf : forall s, Membership.mem S s -> (1 / 2 : Real) <= s.re)
    (hheight : forall s, Membership.mem S s ->
      T <= abs s.im /\ abs s.im <= 2*T)
    (hF : S.sum (fun s =>
      norm ((Finset.range (Nat.floor T - Nat.floor (T^a))).sum
        (fun j => ((Nat.floor (T^a) + j + 1 : Nat) : Complex) ^ (-s)))^2) <= MF)
    (hG : S.sum (fun s =>
      norm ((Finset.range
        (Nat.floor (T^b) * Nat.floor (T^a) - Nat.floor (T^b))).sum
        (fun j => LSeries.truncatedMoebius (Nat.floor (T^b))
          (Nat.floor (T^a)) (Nat.floor (T^b) + j + 1) *
            ((Nat.floor (T^b) + j + 1 : Nat) : Complex) ^ (-s)))^2) <= MG) :
    (S.card : Real) <=
      (MF + MG) / (T^(-2*b))^2 := by
  obtain hdet := nontrivial_zero_dirichlet_typeI_or_typeII
  let Cdet : Real := hdet.choose
  have hdetMain := hdet.choose_spec.2
  have hTC : max 1 (max (Cdet ^ (1 / ((1 / 4 : Real) - 2*b)))
      ((4 : Real) ^ (1/b))) <= T := hT
  have hT1 : 1 <= T := le_trans (le_max_left _ _) hTC
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hcover : forall s, Membership.mem S s ->
      T^(-2*b) <= norm ((Finset.range
        (Nat.floor T - Nat.floor (T^a))).sum
        (fun j => ((Nat.floor (T^a) + j + 1 : Nat) : Complex) ^ (-s))) \/
      T^(-2*b) <= norm ((Finset.range
        (Nat.floor (T^b) * Nat.floor (T^a) - Nat.floor (T^b))).sum
        (fun j => LSeries.truncatedMoebius (Nat.floor (T^b))
          (Nat.floor (T^a)) (Nat.floor (T^b) + j + 1) *
            ((Nat.floor (T^b) + j + 1 : Nat) : Complex) ^ (-s))) := by
    intro s hs
    have hband := hheight s hs
    have h := hdetMain a b T s hba hbb ha hb hTC
      (hzero s hs) (hhalf s hs) hband.1 hband.2
    rcases h with hf | hg
    next => exact Or.inl hf
    next =>
      have h4T : (4 : Real) ^ (1/b) <= T := by
        exact (le_max_right (Cdet ^ (1 / ((1 / 4 : Real) - 2*b)))
          ((4 : Real) ^ (1/b))).trans
          ((le_max_right 1 (max (Cdet ^ (1 / ((1 / 4 : Real) - 2*b)))
            ((4 : Real) ^ (1/b)))).trans hTC)
      have hpowcomp := Real.rpow_le_rpow_of_nonpos
        (by positivity : 0 < (4 : Real) ^ (1/b)) h4T
        (by linarith : (-2*b : Real) <= 0)
      have hhalf : T^(-2*b) <= (1/2 : Real) := by
        calc
          T^(-2*b) <= ((4 : Real) ^ (1/b))^(-2*b) := hpowcomp
          _ = (1/16 : Real) := by
            rw [<- Real.rpow_mul (by norm_num : 0 <= (4 : Real))]
            field_simp
            norm_num
          _ <= (1/2 : Real) := by norm_num
      exact Or.inr (hhalf.trans hg)
  have hL : 0 < T^(-2*b) := by positivity
  exact fks_finite_two_detector_count_from_moments S
    (fun s => (Finset.range (Nat.floor T - Nat.floor (T^a))).sum
      (fun j => ((Nat.floor (T^a) + j + 1 : Nat) : Complex) ^ (-s)))
    (fun s => (Finset.range
      (Nat.floor (T^b) * Nat.floor (T^a) - Nat.floor (T^b))).sum
      (fun j => LSeries.truncatedMoebius (Nat.floor (T^b))
        (Nat.floor (T^a)) (Nat.floor (T^b) + j + 1) *
          ((Nat.floor (T^b) + j + 1 : Nat) : Complex) ^ (-s)))
    (T^(-2*b)) MF MG hL hcover hF hG

/-!
# Mapped finite detector

The detector is also available on an arbitrary finite index type mapping into
complex zeros.  This preserves repeated natural-multiplicity copies instead
of collapsing them through a complex-valued Finset.
-/

theorem fks_mapped_detector_count_from_moment_bounds
    {alpha : Type*} (S : Finset alpha) (rho : alpha -> Complex)
    (a b T MF MG : Real)
    (hba : 0 < b) (hbb : b < a) (ha : a < 1)
    (hb : b < (1 / 8 : Real))
    (hT : fksDetectorHeight b <= T)
    (hzero : forall s, Membership.mem S s ->
      Zeta23.IsNontrivialZero (rho s))
    (hhalf : forall s, Membership.mem S s ->
      (1 / 2 : Real) <= (rho s).re)
    (hheight : forall s, Membership.mem S s ->
      T <= abs (rho s).im /\ abs (rho s).im <= 2*T)
    (hF : S.sum (fun s =>
      norm ((Finset.range (Nat.floor T - Nat.floor (T^a))).sum
        (fun j => ((Nat.floor (T^a) + j + 1 : Nat) : Complex) ^ (-(rho s))))^2) <= MF)
    (hG : S.sum (fun s =>
      norm ((Finset.range
        (Nat.floor (T^b) * Nat.floor (T^a) - Nat.floor (T^b))).sum
        (fun j => LSeries.truncatedMoebius (Nat.floor (T^b))
          (Nat.floor (T^a)) (Nat.floor (T^b) + j + 1) *
            ((Nat.floor (T^b) + j + 1 : Nat) : Complex) ^ (-(rho s))))^2) <= MG) :
    (S.card : Real) <= (MF + MG) / (T^(-2*b))^2 := by
  obtain hdet := nontrivial_zero_dirichlet_typeI_or_typeII
  let Cdet : Real := hdet.choose
  have hdetMain := hdet.choose_spec.2
  have hTC : max 1 (max (Cdet ^ (1 / ((1 / 4 : Real) - 2*b)))
      ((4 : Real) ^ (1/b))) <= T := hT
  have hT1 : 1 <= T := le_trans (le_max_left _ _) hTC
  have hcover : forall s, Membership.mem S s ->
      T^(-2*b) <= norm ((Finset.range
        (Nat.floor T - Nat.floor (T^a))).sum
        (fun j => ((Nat.floor (T^a) + j + 1 : Nat) : Complex) ^ (-(rho s)))) \/
      T^(-2*b) <= norm ((Finset.range
        (Nat.floor (T^b) * Nat.floor (T^a) - Nat.floor (T^b))).sum
        (fun j => LSeries.truncatedMoebius (Nat.floor (T^b))
          (Nat.floor (T^a)) (Nat.floor (T^b) + j + 1) *
            ((Nat.floor (T^b) + j + 1 : Nat) : Complex) ^ (-(rho s)))) := by
    intro s hs
    have hband := hheight s hs
    have h := hdetMain a b T (rho s) hba hbb ha hb hTC
      (hzero s hs) (hhalf s hs) hband.1 hband.2
    rcases h with hf | hg
    next => exact Or.inl hf
    next =>
      have h4T : (4 : Real) ^ (1/b) <= T := by
        exact (le_max_right (Cdet ^ (1 / ((1 / 4 : Real) - 2*b)))
          ((4 : Real) ^ (1/b))).trans
          ((le_max_right 1 (max (Cdet ^ (1 / ((1 / 4 : Real) - 2*b)))
            ((4 : Real) ^ (1/b)))).trans hTC)
      have hpowcomp := Real.rpow_le_rpow_of_nonpos
        (by positivity : 0 < (4 : Real) ^ (1/b)) h4T
        (by linarith : (-2*b : Real) <= 0)
      have hhalf : T^(-2*b) <= (1/2 : Real) := by
        calc
          T^(-2*b) <= ((4 : Real) ^ (1/b))^(-2*b) := hpowcomp
          _ = (1/16 : Real) := by
            rw [<- Real.rpow_mul (by norm_num : 0 <= (4 : Real))]
            field_simp
            norm_num
          _ <= (1/2 : Real) := by norm_num
      exact Or.inr (hhalf.trans hg)
  have hL : 0 < T^(-2*b) := by positivity
  have hcount : (S.card : Real) <= (MF + MG) / (T^(-2*b))^2 := by
    apply fks_finite_two_detector_count_from_moments S
      (fun s : alpha => (Finset.range (Nat.floor T - Nat.floor (T^a))).sum
        (fun j => ((Nat.floor (T^a) + j + 1 : Nat) : Complex) ^ (-(rho s))))
      (fun s : alpha => (Finset.range
        (Nat.floor (T^b) * Nat.floor (T^a) - Nat.floor (T^b))).sum
        (fun j => LSeries.truncatedMoebius (Nat.floor (T^b))
          (Nat.floor (T^a)) (Nat.floor (T^b) + j + 1) *
            ((Nat.floor (T^b) + j + 1 : Nat) : Complex) ^ (-(rho s))))
      (T^(-2*b)) MF MG
    next => exact hL
    next => exact hcover
    next => exact hF
    next => exact hG
  exact hcount

/-!
# Natural-multiplicity detector consumer

Specializing the mapped detector to exact natural-multiplicity copies turns
its finite cardinality into the order-weighted zero mass used by N'.
-/

theorem fks_nat_multiplicity_detector_count_from_moment_bounds
    (A : Finset Complex) (m : Complex -> Nat)
    (a b T MF MG : Real)
    (hba : 0 < b) (hbb : b < a) (ha : a < 1)
    (hb : b < (1 / 8 : Real))
    (hT : fksDetectorHeight b <= T)
    (hzero : forall s, Membership.mem (Finset.natMultiplicityCopies A m) s ->
      Zeta23.IsNontrivialZero s.1)
    (hhalf : forall s, Membership.mem (Finset.natMultiplicityCopies A m) s ->
      (1 / 2 : Real) <= (s.1).re)
    (hheight : forall s, Membership.mem (Finset.natMultiplicityCopies A m) s ->
      T <= abs (s.1).im /\ abs (s.1).im <= 2*T)
    (hF : (Finset.natMultiplicityCopies A m).sum (fun s =>
      norm ((Finset.range (Nat.floor T - Nat.floor (T^a))).sum
        (fun j => ((Nat.floor (T^a) + j + 1 : Nat) : Complex) ^ (-s.1)))^2) <= MF)
    (hG : (Finset.natMultiplicityCopies A m).sum (fun s =>
      norm ((Finset.range
        (Nat.floor (T^b) * Nat.floor (T^a) - Nat.floor (T^b))).sum
        (fun j => LSeries.truncatedMoebius (Nat.floor (T^b))
          (Nat.floor (T^a)) (Nat.floor (T^b) + j + 1) *
            ((Nat.floor (T^b) + j + 1 : Nat) : Complex) ^ (-s.1)))^2) <= MG) :
    A.sum (fun z => (m z : Real)) <= (MF + MG) / (T^(-2*b))^2 := by
  let S := Finset.natMultiplicityCopies A m
  have hcount := fks_mapped_detector_count_from_moment_bounds
    S (fun s => s.1) a b T MF MG hba hbb ha hb hT hzero hhalf hheight hF hG
  have hcard : (S.card : Real) = A.sum (fun z => (m z : Real)) := by
    rw [Finset.card_natMultiplicityCopies]
    norm_num [Nat.cast_sum]
  rw [hcard] at hcount
  exact hcount

end RobinBV.Sieve
