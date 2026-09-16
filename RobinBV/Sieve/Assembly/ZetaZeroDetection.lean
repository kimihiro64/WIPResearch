/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.DirichletSegment
import RobinBV.Mathlib.NumberTheory.LSeries.UnitCoefficients
import RobinBV.Sieve.Proof.ZetaEulerMaclaurin

/-!
# A floor-height detector for actual zeta zeros

The complete Euler--Maclaurin estimate at delta=1/8 is combined with the
exact logarithmic Dirichlet-tail bound. The resulting sum runs through
floor(T), not through an unspecified or slightly longer cutoff. Its
fixed constant is existential and not numerically evaluated. Exact finite
Mobius cancellation then gives a Type-I/Type-II large-polynomial alternative
for every admissible pair of power cutoffs, with its threshold proved.

This is an actual-zero source estimate, not a zero-energy, zero-density,
almost-all prime-count, or all-interval prime theorem.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

/-- The actual-zero Dirichlet sum through floor(T) is uniformly power-small. -/
theorem nontrivial_zero_dirichlet_sum_floor_small :
    Exists fun C : Real => 1 <= C /\
      forall (T : Real) (s : Complex), 1 <= T -> Zeta23.IsNontrivialZero s ->
      (1/2 : Real) <= s.re -> T <= abs s.im -> abs s.im <= 2*T ->
      norm ((Finset.range (Nat.floor T)).sum
        (fun n => ((n+1 : Nat) : Complex)^(-s))) <= C*T^(-(1/4 : Real)) := by
  have h := nontrivial_zero_dirichlet_sum_small (delta := (1/8 : Real))
    (by norm_num) (by norm_num)
  cases h with
  | intro C hC =>
    refine Exists.intro (C+9*Real.pi)
      (And.intro (by linarith [hC.1, Real.pi_pos]) ?_)
    intro T s hT hs hsig ht0 ht1
    have h0 := hC.2 T s hT hs hsig ht0 ht1
    rw [show (1 : Real)+1/8 = 9/8 by norm_num] at h0
    calc
      _ <= norm ((Finset.range (Nat.ceil (T^(9/8 : Real)))).sum
          (fun n => ((n+1 : Nat) : Complex)^(-s))) + 9*Real.pi*T^(-(3/8 : Real)) :=
        Complex.norm_sum_cpow_floor_le_ceiling hT hsig ht0 ht1
      _ <= C*T^(-(1/4 : Real))+9*Real.pi*T^(-(1/4 : Real)) :=
        add_le_add h0 (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hT (by norm_num)) (by positivity))
      _ = _ := by ring

/-- Every actual zero in the height band has one of the two detected large sums.
The single absolute constant is the proved floor-detector constant; it has
not been numerically evaluated. Both finite residual cutoffs are retained. -/
theorem nontrivial_zero_dirichlet_typeI_or_typeII :
    Exists fun C : Real => 1 <= C /\
      forall (a b T : Real) (s : Complex),
      0 < b -> b < a -> a < 1 -> b < (1/8 : Real) ->
      max 1 (max (C^(1/((1/4 : Real)-2*b))) ((4 : Real)^(1/b))) <= T ->
      Zeta23.IsNontrivialZero s -> (1/2 : Real) <= s.re ->
      T <= abs s.im -> abs s.im <= 2*T ->
      T^(-2*b) <= norm ((Finset.range (Nat.floor T-Nat.floor (T^a))).sum
        (fun j => ((Nat.floor (T^a)+j+1 : Nat) : Complex)^(-s))) \/
      (1 : Real)/2 <= norm
        ((Finset.range (Nat.floor (T^b)*Nat.floor (T^a)-Nat.floor (T^b))).sum
          (fun j => LSeries.truncatedMoebius (Nat.floor (T^b)) (Nat.floor (T^a))
            (Nat.floor (T^b)+j+1)*((Nat.floor (T^b)+j+1 : Nat) : Complex)^(-s))) := by
  cases nontrivial_zero_dirichlet_sum_floor_small with
  | intro C hC =>
    refine Exists.intro C (And.intro hC.1 ?_)
    intro a b T s hb hba ha hbSmall hT hs hsig ht0 ht1
    have hT1 : 1 <= T := (le_max_left _ _).trans hT
    exact LSeries.dirichlet_sum_height_or_moebius_residual_large
      hC.1 hb hba ha hbSmall hT (by linarith)
      (hC.2 T s hT1 hs hsig ht0 ht1)

/-- Actual zeros have unit-coefficient detection with an independent loss exponent.
The original source constant remains absolute and existential. Every other
constant and the additional normalization threshold are explicit. -/
theorem nontrivial_zero_unit_coefficient_detection :
    Exists fun C : Real => 1 <= C /\
      forall (a b eta T : Real) (s : Complex),
      0 < b -> b < a -> 0 < eta -> a < 1 -> b < (1/8 : Real) ->
      max (max 1 (max (C^(1/((1/4 : Real)-2*b))) ((4 : Real)^(1/b))))
        ((2*LSeries.moebiusSubpowerConstant (eta/(a+b)))^(1/eta)) <= T ->
      Zeta23.IsNontrivialZero s -> (1/2 : Real) <= s.re ->
      T <= abs s.im -> abs s.im <= 2*T ->
      (forall n : Nat, 0 < n -> n <= Nat.floor (T^b)*Nat.floor (T^a) ->
        norm (LSeries.normalizedTruncatedMoebius (Nat.floor (T^b)) (Nat.floor (T^a))
          (LSeries.moebiusHeightScale a b eta T) n) <= 1) /\
      (T^(-2*b) <= norm ((Finset.range (Nat.floor T-Nat.floor (T^a))).sum
        (fun j => ((Nat.floor (T^a)+j+1 : Nat) : Complex)^(-s))) \/
      T^(-2*eta) <= norm
        ((Finset.range (Nat.floor (T^b)*Nat.floor (T^a)-Nat.floor (T^b))).sum
          (fun j => LSeries.normalizedTruncatedMoebius (Nat.floor (T^b)) (Nat.floor (T^a))
            (LSeries.moebiusHeightScale a b eta T) (Nat.floor (T^b)+j+1)*
            ((Nat.floor (T^b)+j+1 : Nat) : Complex)^(-s)))) := by
  cases nontrivial_zero_dirichlet_sum_floor_small with
  | intro C hC =>
    refine Exists.intro C (And.intro hC.1 ?_)
    intro a b eta T s hb hba heta ha hbSmall hT hs hsig ht0 ht1
    have hOld : max 1 (max (C^(1/((1/4 : Real)-2*b))) ((4 : Real)^(1/b))) <= T :=
      (le_max_left _ _).trans hT
    have hT1 : 1 <= T := (le_max_left _ _).trans hOld
    exact LSeries.dirichlet_sum_height_or_unit_moebius_large
      hC.1 hb hba heta ha hbSmall hT (by linarith) (hC.2 T s hT1 hs hsig ht0 ht1)

end RobinBV.Sieve
