/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikGoodDenominatorMass

/-!
# Complete VMVT and good-denominator exponent packet

This module joins the normalized source VMVT estimate to the exact mass of the
good derivative-denominator indices.  After all signed exponent contributions
are combined, the packet has a strictly negative power `-lambda / k^2`, where
`lambda` depends only on the density parameter and is positive.
-/

theorem exists_linnikVMVT_good_index_packet_bound :
    exists C : Real, 0 < C /\ forall delta : Real, 0 < delta ->
      exists m : Nat, 0 < m /\ exists lambda : Real, 0 < lambda /\
        forall k Q : Nat, forall s : Finset Int,
          2 <= k -> 0 < Q ->
          (forall j : Int, Membership.mem s j -> 2 <= j) ->
          delta * (k : Real) <= (s.card : Real) ->
          ((Finset.vinogradovMeanValue k (k * (k * m)) (2 * Q) : Real) /
              ((2 * Q : Nat) : Real) ^
                (2 * ((k * m : Nat) : Real) * k -
                  (k : Real) * (k + 1) / 2)) ^
              (1 / (4 * (k : Real) ^ 2 * ((k * m : Nat) : Real) ^ 2)) *
            (((2 * Q : Nat) : Real) ^
              (-(delta * Finset.sum s (fun j => (j : Real))) /
                (8 * (k : Real) ^ 2 * ((k * m : Nat) : Real) ^ 2))) <=
            Real.exp (C * Real.log k / (4 * ((k * m : Nat) : Real))) *
              (((2 * Q : Nat) : Real) ^
                (-lambda / (k : Real) ^ 2)) := by
  choose C hC hsigned using exists_linnikVMVT_signed_decay_bound
  refine Exists.intro C (And.intro hC ?_)
  intro delta hdelta
  choose m hm lambda hlambda hpacket using hsigned delta hdelta
  refine Exists.intro m (And.intro hm
    (Exists.intro lambda (And.intro hlambda ?_)))
  intro k Q s hk hQ hs hcard
  have hkPos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hrPos : 0 < k * m := Nat.mul_pos hkPos hm
  have hnegative := linnik_good_index_negative_exponent_le
    delta k (k * m) s hdelta hkPos hrPos hs hcard
  have hbase : (1 : Real) <= ((2 * Q : Nat) : Real) := by
    exact_mod_cast (show 1 <= 2 * Q by omega)
  have hpow := Real.rpow_le_rpow_of_exponent_le hbase hnegative
  have hratioNonneg : 0 <=
      (Finset.vinogradovMeanValue k (k * (k * m)) (2 * Q) : Real) /
        ((2 * Q : Nat) : Real) ^
          (2 * ((k * m : Nat) : Real) * k -
            (k : Real) * (k + 1) / 2) := by
    apply div_nonneg
    next => positivity
    next => exact Real.rpow_nonneg (by positivity) _
  have hfactorNonneg : 0 <=
      ((Finset.vinogradovMeanValue k (k * (k * m)) (2 * Q) : Real) /
          ((2 * Q : Nat) : Real) ^
            (2 * ((k * m : Nat) : Real) * k -
              (k : Real) * (k + 1) / 2)) ^
        (1 / (4 * (k : Real) ^ 2 * ((k * m : Nat) : Real) ^ 2)) :=
    Real.rpow_nonneg hratioNonneg _
  exact (mul_le_mul_of_nonneg_left hpow hfactorNonneg).trans
    (hpacket k Q hk hQ)
