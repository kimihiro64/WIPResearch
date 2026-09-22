/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.Order.Group.Int.Sum
import RobinBV.Sieve.Proof.LinnikVMVTDecay

/-!
# Mass of the good derivative-denominator indices

Theorem 24.12 assumes at least `delta * k` good derivative indices.  Since
these are distinct integers at least two, their weighted index sum is not just
linear in their number: its sharp minimum is `h * (h + 3) / 2`.  Consequently
the good-denominator packet contributes at least `delta^3 * k^2 / 2`, exactly
the negative exponent mass consumed by `exists_linnikVMVT_signed_decay_bound`.
-/

theorem linnik_affine_range_sum (h : Nat) :
    Finset.sum (Finset.range h) (fun n => ((2 + n : Nat) : Real)) =
      (h : Real) * ((h : Real) + 3) / 2 := by
  induction h with
  | zero => norm_num
  | succ h ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem linnik_good_index_sum_lower
    (s : Finset Int) (hs : forall j : Int, Membership.mem s j -> 2 <= j) :
    (s.card : Real) * ((s.card : Real) + 3) / 2 <=
      Finset.sum s (fun j => (j : Real)) := by
  have hint := Finset.sum_range_le_sum hs
  have hcast :
      (((Finset.sum (Finset.range s.card)
          (fun n => ((2 : Int) + n))) : Int) : Real) <=
        (((Finset.sum s (fun j => j)) : Int) : Real) := by
    exact_mod_cast hint
  have hleft :
      (((Finset.sum (Finset.range s.card)
          (fun n => ((2 : Int) + n))) : Int) : Real) =
        (s.card : Real) * ((s.card : Real) + 3) / 2 := by
    calc
      (((Finset.sum (Finset.range s.card)
          (fun n => ((2 : Int) + n))) : Int) : Real) =
          Finset.sum (Finset.range s.card)
            (fun n => (((2 : Int) + n : Int) : Real)) := by
              rw [Int.cast_sum]
      _ = Finset.sum (Finset.range s.card)
          (fun n => ((2 + n : Nat) : Real)) := by
            apply Finset.sum_congr rfl
            intro n hn
            norm_num
      _ = (s.card : Real) * ((s.card : Real) + 3) / 2 :=
        linnik_affine_range_sum s.card
  have hright :
      (((Finset.sum s (fun j => j)) : Int) : Real) =
        Finset.sum s (fun j => (j : Real)) := by
    rw [Int.cast_sum]
  rw [hleft, hright] at hcast
  exact hcast

theorem linnik_good_index_mass_lower
    (delta : Real) (k : Nat) (s : Finset Int)
    (hdelta : 0 < delta)
    (hs : forall j : Int, Membership.mem s j -> 2 <= j)
    (hcard : delta * (k : Real) <= (s.card : Real)) :
    delta ^ 3 * (k : Real) ^ 2 / 2 <=
      delta * Finset.sum s (fun j => (j : Real)) := by
  have hsum := linnik_good_index_sum_lower s hs
  have hdeltaKNonneg : 0 <= delta * (k : Real) := by positivity
  have hcardNonneg : 0 <= (s.card : Real) := by positivity
  have hsq : delta ^ 2 * (k : Real) ^ 2 <= (s.card : Real) ^ 2 := by
    have hmul := mul_le_mul hcard hcard hdeltaKNonneg hcardNonneg
    calc
      delta ^ 2 * (k : Real) ^ 2 =
          (delta * (k : Real)) * (delta * (k : Real)) := by ring
      _ <= (s.card : Real) * (s.card : Real) := hmul
      _ = (s.card : Real) ^ 2 := by ring
  have hcardSquare : (s.card : Real) ^ 2 <=
      (s.card : Real) * ((s.card : Real) + 3) := by
    rw [pow_two]
    apply mul_le_mul_of_nonneg_left _ hcardNonneg
    linarith
  calc
    delta ^ 3 * (k : Real) ^ 2 / 2 =
        delta * (delta ^ 2 * (k : Real) ^ 2) / 2 := by ring
    _ <= delta * ((s.card : Real) ^ 2) / 2 := by gcongr
    _ <= delta *
        ((s.card : Real) * ((s.card : Real) + 3)) / 2 := by gcongr
    _ = delta *
        ((s.card : Real) * ((s.card : Real) + 3) / 2) := by ring
    _ <= delta * Finset.sum s (fun j => (j : Real)) := by
      gcongr

/-- The good-index mass in the exact denominator used by Theorem 24.11.
After division by `8 * (k*r)^2`, the factor `k^2` cancels and leaves the
uniform negative exponent `-delta^3 / (16*r^2)`. -/
theorem linnik_good_index_negative_exponent_le
    (delta : Real) (k r : Nat) (s : Finset Int)
    (hdelta : 0 < delta) (hk : 0 < k) (hr : 0 < r)
    (hs : forall j : Int, Membership.mem s j -> 2 <= j)
    (hcard : delta * (k : Real) <= (s.card : Real)) :
    -(delta * Finset.sum s (fun j => (j : Real))) /
        (8 * (k : Real) ^ 2 * (r : Real) ^ 2) <=
      -(delta ^ 3) / (16 * (r : Real) ^ 2) := by
  have hmass := linnik_good_index_mass_lower delta k s hdelta hs hcard
  have hdenPos : 0 < 8 * (k : Real) ^ 2 * (r : Real) ^ 2 := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hmass
    (one_div_nonneg.mpr hdenPos.le)
  have hneg := neg_le_neg hscaled
  calc
    -(delta * Finset.sum s (fun j => (j : Real))) /
        (8 * (k : Real) ^ 2 * (r : Real) ^ 2) =
        -(1 / (8 * (k : Real) ^ 2 * (r : Real) ^ 2) *
          (delta * Finset.sum s (fun j => (j : Real)))) := by ring
    _ <= -(1 / (8 * (k : Real) ^ 2 * (r : Real) ^ 2) *
        (delta ^ 3 * (k : Real) ^ 2 / 2)) := hneg
    _ = -(delta ^ 3) / (16 * (r : Real) ^ 2) := by
      have hkReal : Not ((k : Real) = 0) := by exact_mod_cast (Nat.ne_of_gt hk)
      have hrReal : Not ((r : Real) = 0) := by exact_mod_cast (Nat.ne_of_gt hr)
      field_simp
      ring
