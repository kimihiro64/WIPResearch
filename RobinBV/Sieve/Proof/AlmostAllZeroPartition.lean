/- Copyright (c) 2026 Jonas Whidden. -/
import RobinBV.Sieve.Assembly.SquareCorridorDeviation
import RobinBV.Sieve.Proof.ZetaWindowSummability

/-!
# Almost-all zero partition primitives

The theorems here split a summable actual-zero series into the low and high
real-part packets and convert a full corridor norm into a low-packet norm.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

theorem summable_predicate_partition
    {alpha : Type*}
    (f : alpha -> Complex) (p : alpha -> Prop) [DecidablePred p]
    (hf : Summable f) :
    And (Summable (fun a => if p a then f a else 0))
      (And (Summable (fun a => if Not (p a) then f a else 0))
        (tsum f = tsum (fun a => if p a then f a else 0) +
          tsum (fun a => if Not (p a) then f a else 0))) := by
  have hleft : Summable (fun a => if p a then f a else 0) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun a => norm_nonneg _) _ hf.norm
    intro a
    split_ifs <;> simp [norm_nonneg]
  have hright : Summable (fun a => if Not (p a) then f a else 0) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun a => norm_nonneg _) _ hf.norm
    intro a
    split_ifs <;> simp [norm_nonneg]
  refine And.intro hleft (And.intro hright ?_)
  have hsum : (fun a => f a) =
      (fun a => (if p a then f a else 0) + (if Not (p a) then f a else 0)) := by
    funext a
    by_cases ha : p a <;> simp [ha]
  calc
    tsum f = tsum (fun a =>
      (if p a then f a else 0) + (if Not (p a) then f a else 0)) := congrArg tsum hsum
    _ = tsum (fun a => if p a then f a else 0) +
        tsum (fun a => if Not (p a) then f a else 0) := hleft.tsum_add hright

theorem low_norm_from_full_and_high
    {delta N : Real} {low high : Complex}
    (hd : 0 <= delta) (hN : 0 <= N)
    (hfull : delta*N <= norm (low + high))
    (hhigh : norm high <= delta*N/2) :
    delta*N/2 <= norm low := by
  have htri : norm (low + high) <= norm low + norm high := norm_add_le _ _
  linarith
