/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.LinnikResidueKernel

/-!
# Sharp truncated residue blocks for Linnik's technical inequality

This module retains the minimum in the rational residue kernel and applies the
source cutoff `R = floor(q/Y)`.  The two reflected tails each cost at most
`3*q`, so a complete canonical block costs `Y + 6*q`, uniformly in `Y`.
The final theorem transports the same bound through every coprime affine
residue permutation for use by the perturbed-block consumer.
-/

theorem linnik_one_sided_residue_reflection_sum (Y : Real) (q : Nat) :
    Finset.sum (Finset.Ioo 0 q)
        (fun r => linnikOneSidedResidueKernel Y q (q - r)) =
      Finset.sum (Finset.Ioo 0 q)
        (fun r => linnikOneSidedResidueKernel Y q r) := by
  apply Finset.sum_bij'
    (fun r _ => q - r) (fun r _ => q - r)
  next =>
    intro r hr
    simp only [Finset.mem_Ioo] at hr
    simp only [Finset.mem_Ioo]
    omega
  next =>
    intro r hr
    simp only [Finset.mem_Ioo] at hr
    simp only [Finset.mem_Ioo]
    omega
  next =>
    intro r hr
    simp only [Finset.mem_Ioo] at hr
    omega
  next =>
    intro r hr
    simp only [Finset.mem_Ioo] at hr
    omega
  next =>
    intro r hr
    rfl

theorem linnik_rational_nonzero_kernel_sum_le_six_q
    (Y : Real) (q : Nat) (hY : 0 < Y) (hq : 0 < q) :
    Finset.sum (Finset.Ioo 0 q)
        (fun r => linnikReciprocalSquareKernel Y ((r : Real) / q)) <=
      6 * (q : Real) := by
  calc
    Finset.sum (Finset.Ioo 0 q)
        (fun r => linnikReciprocalSquareKernel Y ((r : Real) / q)) <=
        Finset.sum (Finset.Ioo 0 q) (fun r =>
          linnikOneSidedResidueKernel Y q r +
            linnikOneSidedResidueKernel Y q (q - r)) := by
      apply Finset.sum_le_sum
      intro r hr
      simp only [Finset.mem_Ioo] at hr
      exact linnik_rational_kernel_le_truncated_pair Y r q hY hr.1 hr.2
    _ = Finset.sum (Finset.Ioo 0 q)
          (fun r => linnikOneSidedResidueKernel Y q r) +
        Finset.sum (Finset.Ioo 0 q)
          (fun r => linnikOneSidedResidueKernel Y q (q - r)) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * Finset.sum (Finset.Ioo 0 q)
        (fun r => linnikOneSidedResidueKernel Y q r) := by
      rw [linnik_one_sided_residue_reflection_sum]
      ring
    _ <= 2 * (3 * (q : Real)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact linnik_one_sided_residue_sum_le_three_q Y q hY hq
    _ = 6 * (q : Real) := by ring

theorem linnik_rational_residue_kernel_sum_le_sharp
    (Y : Real) (q : Nat) (hY : 0 < Y) (hq : 0 < q) :
    Finset.sum (Finset.range q)
        (fun r => linnikReciprocalSquareKernel Y ((r : Real) / q)) <=
      Y + 6 * (q : Real) := by
  have hrange : Finset.range q = Insert.insert 0 (Finset.Ioo 0 q) := by
    ext r
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  have hzero : linnikReciprocalSquareKernel Y (((0 : Nat) : Real) / q) = Y := by
    simp [linnikReciprocalSquareKernel, linnikNearestIntDist]
  rw [hzero]
  exact _root_.add_le_add le_rfl
    (linnik_rational_nonzero_kernel_sum_le_six_q Y q hY hq)

theorem linnik_affine_rational_residue_kernel_sum_le_sharp
    (Y : Real) (a c q : Nat) (hY : 0 < Y) (hq : 0 < q)
    (hcop : Nat.Coprime a q) :
    Finset.sum (Finset.range q) (fun r =>
        linnikReciprocalSquareKernel Y
          ((((a * r + c) % q : Nat) : Real) / q)) <=
      Y + 6 * (q : Real) := by
  let f : Nat -> Nat := fun r => (a * r + c) % q
  have hinj : forall r, Membership.mem (Finset.range q) r ->
      forall s, Membership.mem (Finset.range q) s -> f r = f s -> r = s := by
    intro r hr s hs hrs
    exact linnik_affine_residue_injective_on a c q hcop r hr s hs hrs
  have hsubset : Finset.image f (Finset.range q) <= Finset.range q := by
    intro z hz
    rw [Finset.mem_image] at hz
    choose r hr hzr using hz
    rw [<- hzr]
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
  have himage : Finset.sum (Finset.image f (Finset.range q)) (fun z =>
      linnikReciprocalSquareKernel Y ((z : Real) / q)) =
      Finset.sum (Finset.range q) (fun r =>
        linnikReciprocalSquareKernel Y ((f r : Real) / q)) := by
    rw [Finset.sum_image]
    exact hinj
  calc
    Finset.sum (Finset.range q) (fun r =>
        linnikReciprocalSquareKernel Y
          ((((a * r + c) % q : Nat) : Real) / q)) =
        Finset.sum (Finset.image f (Finset.range q)) (fun z =>
          linnikReciprocalSquareKernel Y ((z : Real) / q)) := by
      exact himage.symm
    _ <= Finset.sum (Finset.range q) (fun z =>
        linnikReciprocalSquareKernel Y ((z : Real) / q)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro z hz hznot
      exact linnikReciprocalSquareKernel_nonneg Y ((z : Real) / q) hY.le
    _ <= Y + 6 * (q : Real) :=
      linnik_rational_residue_kernel_sum_le_sharp Y q hY hq
