/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import Mathlib.NumberTheory.MulChar.Basic

/-!
# Periodicity and cancellation limits of finite character packets

The order of the unit group is a common power period. In particular, a
nonzero residue packet recurs cofinally, while vanishing of all character
fibers over a full higher-power cycle forces every character functional to vanish.
-/

set_option autoImplicit false

namespace MulChar

open scoped Classical

noncomputable section

variable {M S I : Type*} [CommMonoid M] [CommSemiring S] [Fintype (Units M)]

/-- The unit-group cardinality is an exact period for every finite packet
of actual character powers, at every residue including nonunits. -/
theorem powerPacket_periodic
    (s : Finset I) (chi : I -> MulChar M S) (c : I -> S)
    (j : Nat) (a : M) :
    s.sum (fun i => c i * ((chi i)^(j+Fintype.card (Units M))) a) =
      s.sum (fun i => c i * ((chi i)^j) a) := by
  simp only [pow_add, MulChar.pow_card_eq_one, mul_one]

/-- Every original residue packet recurs simultaneously at all residues
at arbitrarily large higher exponents. -/
theorem powerPacket_cofinal_recurrence
    (s : Finset I) (chi : I -> MulChar M S) (c : I -> S) (J : Nat) :
    exists j : Nat, And (J <= j) (And (2 <= j)
      (forall a : M, s.sum (fun i => c i * ((chi i)^j) a) =
        s.sum (fun i => c i * chi i a))) := by
  let E := Fintype.card (Units M)
  have hE : 1 <= E := Fintype.card_pos
  have hBound : J+2 <= E*(J+2) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (J+2) hE
  refine Exists.intro (E*(J+2)+1) (And.intro (by omega) (And.intro (by omega) ?_))
  intro a
  simp only [E, pow_add, pow_mul, MulChar.pow_card_eq_one, one_pow, pow_one, one_mul]

/-- A nonzero residue weight cannot vanish at all sufficiently high powers. -/
theorem powerPacket_cofinal_nonzero
    (s : Finset I) (chi : I -> MulChar M S) (c : I -> S)
    (a : M) (hNonzero : Not (s.sum (fun i => c i * chi i a) = 0)) (J : Nat) :
    exists j : Nat, And (J <= j) (And (2 <= j)
      (Not (s.sum (fun i => c i * ((chi i)^j) a) = 0))) := by
  choose j hj using powerPacket_cofinal_recurrence s chi c J
  refine Exists.intro j (And.intro hj.1 (And.intro hj.2.1 ?_))
  rw [hj.2.2 a]
  exact hNonzero

/-- Zero coefficient on every powered-character fiber through one full
higher-power cycle forces the original fibers themselves to vanish. -/
theorem powerPacket_first_fibers_zero_of_full_cycle
    (s : Finset I) (chi : I -> MulChar M S) (c : I -> S)
    (hCycle : forall j : Nat, 2 <= j -> j <= Fintype.card (Units M)+1 ->
      forall psi : MulChar M S, (s.filter (fun i => (chi i)^j=psi)).sum c=0)
    (psi : MulChar M S) :
    (s.filter (fun i => chi i=psi)).sum c=0 := by
  have hE : 1 <= Fintype.card (Units M) := Fintype.card_pos
  have h := hCycle (Fintype.card (Units M)+1) (by omega) le_rfl psi
  simpa only [pow_succ, MulChar.pow_card_eq_one, one_mul] using h

/-- Full-cycle fiber cancellation annihilates every function of the original
character, not merely the originally selected higher-power layers. -/
theorem sum_characterFunctional_eq_zero_of_full_power_cycle
    (s : Finset I) (chi : I -> MulChar M S) (c : I -> S)
    (hCycle : forall j : Nat, 2 <= j -> j <= Fintype.card (Units M)+1 ->
      forall psi : MulChar M S, (s.filter (fun i => (chi i)^j=psi)).sum c=0)
    (f : MulChar M S -> S) :
    s.sum (fun i => c i * f (chi i))=0 := by
  rw [<- Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image chi) (g := chi)
    (fun i hi => Finset.mem_image_of_mem chi hi) (fun i => c i * f (chi i))]
  apply Finset.sum_eq_zero
  intro psi hPsi
  calc
    (s.filter (fun i => chi i=psi)).sum (fun i => c i * f (chi i)) =
        (s.filter (fun i => chi i=psi)).sum (fun i => c i * f psi) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = ((s.filter (fun i => chi i=psi)).sum c) * f psi :=
      (Finset.sum_mul _ _ _).symm
    _ = 0 := by
      rw [powerPacket_first_fibers_zero_of_full_cycle s chi c hCycle psi, zero_mul]

end

end MulChar
