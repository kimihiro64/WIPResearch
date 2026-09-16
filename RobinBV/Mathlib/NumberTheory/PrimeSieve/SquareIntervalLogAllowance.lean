/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalFivePrimePrefix
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalRoughLogBound

/-!
# SquareIntervalLogAllowance

Explicit finite interval estimates used in signed prime-candidate accounting.
All constants and endpoint conditions are retained; no prime-existence result
is claimed by a negative lower envelope.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

noncomputable def roughLogAllowance (n : Nat) : Real :=
  8*(n : Real)/Real.squareSieveDenominator n+2*(n : Real)/(Real.log n)^2

noncomputable def lineCollisionCredit (G : Finset (Prod Nat Nat)) : Real :=
  (2*(Finset.imageFiberPairs G (fun x => x.1*x.2) : Real)+
    (Finset.imageDoubleFibers G (fun x => x.1*x.2) : Real))/3

noncomputable def exactPrefixCompositeAllowance (n : Nat)
    (G : Finset (Prod Nat Nat)) : Real :=
  2*(n : Real)-((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+
    (G.card : Real)-lineCollisionCredit G

theorem lineCollisionCredit_nonneg (G : Finset (Prod Nat Nat)) :
    0 <= lineCollisionCredit G := by unfold lineCollisionCredit; positivity

/-- Bound the actual representation multiplicity excess by the proved
interval sieve. The exact prefix is retained for cancellation downstream. -/
theorem line_family_card_le_prefix_add_log
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {R : Finset Nat}
    (hn : 4 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    ((ownerLineFamilyHighFactorCells Gamma n T fivePrimePrefix R).card : Real) <=
      ((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+roughLogAllowance n := by
  have hg := line_family_card_le_prefix_add_two_rough (Gamma := Gamma) (T := T)
    (by omega : 2 <= n) (fun ell he => fivePrimePrefix_prime he) hcut
  have hgr : ((ownerLineFamilyHighFactorCells Gamma n T fivePrimePrefix R).card : Real) <=
      ((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+
        2*((squareRoughSurvivors n).card : Real) := by exact_mod_cast hg
  have hs := card_squareRoughSurvivors_le_explicit_log hn
  unfold roughLogAllowance
  have hdouble := _root_.mul_le_mul_of_nonneg_left hs (by norm_num : (0 : Real) <= 2)
  have he : 2*(4*(n : Real)/Real.squareSieveDenominator n+(n : Real)/(Real.log n)^2) =
      8*(n : Real)/Real.squareSieveDenominator n+2*(n : Real)/(Real.log n)^2 := by ring
  rw [he] at hdouble
  linarith only [hgr, hdouble]

theorem line_family_card_le_explicit_log
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {R : Finset Nat}
    (hn : 4 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    ((ownerLineFamilyHighFactorCells Gamma n T fivePrimePrefix R).card : Real) <=
      (384/1001 : Real)*n+roughLogAllowance n+31 := by
  have hg := line_family_card_le_prefix_add_log (Gamma := Gamma) (T := T) hn hcut
  have hf := five_prime_prefix_card_upper n
  linarith

/-- Full signed J upper bound, before discarding either nonnegative correction. -/
theorem line_family_signed_allowance_le_explicit_log
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {R : Finset Nat}
    (hn : 4 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    let G := ownerLineFamilyHighFactorCells Gamma n T fivePrimePrefix R
    (G.card : Real)-lineCollisionCredit G <=
      (384/1001 : Real)*n+roughLogAllowance n+31-lineCollisionCredit G := by
  dsimp only
  exact _root_.sub_le_sub_right (line_family_card_le_explicit_log hn hcut) _

/-- The complete exact-prefix composite allowance, not merely its high part.
This is distinct from replacing the exact prefix by a rounded clock lower bound. -/
theorem exactPrefixCompositeAllowance_le_log
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {R : Finset Nat}
    (hn : 4 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    let G := ownerLineFamilyHighFactorCells Gamma n T fivePrimePrefix R
    exactPrefixCompositeAllowance n G <=
      2*(n : Real)+roughLogAllowance n-lineCollisionCredit G := by
  have hg := line_family_card_le_prefix_add_log (Gamma := Gamma) (T := T) hn hcut
  dsimp only
  unfold exactPrefixCompositeAllowance
  linarith

end Nat.PrimeSieve

namespace Finset

/-- Pair and double-fiber credits share the same finite support. A double
fiber consumes one whole support slot just as a triple fiber does. -/
theorem imageFiberPairs_add_twice_double_le_three_support
    {A B : Type*} [DecidableEq B] (s : Finset A) (f : A -> B) (H : Finset B)
    (hthree : forall b, (s.filter (fun a => f a = b)).card <= 3)
    (hoff : forall b, Not (Membership.mem H b) ->
      (s.filter (fun a => f a = b)).card <= 1) :
    imageFiberPairs s f + 2 * imageDoubleFibers s f <= 3 * H.card := by
  let I := s.image f
  let k := fun b => (s.filter (fun a => f a = b)).card
  have hpoint : forall b, Membership.mem I b ->
      (k b).choose 2 + 2 * (if k b = 2 then 1 else 0) <=
        3 * (if Membership.mem H b then 1 else 0) := by
    intro b _
    by_cases hb : Membership.mem H b
    next =>
      have hk : k b <= 3 := hthree b
      have hc : k b = 0 \/ k b = 1 \/ k b = 2 \/ k b = 3 := by omega
      rcases hc with h | h | h | h <;> norm_num [h, hb]
    next =>
      have hk : k b <= 1 := hoff b hb
      have hc : k b = 0 \/ k b = 1 := by omega
      rcases hc with h | h <;> norm_num [h, hb]
  have hd : I.sum (fun b => if k b = 2 then (1 : Nat) else 0) =
      imageDoubleFibers s f := by
    unfold imageDoubleFibers
    rw [card_eq_sum_ones, sum_filter]
  have hh : I.sum (fun b => if Membership.mem H b then (1 : Nat) else 0) =
      (I.filter (fun b => Membership.mem H b)).card := by
    rw [card_eq_sum_ones, sum_filter]
  have hsub : I.filter (fun b => Membership.mem H b) <= H := by
    intro b hb
    exact (mem_filter.mp hb).2
  calc
    imageFiberPairs s f + 2 * imageDoubleFibers s f =
        I.sum (fun b => (k b).choose 2 + 2 * (if k b = 2 then 1 else 0)) := by
      rw [sum_add_distrib, <- mul_sum, hd]
      rfl
    _ <= I.sum (fun b => 3 * (if Membership.mem H b then 1 else 0)) :=
      sum_le_sum hpoint
    _ = 3 * (I.filter (fun b => Membership.mem H b)).card := by
      rw [<- mul_sum, hh]
    _ <= 3 * H.card := Nat.mul_le_mul_left 3 (card_le_card hsub)

end Finset

namespace Nat.PrimeSieve

theorem line_family_pair_double_tradeoff
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 2 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    let G := ownerLineFamilyHighFactorCells Gamma n T S R
    Finset.imageFiberPairs G (fun x => x.1*x.2) +
      2 * Finset.imageDoubleFibers G (fun x => x.1*x.2) <=
        3 * (squareRoughSurvivors n).card := by
  apply Finset.imageFiberPairs_add_twice_double_le_three_support
  next => exact line_family_product_fiber_card_le_three hn hcut
  next => intro m hm; exact line_family_nonrough_fiber_card_le_one hn hcut hm

/-- This is an upper bound on the candidate lower-bound expression, NOT
an upper bound on the actual prime count. It tests the requested threshold. -/
theorem line_collision_log_score_le_neg_double
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 4 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    let G := ownerLineFamilyHighFactorCells Gamma n T S R
    lineCollisionCredit G - roughLogAllowance n <=
      -(Finset.imageDoubleFibers G (fun x => x.1*x.2) : Real) := by
  let G := ownerLineFamilyHighFactorCells Gamma n T S R
  have ht := line_family_pair_double_tradeoff (Gamma := Gamma) (T := T) (S := S)
    (by omega : 2 <= n) hcut
  have htr : (Finset.imageFiberPairs G (fun x => x.1*x.2) : Real) +
      2 * (Finset.imageDoubleFibers G (fun x => x.1*x.2) : Real) <=
        3 * ((squareRoughSurvivors n).card : Real) := by exact_mod_cast ht
  have hs := card_squareRoughSurvivors_le_explicit_log hn
  have hE : 2 * ((squareRoughSurvivors n).card : Real) <= roughLogAllowance n := by
    calc
      2 * ((squareRoughSurvivors n).card : Real) <=
          2 * (4*(n : Real)/Real.squareSieveDenominator n+(n : Real)/(Real.log n)^2) :=
        _root_.mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = roughLogAllowance n := by unfold roughLogAllowance; ring
  change lineCollisionCredit G - roughLogAllowance n <=
    -(Finset.imageDoubleFibers G (fun x => x.1*x.2) : Real)
  unfold lineCollisionCredit
  linarith only [htr, hE]

/-- Every valid pair of lower estimates inherits the same incompatibility;
replacing exact credits by lower bounds cannot make this envelope positive. -/
theorem line_collision_lower_estimates_nonpositive
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 4 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell)
    {A B : Real}
    (hA : A <= (Finset.imageFiberPairs
      (ownerLineFamilyHighFactorCells Gamma n T S R) (fun x => x.1*x.2) : Real))
    (hB : B <= (Finset.imageDoubleFibers
      (ownerLineFamilyHighFactorCells Gamma n T S R) (fun x => x.1*x.2) : Real)) :
    (2*A+B)/3 - roughLogAllowance n <= 0 := by
  have ht := line_collision_log_score_le_neg_double (Gamma := Gamma) (T := T) (S := S) hn hcut
  dsimp only at ht
  unfold lineCollisionCredit at ht
  have hz : (0 : Real) <= (Finset.imageDoubleFibers
    (ownerLineFamilyHighFactorCells Gamma n T S R) (fun x => x.1*x.2) : Real) := by positivity
  linarith only [ht, hA, hB, hz]

end Nat.PrimeSieve
