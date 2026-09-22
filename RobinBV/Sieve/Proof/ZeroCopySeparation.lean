/- Separation of finite zero copies used by the corridor decomposition. -/
import RobinBV.Mathlib.Analysis.Complex.FiniteMultiplicityCopies
import RobinBV.Mathlib.Analysis.Complex.FiniteNeighborhoodColor
import RobinBV.Sieve.Proof.ZeroClosedWindow

/-!
# Separated classes of actual zeta-zero copies

Exact indexed multiplicity mass bounds every closed neighborhood, and finite
relation coloring constructs classes at the required spacing. The ambient copy
type is independent of analytic parameters; sign labels remain separate for
annular consumers.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem zeta_zero_copy_separation :
    exists C : Real, 1 <= C /\
      forall (T Delta : Real), 2 <= T -> 1 <= Delta -> Delta <= T ->
      forall A : Finset Complex,
      (forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) ->
      (forall rho, (A : Set Complex) rho -> abs rho.im <= 2*T) ->
      let B := C*(2*Delta+2)*Real.log (3*T+4)
      let K := Nat.ceil B+1
      (K : Real) <= B+2 /\
      exists color : Sigma (fun _ : Complex => Nat) -> Fin K,
        forall x, Membership.mem (Finset.natMultiplicityCopies A Zeta23.zeroMult) x ->
        forall y, Membership.mem (Finset.natMultiplicityCopies A Zeta23.zeroMult) y ->
        Not (x = y) -> color x = color y -> Delta <= abs (x.1.im-y.1.im) := by
  classical
  cases zeta_zero_height_window_mass with
  | intro C hC =>
    refine Exists.intro C (And.intro hC.1 ?_)
    intro T Delta hT hD hDT A hA hheight
    let B : Real := C*(2*Delta+2)*Real.log (3*T+4)
    let K : Nat := Nat.ceil B+1
    let S := Finset.natMultiplicityCopies A Zeta23.zeroMult
    let r : Sigma (fun _ : Complex => Nat) ->
        Sigma (fun _ : Complex => Nat) -> Prop :=
      fun x y => abs (y.1.im-x.1.im) < Delta
    have hB : 0 <= B := by
      exact mul_nonneg
        (mul_nonneg (zero_le_one.trans hC.1) (by linarith only [hD]))
        (Real.log_nonneg (by linarith only [hT]))
    have hK : 0 < K := Nat.zero_lt_succ _
    have hKbound : (K : Real) <= B+2 := by
      have hh := Nat.ceil_lt_add_one hB
      dsimp only [K]
      push_cast
      linarith
    have hsym : forall x y, r x y -> r y x := by
      intro x y hxy
      change abs (x.1.im-y.1.im) < Delta
      rw [abs_sub_comm]
      exact hxy
    have hbound : forall x, Membership.mem S x -> (S.filter (r x)).card < K := by
      intro x hx
      have hxA : (A : Set Complex) x.1 :=
        (Finset.mem_natMultiplicityCopies A Zeta23.zeroMult x).mp hx |>.1
      have hmass := hC.2 T Delta x.1.im hT hD hDT (hheight x.1 hxA) A hA
      have hsub : S.filter (r x) <=
          S.filter (fun y => abs (y.1.im-x.1.im) <= Delta) := by
        intro y hy
        have hp := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr (And.intro hp.1 (le_of_lt hp.2))
      have hcardCast : ((S.filter (r x)).card : Real) <=
          ((S.filter (fun y => abs (y.1.im-x.1.im) <= Delta)).card : Real) := by
        exact_mod_cast Finset.card_le_card hsub
      have hclosed :
          ((S.filter (fun y => abs (y.1.im-x.1.im) <= Delta)).card : Real) =
            (A.filter (fun rho => abs (rho.im-x.1.im) <= Delta)).sum
              (fun rho => (Zeta23.zeroMult rho : Real)) := by
        dsimp only [S]
        rw [Finset.card_filter_natMultiplicityCopies A Zeta23.zeroMult
          (fun rho => abs (rho.im-x.1.im) <= Delta), Nat.cast_sum]
      have hreal : ((S.filter (r x)).card : Real) <= B := by
        rw [hclosed] at hcardCast
        exact hcardCast.trans hmass
      have hceil : ((S.filter (r x)).card : Real) <= (Nat.ceil B : Real) :=
        hreal.trans (Nat.le_ceil B)
      have hn : (S.filter (r x)).card <= Nat.ceil B := by
        exact_mod_cast hceil
      exact Nat.lt_succ_of_le hn
    cases Finset.exists_coloring_of_finite_neighborhood S r hsym K hK hbound with
    | intro color hcolor =>
      refine And.intro hKbound (Exists.intro color ?_)
      intro x hx y hy hne hsame
      have hsep : Delta <= abs (y.1.im-x.1.im) :=
        le_of_not_gt (hcolor x hx y hy hne hsame)
      rwa [abs_sub_comm] at hsep

end RobinBV.Sieve
