/- Closed-window separation and endpoint inequalities for zero packets. -/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zeta23.RvM.LocalCount
import Zeta23.RvM.NcountWindow

/-!
# Complete multiplicity mass in closed zero-height windows

The actual unit-window count is summed over an exact disjoint half-open
partition. The extra unit at the left retains the closed lower endpoint, and
all zero multiplicities remain explicit. The absolute constant is inherited
existentially from the local Riemann--von Mangoldt count.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

private theorem zeroWindow_ncount_nat (a : Real) (m : Nat) :
    Zeta23.Ncount a (a+((m+1 : Nat) : Real)) =
      (Finset.range (m+1)).sum (fun j =>
        Zeta23.Ncount (a+(j : Real)) (a+(j : Real)+1)) := by
  induction m with
  | zero =>
    simp only [Nat.zero_add, Nat.cast_one, Finset.range_one,
      Finset.sum_singleton, Nat.cast_zero, add_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ, <- ih]
    have ht : a+((m+1+1 : Nat) : Real) = a+((m+1 : Nat) : Real)+1 := by
      push_cast
      ring
    rw [ht]
    exact Zeta23.Ncount_add
      (by
        have hm : (0 : Real) <= ((m+1 : Nat) : Real) := Nat.cast_nonneg _
        linarith)
      (by linarith)

private theorem zeroWindow_ceil_bounds (Delta : Real) (hD : 0 <= Delta) :
    (1 : Real) <= (Nat.ceil (2*Delta+1) : Real) /\
      (Nat.ceil (2*Delta+1) : Real) < 2*Delta+2 := by
  have hlo := Nat.le_ceil (2*Delta+1)
  have hhi := Nat.ceil_lt_add_one (by linarith : 0 <= 2*Delta+1)
  exact And.intro (by linarith) (by linarith)

private theorem zeroWindow_mass_le_count (A : Finset Complex) {a b : Real}
    (hA : forall rho, (A : Set Complex) rho -> Zeta23.zerosIn a b rho) :
    A.sum (fun rho => (Zeta23.zeroMult rho : Real)) <= (Zeta23.Ncount a b : Real) := by
  classical
  have hn : A.sum Zeta23.zeroMult <= Zeta23.Ncount a b := by
    rw [Zeta23.Ncount, finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite a b)]
    apply Finset.sum_le_sum_of_subset
    intro rho hrho
    exact (Set.Finite.mem_toFinset (Zeta23.zerosIn_finite a b)).mpr (hA rho hrho)
  exact_mod_cast hn

private theorem zeroWindow_mass_of_local_count {C : Real} (hC : 0 <= C)
    (hlocal : forall t : Real, (Zeta23.Ncount t (t+1) : Real) <=
      C*Real.log (abs t+3))
    (Delta c : Real) (hD : 0 <= Delta) (A : Finset Complex)
    (hA : forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) :
    (A.filter (fun rho => abs (rho.im-c) <= Delta)).sum
      (fun rho => (Zeta23.zeroMult rho : Real)) <=
      C*(2*Delta+2)*Real.log (abs c+Delta+4) := by
  classical
  let M : Nat := Nat.ceil (2*Delta+1)
  let a : Real := c-Delta-1
  have hMone : (1 : Real) <= (M : Real) := (zeroWindow_ceil_bounds Delta hD).1
  have hMhi : (M : Real) < 2*Delta+2 := (zeroWindow_ceil_bounds Delta hD).2
  have hMlo : 2*Delta+1 <= (M : Real) := Nat.le_ceil _
  have hmass :
      (A.filter (fun rho => abs (rho.im-c) <= Delta)).sum
        (fun rho => (Zeta23.zeroMult rho : Real)) <=
      (Zeta23.Ncount a (a+(M : Real)) : Real) := by
    apply zeroWindow_mass_le_count
    intro rho hrho
    have hm := Finset.mem_filter.mp hrho
    have hdist := abs_le.mp hm.2
    refine And.intro (hA rho hm.1) (And.intro ?_ ?_)
    next =>
      dsimp only [a]
      linarith only [hdist.1]
    next =>
      dsimp only [a]
      linarith only [hdist.2, hMlo]
  have hsplitNat : Zeta23.Ncount a (a+(M : Real)) =
      (Finset.range M).sum (fun j =>
        Zeta23.Ncount (a+(j : Real)) (a+(j : Real)+1)) := by
    cases hM : M with
    | zero =>
      norm_num [hM] at hMone
    | succ m =>
      simpa only [Nat.succ_eq_add_one] using zeroWindow_ncount_nat a m
  have hsplit : (Zeta23.Ncount a (a+(M : Real)) : Real) =
      (Finset.range M).sum (fun j =>
        (Zeta23.Ncount (a+(j : Real)) (a+(j : Real)+1) : Real)) := by
    exact_mod_cast hsplitNat
  have hrow (j : Nat) (hj : Membership.mem (Finset.range M) j) :
      (Zeta23.Ncount (a+(j : Real)) (a+(j : Real)+1) : Real) <=
        C*Real.log (abs c+Delta+4) := by
    have hj0 : (0 : Real) <= (j : Real) := Nat.cast_nonneg _
    have hjM : (j : Real) < (M : Real) := by exact_mod_cast Finset.mem_range.mp hj
    have hstart : abs (a+(j : Real)) <= abs c+Delta+1 := by
      dsimp only [a]
      apply abs_le.mpr
      constructor
      next =>
        linarith only [neg_abs_le c, hj0]
      next =>
        linarith only [le_abs_self c, hjM, hMhi]
    have hlog := Real.log_le_log
      (by linarith [abs_nonneg (a+(j : Real))] : 0 < abs (a+(j : Real))+3)
      (by linarith only [hstart] : abs (a+(j : Real))+3 <= abs c+Delta+4)
    exact (hlocal (a+(j : Real))).trans (mul_le_mul_of_nonneg_left hlog hC)
  have hlog0 : 0 <= Real.log (abs c+Delta+4) :=
    Real.log_nonneg (by linarith only [hD, abs_nonneg c])
  calc
    _ <= (Zeta23.Ncount a (a+(M : Real)) : Real) := hmass
    _ = (Finset.range M).sum (fun j =>
        (Zeta23.Ncount (a+(j : Real)) (a+(j : Real)+1) : Real)) := hsplit
    _ <= (Finset.range M).sum (fun _ => C*Real.log (abs c+Delta+4)) :=
      Finset.sum_le_sum (fun j hj => hrow j hj)
    _ = (M : Real)*(C*Real.log (abs c+Delta+4)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    _ <= (2*Delta+2)*(C*Real.log (abs c+Delta+4)) :=
      mul_le_mul_of_nonneg_right hMhi.le (mul_nonneg hC hlog0)
    _ = _ := by ring

theorem zeta_zero_closed_window_mass :
    exists C : Real, 1 <= C /\
      forall (Delta c : Real), 0 <= Delta ->
      forall A : Finset Complex,
      (forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) ->
      (A.filter (fun rho => abs (rho.im-c) <= Delta)).sum
        (fun rho => (Zeta23.zeroMult rho : Real)) <=
        C*(2*Delta+2)*Real.log (abs c+Delta+4) := by
  cases Zeta23.RvM.zeta_local_zero_count with
  | intro C hC =>
    refine Exists.intro C (And.intro hC.1 ?_)
    intro Delta c hD A hA
    exact zeroWindow_mass_of_local_count (zero_le_one.trans hC.1) hC.2 Delta c hD A hA

theorem zeta_zero_height_window_mass :
    exists C : Real, 1 <= C /\
      forall (T Delta c : Real), 2 <= T -> 1 <= Delta -> Delta <= T -> abs c <= 2*T ->
      forall A : Finset Complex,
      (forall rho, (A : Set Complex) rho -> Zeta23.IsNontrivialZero rho) ->
      (A.filter (fun rho => abs (rho.im-c) <= Delta)).sum
        (fun rho => (Zeta23.zeroMult rho : Real)) <=
        C*(2*Delta+2)*Real.log (3*T+4) := by
  cases zeta_zero_closed_window_mass with
  | intro C hC =>
    refine Exists.intro C (And.intro hC.1 ?_)
    intro T Delta c _hT hD hDT hc A hA
    have hbase := hC.2 Delta c (zero_le_one.trans hD) A hA
    have hlog := Real.log_le_log
      (by linarith [abs_nonneg c] : 0 < abs c+Delta+4)
      (by linarith only [hc, hDT] : abs c+Delta+4 <= 3*T+4)
    exact hbase.trans (mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (zero_le_one.trans hC.1) (by linarith only [hD])))

end RobinBV.Sieve
