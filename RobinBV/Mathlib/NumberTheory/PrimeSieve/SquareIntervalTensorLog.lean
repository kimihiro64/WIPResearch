/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalTensorSieve

/-!
# An explicit logarithmic balanced-owner allowance

The integer root cutoff discharges every tensor-sieve parameter condition.
For n >= 64^78 the balanced allowance is bounded by explicit multiples of
n/log(n)^2 and n/log(n)^4. This is a component estimate; the full actual
prime-count consumer still retains the unestimated middle joint allowance.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

theorem balanced_tensor_power_budget {n Q : Nat} (hQ : 64 <= Q) (hn : Q^78 <= n) :
    2*Q <= n /\ 2*(Q*Q)*(Q^5)^15 <= n /\ 64*Q^4*(Q^5)^14 <= n := by
  have hQ77 : Q <= Q^77 := Nat.le_self_pow (by decide) Q
  have hscale : 2*(Q*Q)*(Q^5)^15 <= Q^78 := by
    have h := Nat.mul_le_mul_left (Q^77) (show 2 <= Q by omega)
    convert h using 1 <;> ring
  have hbudget : 64*Q^4*(Q^5)^14 <= Q^78 := by
    have hp : Q <= Q^4 := Nat.le_self_pow (by decide) Q
    have h := Nat.mul_le_mul_left (Q^74) (hQ.trans hp)
    convert h using 1 <;> ring
  have hlinear : 2*Q <= 2*(Q*Q)*(Q^5)^15 := by
    have h := Nat.mul_le_mul_left 2 hQ77
    convert h using 1 <;> ring
  exact And.intro (hlinear.trans (hscale.trans hn))
    (And.intro (hscale.trans hn) (hbudget.trans hn))

theorem balanced_tensor_power_allowance_identity (n : Nat) {Q : Nat} (hQ : 1 <= Q) :
    balancedTensorAllowance n Q (Q^5) =
      (2*(n : Real)*Real.log 2)/(Real.log ((Q : Real)+1))^2+
        40*(n : Real)/Q+4*(Q : Real)^4+20*(Q : Real)^16-20*(Q : Real)^6 := by
  have hQ0 : Not ((Q : Real) = 0) := by
    exact_mod_cast (show Not (Q = 0) by omega)
  unfold balancedTensorAllowance
  push_cast
  field_simp [hQ0]
  <;> ring

theorem balanced_tensor_power_allowance_le {n Q : Nat}
    (hQ : 64 <= Q) (hn : Q^78 <= n) :
    balancedTensorAllowance n Q (Q^5) <=
      (2*(n : Real)*Real.log 2)/(Real.log ((Q : Real)+1))^2+
        41*(n : Real)/Q := by
  have hQpos : (0 : Real) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQ0 : Not ((Q : Real) = 0) := ne_of_gt hQpos
  have hQ61 : Q <= Q^61 := Nat.le_self_pow (by decide) Q
  have h24 : 24*Q^17 <= n := by
    have h := Nat.mul_le_mul_left (Q^17) (show 24 <= Q^61 by omega)
    have hp : 24*Q^17 <= Q^78 := by convert h using 1 <;> ring
    exact hp.trans hn
  have h24R : (24 : Real)*(Q : Real)^17 <= n := by exact_mod_cast h24
  have htail : (24 : Real)*(Q : Real)^16 <= (n : Real)/Q := by
    have h := div_le_div_of_nonneg_right h24R hQpos.le
    have he : (24*(Q : Real)^17)/(Q : Real) = 24*(Q : Real)^16 := by
      field_simp [hQ0]
      <;> ring
    rw [he] at h
    exact h
  have h416 : (Q : Real)^4 <= (Q : Real)^16 := by
    have h12 : 1 <= Q^12 := by
      have h := pow_pos (show 0 < Q by omega) 12
      omega
    have h := Nat.mul_le_mul_left (Q^4) h12
    have hnats : Q^4 <= Q^16 := by convert h using 1 <;> ring
    exact_mod_cast hnats
  rw [balanced_tensor_power_allowance_identity n (by omega)]
  simp only [div_eq_mul_inv] at htail
  simp only [div_eq_mul_inv]
  nlinarith only [htail, h416, pow_nonneg hQpos.le 6]

theorem balanced_tensor_root_data {n : Nat} (hn : 64^78 <= n) :
    let Q := Nat.nthRoot 78 n
    64 <= Q /\ Q^78 <= n /\ 0 < Real.log n /\
      Real.log n <= 78*Real.log ((Q : Real)+1) /\
        (Real.log n)^4 <= (48*78^4 : Real)*Q := by
  let Q := Nat.nthRoot 78 n
  have hQ : 64 <= Q := (Nat.le_nthRoot_iff (by decide : Not (78 = 0))).mpr hn
  have hpow : Q^78 <= n := Nat.pow_nthRoot_le (Or.inl (by decide : Not (78 = 0)))
  have h64 : (64 : Nat) <= 64^78 := Nat.le_self_pow (by decide) 64
  have hn2 : 2 <= n := by omega
  have hnR : (1 : Real) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : Real) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have hQ0 : (0 : Real) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQ1 : (1 : Real) <= Q := by exact_mod_cast (show 1 <= Q by omega)
  have hQplus : (0 : Real) < (Q : Real)+1 := by positivity
  have hlQ : 0 < Real.log ((Q : Real)+1) := Real.log_pos (by linarith)
  have hupper : (n : Real) < ((Q : Real)+1)^78 := by
    exact_mod_cast Nat.lt_pow_nthRoot_add_one (by decide : Not (78 = 0)) n
  have hlogupper : Real.log n <= 78*Real.log ((Q : Real)+1) := by
    have h := Real.log_le_log hn0 hupper.le
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hfour0 := Real.pow_div_factorial_le_exp (Real.log ((Q : Real)+1)) hlQ.le 4
  rw [Real.exp_log hQplus] at hfour0
  norm_num at hfour0
  have hfour : (Real.log ((Q : Real)+1))^4 <= 48*(Q : Real) := by
    nlinarith only [hfour0, hQ1]
  have hsq := _root_.mul_le_mul hlogupper hlogupper hlog.le (by positivity)
  have hpow4 := _root_.mul_le_mul hsq hsq
    (mul_nonneg hlog.le hlog.le) (by positivity)
  have hL4 : (Real.log n)^4 <= (78*Real.log ((Q : Real)+1))^4 := by
    nlinarith only [hpow4]
  have hfinal : (Real.log n)^4 <= (48*78^4 : Real)*Q := by
    calc
      _ <= (78*Real.log ((Q : Real)+1))^4 := hL4
      _ = (78 : Real)^4*(Real.log ((Q : Real)+1))^4 := by ring
      _ <= (78 : Real)^4*(48*(Q : Real)) :=
        _root_.mul_le_mul_of_nonneg_left hfour (by norm_num)
      _ = _ := by ring
  exact And.intro hQ (And.intro hpow (And.intro hlog (And.intro hlogupper hfinal)))

noncomputable def balancedTensorLogAllowance (n : Nat) : Real :=
  (2*78^2*Real.log 2)*(n : Real)/(Real.log n)^2+
    (41*48*78^4 : Real)*(n : Real)/(Real.log n)^4

set_option maxHeartbeats 400000 in
theorem balanced_tensor_root_allowance_le {n : Nat} (hn : 64^78 <= n) :
    balancedTensorAllowance n (Nat.nthRoot 78 n) ((Nat.nthRoot 78 n)^5) <=
      balancedTensorLogAllowance n := by
  let Q := Nat.nthRoot 78 n
  have hd := balanced_tensor_root_data hn
  change 64 <= Q /\ Q^78 <= n /\ 0 < Real.log n /\
    Real.log n <= 78*Real.log ((Q : Real)+1) /\
      (Real.log n)^4 <= (48*78^4 : Real)*Q at hd
  have hbase := balanced_tensor_power_allowance_le hd.1 hd.2.1
  have hL := hd.2.2.1
  have hL0 : Not (Real.log n = 0) := ne_of_gt hL
  have hQ0 : (0 : Real) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlQ : 0 < Real.log ((Q : Real)+1) := Real.log_pos (by linarith)
  have hloglower : Real.log n/78 <= Real.log ((Q : Real)+1) := by
    linarith only [hd.2.2.2.1]
  have hsq : (Real.log n/78)^2 <= (Real.log ((Q : Real)+1))^2 := by
    have h := _root_.mul_le_mul hloglower hloglower (by positivity) hlQ.le
    nlinarith only [h]
  have hmain : (2*(n : Real)*Real.log 2)/(Real.log ((Q : Real)+1))^2 <=
      (2*78^2*Real.log 2)*(n : Real)/(Real.log n)^2 := by
    calc
      _ <= (2*(n : Real)*Real.log 2)/(Real.log n/78)^2 :=
        _root_.div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      _ = _ := by field_simp [hL0] <;> ring
  have hden : (Real.log n)^4/(48*78^4 : Real) <= (Q : Real) := by
    linarith only [hd.2.2.2.2]
  have herr : 41*(n : Real)/Q <= (41*48*78^4 : Real)*(n : Real)/(Real.log n)^4 := by
    calc
      _ <= (41*(n : Real))/((Real.log n)^4/(48*78^4 : Real)) :=
        _root_.div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by field_simp [hL0] <;> ring
  exact hbase.trans (_root_.add_le_add hmain herr)

theorem screened_balanced_owner_card_le_tensor_log
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {S R : Finset Nat}
    (hn : 64^78 <= n)
    (hR : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= 2*n+1 ->
      Membership.mem R ell) :
    (((ownerLineFamilyHighFactorCells Gamma n T S R).filter
      (fun x => n < 2*x.1)).card : Real) <= balancedTensorLogAllowance n := by
  let Q := Nat.nthRoot 78 n
  have hd := balanced_tensor_root_data hn
  have hQ : 64 <= Q := hd.1
  have hpow : Q^78 <= n := hd.2.1
  have hb := balanced_tensor_power_budget hQ hpow
  have hQ5 : Q <= Q^5 := Nat.le_self_pow (by decide) Q
  have h64 : (64 : Nat) <= 64^78 := Nat.le_self_pow (by decide) 64
  have h := screened_balanced_owner_card_le_tensor (Gamma := Gamma) (T := T) (S := S)
    (by omega : 9 <= n) (by omega : 1 <= Q) (by omega : 2 <= Q^5)
    hb.1 hb.2.1 hb.2.2 hR
  exact h.trans (balanced_tensor_root_allowance_le hn)

theorem prime_count_ge_tensor_log_geometric_allowance
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) {n : Nat} (hn : 64^78 <= n) :
    let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix (balancedOwnerScreen n)
    (384/1001 : Real)*n-31-((G.filter (fun x => 2*x.1 <= n)).card : Real)-
      balancedTensorLogAllowance n+lineCollisionCredit G <=
        ((squareIntervalPrimes n).card : Real) := by
  let Q := Nat.nthRoot 78 n
  have hd := balanced_tensor_root_data hn
  have hQ : 64 <= Q := hd.1
  have hpow : Q^78 <= n := hd.2.1
  have hb := balanced_tensor_power_budget hQ hpow
  have hQ5 : Q <= Q^5 := Nat.le_self_pow (by decide) Q
  have h64 : (64 : Nat) <= 64^78 := Nat.le_self_pow (by decide) 64
  have h := prime_count_ge_tensor_geometric_allowance Gamma
    (by omega : 9 <= n) (by omega : 1 <= Q) (by omega : 2 <= Q^5)
    hb.1 hb.2.1 hb.2.2
  have hlog := balanced_tensor_root_allowance_le hn
  dsimp only at h
  dsimp only
  linarith only [h, hlog]

theorem balanced_tensor_log_allowance_le_single_log {n : Nat}
    (hL : (25000 : Real) <= Real.log n) :
    balancedTensorLogAllowance n <= (n : Real)/Real.log n := by
  let L := Real.log n
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hL0 : Not (L = 0) := ne_of_gt hLpos
  have hlog2 : Real.log 2 <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hcoef : 2*78^2*Real.log 2 <= (12168 : Real) := by nlinarith only [hlog2]
  have hpoly : (12168 : Real)*L^2+(41*48*78^4 : Real) <= L^3 := by
    have hbase : (25000 : Real) <= L := hL
    have hc := mul_nonneg (sub_nonneg.mpr hbase) (sq_nonneg L)
    nlinarith [sq_nonneg (L-25000)]
  have hprod := _root_.mul_le_mul_of_nonneg_right hcoef (sq_nonneg L)
  have hpoly' : (2*78^2*Real.log 2)*L^2+(41*48*78^4 : Real) <= L^3 := by
    linarith only [hpoly, hprod]
  have hnum := _root_.mul_le_mul_of_nonneg_right hpoly' (Nat.cast_nonneg n)
  have hdiv := div_le_div_of_nonneg_right hnum (pow_nonneg hLpos.le 4)
  change balancedTensorLogAllowance n <= (n : Real)/L
  calc
    _ = (((2*78^2*Real.log 2)*L^2+(41*48*78^4 : Real))*(n : Real))/L^4 := by
      unfold balancedTensorLogAllowance
      change (2*78^2*Real.log 2)*(n : Real)/L^2+
        (41*48*78^4 : Real)*(n : Real)/L^4 = _
      field_simp [hL0]
      <;> ring
    _ <= (L^3*(n : Real))/L^4 := hdiv
    _ = _ := by field_simp [hL0] <;> ring

end Nat.PrimeSieve
