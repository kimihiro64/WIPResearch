/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalSkewTensor

/-!
# Closed logarithmic bounds for skew least-owner bands

An integer-root cutoff discharges every sieve parameter when n^3 <= M^4.
The resulting band bound depends only on explicit powers and logarithms of n.
The full prime-count consumer retains the still-unestimated middle complement.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

theorem skew_tensor_power_budget {n M Q : Nat}
    (hQ : 64 <= Q) (hn : Q^312 <= n) (hM : n^3 <= M^4) :
    2*Q <= M /\ 2*(Q*Q)*(Q^5)^15 <= M /\
      64*Q^4*n^2*(Q^5)^14 <= M^3 := by
  have hQ234 : Q^234 <= M := by
    have hpow : Q^936 <= M^4 := by
      have h : (Q^312)^3 <= n^3 := by gcongr
      have he : (Q^312)^3 = Q^936 := by ring
      rw [he] at h
      exact h.trans hM
    by_contra h
    have hlt : M^4 < (Q^234)^4 := by gcongr; omega
    have he : (Q^234)^4 = Q^936 := by ring
    rw [he] at hlt
    omega
  have hQ157 : Q <= Q^157 := Nat.le_self_pow (by decide) Q
  have hscale : 2*(Q*Q)*(Q^5)^15 <= M := by
    have h := Nat.mul_le_mul_left (Q^77) (show 2 <= Q^157 by omega)
    have he : 2*(Q*Q)*(Q^5)^15 <= Q^234 := by convert h using 1 <;> ring
    exact he.trans hQ234
  have hQ77 : Q <= Q^77 := Nat.le_self_pow (by decide) Q
  have hlinear : 2*Q <= 2*(Q*Q)*(Q^5)^15 := by
    have h := Nat.mul_le_mul_left 2 hQ77
    convert h using 1 <;> ring
  have hQ4 : Q <= Q^4 := Nat.le_self_pow (by decide) Q
  have hcoef : 64*Q^74 <= Q^78 := by
    have h := Nat.mul_le_mul_left (Q^74) (hQ.trans hQ4)
    convert h using 1 <;> ring
  have hcoef4 : (64*Q^74)^4 <= n := by
    have h : (64*Q^74)^4 <= (Q^78)^4 := by gcongr
    have he : (Q^78)^4 = Q^312 := by ring
    rw [he] at h
    exact h.trans hn
  have hfour : (64*Q^4*n^2*(Q^5)^14)^4 <= (M^3)^4 := by
    have h1 := Nat.mul_le_mul_right (n^8) hcoef4
    have h2 : (n^3)^3 <= (M^4)^3 := by gcongr
    have h1' : (64*Q^4*n^2*(Q^5)^14)^4 <= n^9 := by
      convert h1 using 1 <;> ring
    have h2' : n^9 <= (M^3)^4 := by convert h2 using 1 <;> ring
    exact h1'.trans h2'
  have hbudget : 64*Q^4*n^2*(Q^5)^14 <= M^3 := by
    by_contra h
    have hlt : (M^3)^4 < (64*Q^4*n^2*(Q^5)^14)^4 := by gcongr; omega
    omega
  exact And.intro (hlinear.trans hscale) (And.intro hscale hbudget)

theorem skew_tensor_power_allowance_identity {n M Q : Nat}
    (hQ : 1 <= Q) (hM : 0 < M) :
    skewTensorAllowance n M Q (Q^5) =
      (2*(n : Real)*Real.log 2)/(Real.log ((Q : Real)+1))^2+
        40*(M : Real)/Q+4*(n : Real)*(Q : Real)^4/M+
          20*(M : Real)^2*((Q : Real)^16-(Q : Real)^6)/(n : Real)^2 := by
  have hQ0 : Not ((Q : Real) = 0) := by
    exact_mod_cast (show Not (Q = 0) by omega)
  have hM0 : Not ((M : Real) = 0) := by
    exact_mod_cast (show Not (M = 0) by omega)
  unfold skewTensorAllowance
  push_cast
  field_simp [hQ0, hM0]
  <;> ring

theorem skew_tensor_power_allowance_le {n M Q : Nat}
    (hQ : 64 <= Q) (hn : Q^312 <= n) (hM : n^3 <= M^4) (hMn : M <= n) :
    skewTensorAllowance n M Q (Q^5) <=
      (2*(n : Real)*Real.log 2)/(Real.log ((Q : Real)+1))^2+
        41*(n : Real)/Q := by
  have hbud := skew_tensor_power_budget hQ hn hM
  have hQ0n : 0 < Q := by omega
  have hQ0 : (0 : Real) < Q := by exact_mod_cast hQ0n
  have hQne : Not ((Q : Real)=0) := ne_of_gt hQ0
  have hn0n : 0 < n := (pow_pos hQ0n 312).trans_le hn
  have hn0 : (0 : Real) < n := by exact_mod_cast hn0n
  have hnne : Not ((n : Real)=0) := ne_of_gt hn0
  have hM0 : (0 : Real) < M := by
    exact_mod_cast (show 0 < M by omega)
  have hMnR : (M : Real) <= n := by exact_mod_cast hMn
  have hQ72 : Q <= Q^72 := Nat.le_self_pow (by decide) Q
  have h8 : 8*Q^5 <= M := by
    have h := Nat.mul_le_mul_left (2*Q^5) (show 4 <= Q^72 by omega)
    have h' : 8*Q^5 <= 2*(Q*Q)*(Q^5)^15 := by convert h using 1 <;> ring
    exact h'.trans hbud.2.1
  have h8R : (8 : Real)*(Q : Real)^5 <= M := by exact_mod_cast h8
  have hQ295 : Q <= Q^295 := Nat.le_self_pow (by decide) Q
  have h40 : 40*Q^17 <= n := by
    have h := Nat.mul_le_mul_left (Q^17) (show 40 <= Q^295 by omega)
    have h' : 40*Q^17 <= Q^312 := by convert h using 1 <;> ring
    exact h'.trans hn
  have h40R : (40 : Real)*(Q : Real)^17 <= n := by exact_mod_cast h40
  have hmain : 40*(M : Real)/Q <= 40*(n : Real)/Q :=
    div_le_div_of_nonneg_right (by linarith only [hMnR]) hQ0.le
  have hunit : 4*(n : Real)*(Q : Real)^4/M <= (n : Real)/(2*Q) := by
    calc
      _ <= (4*(n : Real)*(Q : Real)^4)/(8*(Q : Real)^5) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h8R
      _ = _ := by field_simp [hQne] <;> ring
  have hsquare : (M : Real)^2 <= (n : Real)^2 := by gcongr
  have hdrop : 20*(M : Real)^2*((Q : Real)^16-(Q : Real)^6)/(n : Real)^2 <=
      20*(M : Real)^2*(Q : Real)^16/(n : Real)^2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h := mul_nonneg (show 0 <= 20*(M : Real)^2 by positivity)
      (pow_nonneg hQ0.le 6)
    nlinarith only [h]
  have hlarge : 20*(M : Real)^2*(Q : Real)^16/(n : Real)^2 <=
      20*(Q : Real)^16 := by
    calc
      _ <= (20*(n : Real)^2*(Q : Real)^16)/(n : Real)^2 := by gcongr
      _ = _ := by field_simp [hnne]
  have htail : 20*(Q : Real)^16 <= (n : Real)/(2*Q) := by
    calc
      _ = (40*(Q : Real)^17)/(2*Q) := by field_simp [hQne] <;> ring
      _ <= _ := div_le_div_of_nonneg_right h40R (by positivity)
  rw [skew_tensor_power_allowance_identity (by omega) (by omega)]
  have hcomplete := hdrop.trans (hlarge.trans htail)
  have hsum := _root_.add_le_add (_root_.add_le_add hmain hunit) hcomplete
  have he : 40*(n : Real)/Q+(n : Real)/(2*Q)+(n : Real)/(2*Q) = 41*(n : Real)/Q := by ring
  rw [he] at hsum
  linarith only [hsum]

theorem skew_tensor_root_data {n : Nat} (hn : 64^312 <= n) :
    let Q := Nat.nthRoot 312 n
    64 <= Q /\ Q^312 <= n /\ 0 < Real.log n /\
      Real.log n <= 312*Real.log ((Q : Real)+1) /\
        (Real.log n)^4 <= (48*312^4 : Real)*Q := by
  let Q := Nat.nthRoot 312 n
  have hQ : 64 <= Q := (Nat.le_nthRoot_iff (by decide : Not (312 = 0))).mpr hn
  have hpow : Q^312 <= n := Nat.pow_nthRoot_le (Or.inl (by decide : Not (312 = 0)))
  have h64 : (64 : Nat) <= 64^312 := Nat.le_self_pow (by decide) 64
  have hn2 : 2 <= n := by omega
  have hnR : (1 : Real) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : Real) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have hQ0 : (0 : Real) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQ1 : (1 : Real) <= Q := by exact_mod_cast (show 1 <= Q by omega)
  have hQplus : (0 : Real) < (Q : Real)+1 := by positivity
  have hlQ : 0 < Real.log ((Q : Real)+1) := Real.log_pos (by linarith)
  have hupper : (n : Real) < ((Q : Real)+1)^312 := by
    exact_mod_cast Nat.lt_pow_nthRoot_add_one (by decide : Not (312 = 0)) n
  have hlogupper : Real.log n <= 312*Real.log ((Q : Real)+1) := by
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
  have hL4 : (Real.log n)^4 <= (312*Real.log ((Q : Real)+1))^4 := by
    nlinarith only [hpow4]
  have hfinal : (Real.log n)^4 <= (48*312^4 : Real)*Q := by
    calc
      _ <= (312*Real.log ((Q : Real)+1))^4 := hL4
      _ = (312 : Real)^4*(Real.log ((Q : Real)+1))^4 := by ring
      _ <= (312 : Real)^4*(48*(Q : Real)) :=
        _root_.mul_le_mul_of_nonneg_left hfour (by norm_num)
      _ = _ := by ring
  exact And.intro hQ (And.intro hpow (And.intro hlog (And.intro hlogupper hfinal)))

noncomputable def skewTensorLogAllowance (n : Nat) : Real :=
  (2*312^2*Real.log 2)*(n : Real)/(Real.log n)^2+
    (41*48*312^4 : Real)*(n : Real)/(Real.log n)^4

set_option maxHeartbeats 400000 in
theorem skew_tensor_root_allowance_le {n M : Nat} (hn : 64^312 <= n)
    (hM : n^3 <= M^4) (hMn : M <= n) :
    skewTensorAllowance n M (Nat.nthRoot 312 n) ((Nat.nthRoot 312 n)^5) <=
      skewTensorLogAllowance n := by
  let Q := Nat.nthRoot 312 n
  have hd := skew_tensor_root_data hn
  change 64 <= Q /\ Q^312 <= n /\ 0 < Real.log n /\
    Real.log n <= 312*Real.log ((Q : Real)+1) /\
      (Real.log n)^4 <= (48*312^4 : Real)*Q at hd
  have hbase := skew_tensor_power_allowance_le hd.1 hd.2.1 hM hMn
  have hL := hd.2.2.1
  have hL0 : Not (Real.log n = 0) := ne_of_gt hL
  have hQ0 : (0 : Real) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlQ : 0 < Real.log ((Q : Real)+1) := Real.log_pos (by linarith)
  have hloglower : Real.log n/312 <= Real.log ((Q : Real)+1) := by
    linarith only [hd.2.2.2.1]
  have hsq : (Real.log n/312)^2 <= (Real.log ((Q : Real)+1))^2 := by
    have h := _root_.mul_le_mul hloglower hloglower (by positivity) hlQ.le
    nlinarith only [h]
  have hmain : (2*(n : Real)*Real.log 2)/(Real.log ((Q : Real)+1))^2 <=
      (2*312^2*Real.log 2)*(n : Real)/(Real.log n)^2 := by
    calc
      _ <= (2*(n : Real)*Real.log 2)/(Real.log n/312)^2 :=
        _root_.div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      _ = _ := by field_simp [hL0] <;> ring
  have hden : (Real.log n)^4/(48*312^4 : Real) <= (Q : Real) := by
    linarith only [hd.2.2.2.2]
  have herr : 41*(n : Real)/Q <= (41*48*312^4 : Real)*(n : Real)/(Real.log n)^4 := by
    calc
      _ <= (41*(n : Real))/((Real.log n)^4/(48*312^4 : Real)) :=
        _root_.div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by field_simp [hL0] <;> ring
  exact hbase.trans (_root_.add_le_add hmain herr)

theorem canonical_skew_owner_card_le_tensor_log
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n M : Nat} {S : Finset Nat}
    (hn : 64^312 <= n) (hM : n^3 <= M^4) (hMn : M <= n) :
    (((canonicalOwnerFamily Gamma n S).filter
      (fun x => M < 2*x.1 /\ x.1 <= M)).card : Real) <=
        skewTensorLogAllowance n := by
  let Q := Nat.nthRoot 312 n
  have hd := skew_tensor_root_data hn
  have hQ : 64 <= Q := hd.1
  have hpow : Q^312 <= n := hd.2.1
  have hbud := skew_tensor_power_budget hQ hpow hM
  have h64 : (64 : Nat) <= 64^312 := Nat.le_self_pow (by decide) 64
  have hn2 : 2 <= n := by omega
  have hMpos : 0 < M := by omega
  have hQ5 : Q <= Q^5 := Nat.le_self_pow (by decide) Q
  have hraw := canonical_skew_owner_card_le_tensor (Gamma := Gamma) (S := S)
    hn2 hMpos (show 1 <= Q by omega) (show 2 <= Q^5 by omega)
    hbud.1 hbud.2.1 hbud.2.2
  exact hraw.trans (skew_tensor_root_allowance_le hn hM hMn)

theorem prime_count_ge_canonical_skew_tensor_log
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) {n M : Nat}
    (hn : 64^312 <= n) (hM : n^3 <= M^4) (hMn : 2*M <= n) :
    let C := canonicalOwnerFamily Gamma n fivePrimePrefix
    let L := C.filter (fun x => 2*x.1 <= n)
    (384/1001 : Real)*n-31-
      ((L.filter (fun x => Not (M < 2*x.1 /\ x.1 <= M))).card : Real)-
      skewTensorLogAllowance n-balancedTensorLogAllowance n <=
        ((squareIntervalPrimes n).card : Real) := by
  let Q := Nat.nthRoot 312 n
  have hd := skew_tensor_root_data hn
  have hQ : 64 <= Q := hd.1
  have hpow : Q^312 <= n := hd.2.1
  have hbud := skew_tensor_power_budget hQ hpow hM
  have hQ5 : Q <= Q^5 := Nat.le_self_pow (by decide) Q
  have hMpos : 0 < M := by omega
  have hexp : (64 : Nat)^78 <= 64^312 := by
    change (64 : Nat)^78 <= 64^(78*4)
    rw [pow_mul]
    exact Nat.le_self_pow (by decide : Not (4 = 0)) ((64 : Nat)^78)
  have hP := prime_count_ge_canonical_skew_tensor Gamma (hexp.trans hn) hMpos hMn
    (show 1 <= Q by omega) (show 2 <= Q^5 by omega)
    hbud.1 hbud.2.1 hbud.2.2
  have hB := skew_tensor_root_allowance_le hn hM (show M <= n by omega)
  dsimp only at hP
  dsimp only
  linarith only [hP, hB]

end Nat.PrimeSieve
