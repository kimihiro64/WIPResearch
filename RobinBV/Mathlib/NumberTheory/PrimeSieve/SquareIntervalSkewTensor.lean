/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalCanonicalOwner
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalSkewDivisor

/-!
# A tensor sieve for canonical least-owner bands

Canonical least-owner minimality sieves both coordinates, including arbitrary
composite cofactors. The complete two-coordinate remainder is retained and
connected to the actual prime count without estimating the remaining band.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

theorem tensorDivisorCount_skew {n M a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    tensorDivisorCount (skewDivisorRows n M 1 1) a b =
      (skewDivisorRows n M a b).card := by
  unfold tensorDivisorCount
  congr 1
  ext x
  have h11 := mem_skewDivisorRows_iff (n := n) (M := M) (a := 1) (b := 1)
    (p := x.1) (q := x.2) (by decide) (by decide)
  simp only [one_dvd, true_and] at h11
  rw [Finset.mem_filter, h11, mem_skewDivisorRows_iff ha hb]
  constructor
  next => exact fun h => And.intro h.2.1 (And.intro h.2.2 h.1)
  next => exact fun h => And.intro h.2.2 (And.intro h.1 h.2.1)

theorem skew_divisor_row_uniform_error {n M Q t a b : Nat}
    (hn : 2 <= n) (hM : 0 < M) (ht : 2 <= t) (ha : 0 < a) (hb : 0 < b)
    (haQ : a <= Q*Q) (hbQ : b <= Q*Q)
    (hscale : 2*(Q*Q)*t^15 <= M) (hbudget : 64*Q^4*n^2*t^14 <= M^3) :
    abs (((skewDivisorRows n M a b).card : Real)-
      (2*(n : Real)*Real.log 2)/((a : Real)*b)) <=
        40*(M : Real)/t+4*(n : Real)/M+
          20*((t : Real)^2-1)*(M : Real)^2*(Q : Real)^2/(n : Real)^2 := by
  have ha2 : a^2 <= Q^4 := by
    have h := Nat.mul_le_mul haQ haQ
    nlinarith only [h]
  have hscaleA : 2*a*t^15 <= M := by
    have h := Nat.mul_le_mul_right (2*t^15) haQ
    nlinarith only [h, hscale]
  have hbudgetA : 64*a^2*n^2*t^14 <= M^3 := by
    have h := Nat.mul_le_mul_right (64*n^2*t^14) ha2
    nlinarith only [h, hbudget]
  have hraw := skewDivisorRows_abs_error hn ha hb ht hscaleA hbudgetA
  have he : (2*(n : Real)/((a : Real)*b))*Real.log 2 =
      (2*(n : Real)*Real.log 2)/((a : Real)*b) := by ring
  rw [he] at hraw
  have haR : (1 : Real) <= a := by exact_mod_cast (show 1 <= a by omega)
  have hbR : (1 : Real) <= b := by exact_mod_cast (show 1 <= b by omega)
  have htR : (2 : Real) <= t := by exact_mod_cast ht
  have ht0 : (0 : Real) < t := by linarith
  have hM0 : (0 : Real) < M := by exact_mod_cast hM
  have hbQR : (b : Real) <= (Q : Real)^2 := by
    rw [pow_two]
    exact_mod_cast hbQ
  have hmain : 40*(M : Real)/((a : Real)*t) <= 40*(M : Real)/t := by
    apply _root_.div_le_div_of_nonneg_left (by positivity) ht0
    nlinarith
  have hunit : 4*(n : Real)/((b : Real)*M) <= 4*(n : Real)/M := by
    apply _root_.div_le_div_of_nonneg_left (by positivity) hM0
    nlinarith
  have hratio : (b : Real)/a <= (Q : Real)^2 := by
    have h := _root_.div_le_div_of_nonneg_left (Nat.cast_nonneg b)
      (by norm_num : (0 : Real) < 1) haR
    have h' : (b : Real)/a <= b := by simpa only [div_one] using h
    exact h'.trans hbQR
  have hc : 0 <= 20*((t : Real)^2-1)*(M : Real)^2/(n : Real)^2 := by
    have hnn : 0 <= (t : Real)^2-1 := by nlinarith
    positivity
  have hcost : 20*((t : Real)^2-1)*(M : Real)^2*b/((a : Real)*(n : Real)^2) <=
      20*((t : Real)^2-1)*(M : Real)^2*(Q : Real)^2/(n : Real)^2 := by
    calc
      _ = (20*((t : Real)^2-1)*(M : Real)^2/(n : Real)^2)*((b : Real)/a) := by ring
      _ <= (20*((t : Real)^2-1)*(M : Real)^2/(n : Real)^2)*(Q : Real)^2 :=
        mul_le_mul_of_nonneg_left hratio hc
      _ = _ := by ring
  exact hraw.trans (_root_.add_le_add (_root_.add_le_add hmain hunit) hcost)

noncomputable def skewTensorAllowance (n M Q t : Nat) : Real :=
  (2*(n : Real)*Real.log 2)/(Real.log ((Q : Real)+1))^2+
    (40*(M : Real)/t+4*(n : Real)/M+
      20*((t : Real)^2-1)*(M : Real)^2*(Q : Real)^2/(n : Real)^2)*(Q : Real)^4

theorem skew_sifted_pairs_le_tensor {n M Q t : Nat}
    (hn : 2 <= n) (hM : 0 < M) (hQ : 1 <= Q) (ht : 2 <= t)
    (hscale : 2*(Q*Q)*t^15 <= M) (hbudget : 64*Q^4*n^2*t^14 <= M^3) :
    (((skewDivisorRows n M 1 1).filter (fun x =>
      Nat.Coprime (selbergPrimeProduct Q) x.1 /\
      Nat.Coprime (selbergPrimeProduct Q) x.2)).card : Real) <=
        skewTensorAllowance n M Q t := by
  have hc : (0 : Real) <= (t : Real)^2-1 := by
    have htr : (2 : Real) <= t := by exact_mod_cast ht
    nlinarith
  apply Nat.tensor_sifted_card_le_log_sieve _ hQ
    (2*(n : Real)*Real.log 2)
    (40*(M : Real)/t+4*(n : Real)/M+
      20*((t : Real)^2-1)*(M : Real)^2*(Q : Real)^2/(n : Real)^2)
    (by positivity) (by positivity)
  intro a ha haQ b hb hbQ
  rw [tensorDivisorCount_skew ha hb]
  exact skew_divisor_row_uniform_error hn hM ht ha hb haQ hbQ hscale hbudget

theorem canonical_owner_factors_coprime
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n Q : Nat} {S : Finset Nat}
    {x : Prod Nat Nat} (hn : 2 <= n)
    (hx : Membership.mem (canonicalOwnerFamily Gamma n S) x) (hQp : Q < x.1) :
    Nat.Coprime (selbergPrimeProduct Q) x.1 /\
      Nat.Coprime (selbergPrimeProduct Q) x.2 := by
  have hcanon := canonical_owner_first_eq_minFac hn hx
  have hcop (r : Nat) (hr : Dvd.dvd r (x.1*x.2)) :
      Nat.Coprime (selbergPrimeProduct Q) r := by
    apply Nat.coprime_of_dvd
    intro ell hell hprod hdiv
    have hbound := (prime_dvd_selbergPrimeProduct_iff hell).mp hprod
    have hmin := Nat.minFac_le_of_dvd hell.two_le (dvd_trans hdiv hr)
    rw [<- hcanon] at hmin
    omega
  exact And.intro (hcop x.1 (dvd_mul_right x.1 x.2))
    (hcop x.2 (dvd_mul_left x.2 x.1))

theorem canonical_skew_owner_card_le_tensor
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n M Q t : Nat} {S : Finset Nat}
    (hn : 2 <= n) (hM : 0 < M) (hQ : 1 <= Q) (ht : 2 <= t) (hQM : 2*Q <= M)
    (hscale : 2*(Q*Q)*t^15 <= M) (hbudget : 64*Q^4*n^2*t^14 <= M^3) :
    (((canonicalOwnerFamily Gamma n S).filter
      (fun x => M < 2*x.1 /\ x.1 <= M)).card : Real) <=
        skewTensorAllowance n M Q t := by
  have hsub : (canonicalOwnerFamily Gamma n S).filter
      (fun x => M < 2*x.1 /\ x.1 <= M) <=
      (skewDivisorRows n M 1 1).filter (fun x =>
        Nat.Coprime (selbergPrimeProduct Q) x.1 /\
        Nat.Coprime (selbergPrimeProduct Q) x.2) := by
    intro x hx
    have hd := Finset.mem_filter.mp hx
    have hpCell := Finset.mem_filter.mp (Finset.mem_filter.mp hd.1).1
    have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hpCell.1).1
    have hlo : n*n < x.1*x.2 := hc.2.2.1
    have hhi : x.1*x.2 <= n*n+2*n := by
      have h := hc.2.2.2.1
      nlinarith
    apply Finset.mem_filter.mpr
    refine And.intro ?_ (canonical_owner_factors_coprime hn hd.1 (by omega))
    exact (mem_skewDivisorRows_iff (a := 1) (b := 1) (by decide) (by decide)).mpr
      (And.intro (one_dvd _) (And.intro (one_dvd _)
        (And.intro hd.2.1 (And.intro hd.2.2 (And.intro hlo hhi)))))
  have hcard : (((canonicalOwnerFamily Gamma n S).filter
      (fun x => M < 2*x.1 /\ x.1 <= M)).card : Real) <=
      (((skewDivisorRows n M 1 1).filter (fun x =>
        Nat.Coprime (selbergPrimeProduct Q) x.1 /\
        Nat.Coprime (selbergPrimeProduct Q) x.2)).card : Real) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (skew_sifted_pairs_le_tensor hn hM hQ ht hscale hbudget)

theorem prime_count_ge_canonical_skew_tensor
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) {n M Q t : Nat}
    (hn : 64^78 <= n) (hM : 0 < M) (hMn : 2*M <= n)
    (hQ : 1 <= Q) (ht : 2 <= t) (hQM : 2*Q <= M)
    (hscale : 2*(Q*Q)*t^15 <= M) (hbudget : 64*Q^4*n^2*t^14 <= M^3) :
    let C := canonicalOwnerFamily Gamma n fivePrimePrefix
    let L := C.filter (fun x => 2*x.1 <= n)
    (384/1001 : Real)*n-31-
      ((L.filter (fun x => Not (M < 2*x.1 /\ x.1 <= M))).card : Real)-
      skewTensorAllowance n M Q t-balancedTensorLogAllowance n <=
        ((squareIntervalPrimes n).card : Real) := by
  let C := canonicalOwnerFamily Gamma n fivePrimePrefix
  let L := C.filter (fun x => 2*x.1 <= n)
  let band : Prod Nat Nat -> Prop := fun x => M < 2*x.1 /\ x.1 <= M
  have h64 : (64 : Nat) <= 64^78 := Nat.le_self_pow (by decide) 64
  have hn2 : 2 <= n := by omega
  have heq : L.filter band = C.filter band := by
    ext x
    simp only [L, Finset.mem_filter]
    constructor
    next => exact fun h => And.intro h.1.1 h.2
    next =>
      intro h
      have hsize : x.1 <= M := h.2.2
      exact And.intro (And.intro h.1 (by omega)) h.2
  have hsum := Finset.card_filter_add_card_filter_not (s := L) band
  rw [heq] at hsum
  have hsumR : ((C.filter band).card : Real)+
      ((L.filter (fun x => Not (band x))).card : Real) = (L.card : Real) := by
    exact_mod_cast hsum
  have hband := canonical_skew_owner_card_le_tensor
    (Gamma := Gamma) (S := fivePrimePrefix) hn2 hM hQ ht hQM hscale hbudget
  change ((C.filter band).card : Real) <= skewTensorAllowance n M Q t at hband
  have hP := prime_count_ge_canonical_middle_tensor Gamma hn
  change (384/1001 : Real)*n-31-(L.card : Real)-balancedTensorLogAllowance n <=
    ((squareIntervalPrimes n).card : Real) at hP
  change (384/1001 : Real)*n-31-((L.filter (fun x => Not (band x))).card : Real)-
    skewTensorAllowance n M Q t-balancedTensorLogAllowance n <= _
  linarith only [hP, hsumR, hband]

end Nat.PrimeSieve
