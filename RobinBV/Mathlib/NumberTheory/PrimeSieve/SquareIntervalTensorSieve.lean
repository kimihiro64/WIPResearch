/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalDivisorAllPhase
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalGeometricSupply
import RobinBV.Mathlib.NumberTheory.SelbergSieve.Tensor

/-!
# A two-factor sieve for balanced square-interval owners

Both factors of actual screened owner cells in n/2 < p <= n are sieved.
The exact divisor-matrix main term and every error are retained. The actual
prime-count consumer keeps the entire middle joint allowance G_low-K.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

theorem tensorDivisorCount_balanced {n a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    tensorDivisorCount (balancedDivisorRows n 1 1) a b =
      (balancedDivisorRows n a b).card := by
  unfold tensorDivisorCount
  congr 1
  ext x
  have h11 := mem_balancedDivisorRows_iff (n := n) (a := 1) (b := 1)
    (p := x.1) (q := x.2) (by decide) (by decide)
  simp only [one_dvd, true_and] at h11
  rw [Finset.mem_filter, h11, mem_balancedDivisorRows_iff ha hb]
  constructor
  next => exact fun h => And.intro h.2.1 (And.intro h.2.2 h.1)
  next => exact fun h => And.intro h.2.2 (And.intro h.1 h.2.1)

set_option maxHeartbeats 400000 in
theorem balanced_divisor_row_uniform_error {n Q t a b : Nat}
    (hn : 2 <= n) (ht : 2 <= t) (ha : 0 < a) (hb : 0 < b)
    (haQ : a <= Q*Q) (hbQ : b <= Q*Q)
    (hscale : 2*(Q*Q)*t^15 <= n) (hbudget : 64*Q^4*t^14 <= n) :
    abs (((balancedDivisorRows n a b).card : Real)-
      (2*(n : Real)*Real.log 2)/((a : Real)*b)) <=
        40*(n : Real)/t+4+20*((t : Real)^2-1)*(Q : Real)^2 := by
  have ha2 : a^2 <= Q^4 := by
    have h := Nat.mul_le_mul haQ haQ
    nlinarith only [h]
  have hscaleA : 2*a*t^15 <= n := by
    have h := Nat.mul_le_mul_right (2*t^15) haQ
    nlinarith only [h, hscale]
  have hbudgetA : 64*a^2*t^14 <= n := by
    have h := Nat.mul_le_mul_right (64*t^14) ha2
    nlinarith only [h, hbudget]
  have hraw := balancedDivisorRows_abs_error_all_moduli hn ha hb ht hscaleA hbudgetA
  have he : (2*(n : Real)/((a : Real)*b))*Real.log 2 =
      (2*(n : Real)*Real.log 2)/((a : Real)*b) := by ring
  rw [he] at hraw
  have haR : (1 : Real) <= a := by exact_mod_cast (show 1 <= a by omega)
  have hbR : (1 : Real) <= b := by exact_mod_cast (show 1 <= b by omega)
  have htR : (2 : Real) <= t := by exact_mod_cast ht
  have ht0 : (0 : Real) < t := by linarith
  have hbQR : (b : Real) <= (Q : Real)^2 := by
    rw [pow_two]
    exact_mod_cast hbQ
  have hmain : 40*(n : Real)/((a : Real)*t) <= 40*(n : Real)/t := by
    apply _root_.div_le_div_of_nonneg_left (by positivity) ht0
    nlinarith
  have hunit : (4 : Real)/b <= 4 := by
    have h := _root_.div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 4)
      (by norm_num : (0 : Real) < 1) hbR
    simpa only [div_one] using h
  have hratio : (b : Real)/a <= (Q : Real)^2 := by
    have h := _root_.div_le_div_of_nonneg_left (Nat.cast_nonneg b)
      (by norm_num : (0 : Real) < 1) haR
    have h' : (b : Real)/a <= b := by simpa only [div_one] using h
    exact h'.trans hbQR
  have hc : 0 <= 20*((t : Real)^2-1) := by nlinarith
  have hcost : 20*((t : Real)^2-1)*(b : Real)/a <=
      20*((t : Real)^2-1)*(Q : Real)^2 := by
    calc
      _ = (20*((t : Real)^2-1))*((b : Real)/a) := by ring
      _ <= _ := _root_.mul_le_mul_of_nonneg_left hratio hc
  exact hraw.trans (_root_.add_le_add (_root_.add_le_add hmain hunit) hcost)

noncomputable def balancedTensorAllowance (n Q t : Nat) : Real :=
  (2*(n : Real)*Real.log 2)/(Real.log ((Q : Real)+1))^2+
    (40*(n : Real)/t+4+20*((t : Real)^2-1)*(Q : Real)^2)*(Q : Real)^4

theorem balanced_sifted_pairs_le_tensor {n Q t : Nat}
    (hn : 2 <= n) (hQ : 1 <= Q) (ht : 2 <= t)
    (hscale : 2*(Q*Q)*t^15 <= n) (hbudget : 64*Q^4*t^14 <= n) :
    (((balancedDivisorRows n 1 1).filter (fun x =>
      Nat.Coprime (selbergPrimeProduct Q) x.1 /\
      Nat.Coprime (selbergPrimeProduct Q) x.2)).card : Real) <=
        balancedTensorAllowance n Q t := by
  have hc : (0 : Real) <= (t : Real)^2-1 := by
    have htr : (2 : Real) <= t := by exact_mod_cast ht
    nlinarith
  apply Nat.tensor_sifted_card_le_log_sieve _ hQ
    (2*(n : Real)*Real.log 2)
    (40*(n : Real)/t+4+20*((t : Real)^2-1)*(Q : Real)^2)
    (by positivity) (by positivity)
  intro a ha haQ b hb hbQ
  rw [tensorDivisorCount_balanced ha hb]
  exact balanced_divisor_row_uniform_error hn ht ha hb haQ hbQ hscale hbudget

theorem screened_balanced_owner_card_le_tensor
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T Q t : Nat} {S R : Finset Nat}
    (hn : 9 <= n) (hQ : 1 <= Q) (ht : 2 <= t) (hQn : 2*Q <= n)
    (hscale : 2*(Q*Q)*t^15 <= n) (hbudget : 64*Q^4*t^14 <= n)
    (hR : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= 2*n+1 ->
      Membership.mem R ell) :
    (((ownerLineFamilyHighFactorCells Gamma n T S R).filter
      (fun x => n < 2*x.1)).card : Real) <= balancedTensorAllowance n Q t := by
  have hcop : forall r, Nat.Prime r -> Q < r -> Nat.Coprime (selbergPrimeProduct Q) r := by
    intro r hr hQr
    apply Nat.coprime_of_dvd
    intro p hp hpP hpr
    have hpQ := (prime_dvd_selbergPrimeProduct_iff hp).mp hpP
    have he := (hr.eq_one_or_self_of_dvd p hpr).resolve_left hp.ne_one
    omega
  have hsub : (ownerLineFamilyHighFactorCells Gamma n T S R).filter
      (fun x => n < 2*x.1) <=
      (balancedDivisorRows n 1 1).filter (fun x =>
        Nat.Coprime (selbergPrimeProduct Q) x.1 /\
        Nat.Coprime (selbergPrimeProduct Q) x.2) := by
    intro x hx
    have hd := Finset.mem_filter.mp hx
    have hpCell := Finset.mem_filter.mp (Finset.mem_filter.mp hd.1).1
    have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hpCell.1).1
    have hpn : x.1 <= n := by
      have h := Finset.mem_range.mp (Finset.mem_product.mp hc.1).1
      omega
    have hqprime := screened_balanced_owner_cofactor_prime hn hR hd.1 hd.2
    have hlo : n*n < x.1*x.2 := hc.2.2.1
    have hhi : x.1*x.2 <= n*n+2*n := by
      have h := hc.2.2.2.1
      nlinarith
    have hqn : n < x.2 := by
      by_contra h
      have hm := Nat.mul_le_mul hpn (show x.2 <= n by omega)
      omega
    apply Finset.mem_filter.mpr
    refine And.intro ?_ (And.intro (hcop x.1 hpCell.2 (by omega))
      (hcop x.2 hqprime (by omega)))
    exact (mem_balancedDivisorRows_iff (a := 1) (b := 1) (by decide) (by decide)).mpr
      (And.intro (one_dvd _) (And.intro (one_dvd _)
        (And.intro hd.2 (And.intro hpn (And.intro hlo hhi)))))
  have hc : (((ownerLineFamilyHighFactorCells Gamma n T S R).filter
      (fun x => n < 2*x.1)).card : Real) <=
      (((balancedDivisorRows n 1 1).filter (fun x =>
        Nat.Coprime (selbergPrimeProduct Q) x.1 /\
        Nat.Coprime (selbergPrimeProduct Q) x.2)).card : Real) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (balanced_sifted_pairs_le_tensor (by omega) hQ ht hscale hbudget)

theorem prime_count_ge_tensor_geometric_allowance
    (Gamma : Nat -> Nat -> Finset (Prod Nat Nat)) {n Q t : Nat}
    (hn : 9 <= n) (hQ : 1 <= Q) (ht : 2 <= t) (hQn : 2*Q <= n)
    (hscale : 2*(Q*Q)*t^15 <= n) (hbudget : 64*Q^4*t^14 <= n) :
    let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix (balancedOwnerScreen n)
    (384/1001 : Real)*n-31-((G.filter (fun x => 2*x.1 <= n)).card : Real)-
      balancedTensorAllowance n Q t+lineCollisionCredit G <=
        ((squareIntervalPrimes n).card : Real) := by
  let R := balancedOwnerScreen n
  let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R
  let low := G.filter (fun x => 2*x.1 <= n)
  let high := G.filter (fun x => n < 2*x.1)
  have hR : forall ell, Membership.mem R ell -> 2 <= ell := by
    intro ell he
    exact (Finset.mem_filter.mp he).2.1.two_le
  have hcomplete : forall ell, Nat.Prime ell -> ell%2 = 1 ->
      ell*ell <= 2*n+1 -> Membership.mem R ell :=
    fun ell hp ho hs => balancedOwnerScreen_complete hp ho hs
  have hcut : forall ell, Nat.Prime ell -> ell%2 = 1 ->
      ell*ell <= n -> Membership.mem R ell :=
    fun ell hp ho hs => hcomplete ell hp ho (by omega)
  have hcomp := actual_composites_le_exactPrefixAllowance (Gamma := Gamma)
    (by omega : 2 <= n) hR hcut
  dsimp only at hcomp
  change 2*(n : Real)-((squareIntervalPrimes n).card : Real) <=
    2*(n : Real)-((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+
      (G.card : Real)-lineCollisionCredit G at hcomp
  have hsplit : high.card+low.card = G.card := by
    have h := Finset.card_filter_add_card_filter_not (s := G) (fun x => n < 2*x.1)
    have he : G.filter (fun x => Not (n < 2*x.1)) = low := by
      change G.filter (fun x => Not (n < 2*x.1)) = G.filter (fun x => 2*x.1 <= n)
      simp only [not_lt]
    rw [he] at h
    exact h
  have hsplitR : (high.card : Real)+(low.card : Real) = (G.card : Real) := by
    exact_mod_cast hsplit
  have hhigh : (high.card : Real) <= balancedTensorAllowance n Q t :=
    screened_balanced_owner_card_le_tensor hn hQ ht hQn hscale hbudget hcomplete
  have hF := five_prime_prefix_card_lower n
  change (384/1001 : Real)*n-31-(low.card : Real)-
    balancedTensorAllowance n Q t+lineCollisionCredit G <= _
  linarith only [hcomp, hsplitR, hhigh, hF]

end Nat.PrimeSieve
