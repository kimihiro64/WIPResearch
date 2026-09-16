/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalPrimeLogBound
import RobinBV.Mathlib.NumberTheory.SelbergSieve.LogReserve

/-!
# A complete square-interval bound with logarithmic reserve

The positive denominator reserve is carried through rough survivors, G-K,
the full composite allowance and the actual prime count. The exact gain is
strictly positive for every n >= 4, but the resulting lower envelope remains
negative; the leading n/log(n) coefficient is unchanged.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat.PrimeSieve

noncomputable def roughLogReserveAllowance (n : Nat) : Real :=
  8*(n : Real)/(Real.squareSieveDenominator n+2*(1-Real.log 2))+
    2*(n : Real)/(Real.log n)^2

theorem card_squareRoughSurvivors_le_explicit_reserve {n : Nat} (hn : 4 <= n) :
    ((squareRoughSurvivors n).card : Real) <=
      4*(n : Real)/(Real.squareSieveDenominator n+2*(1-Real.log 2))+
        (n : Real)/(Real.log n)^2 := by
  have hn4 : (4 : Real) <= n := by exact_mod_cast hn
  have hn1 : (1 : Real) < n := by linarith
  let Q := Real.squareSieveCutoff (n : Real)
  have hQ1 : 1 <= Q := Real.one_le_squareSieveCutoff hn1
  have hQsq := Real.squareSieveCutoff_sq_le_self hn4
  have hQ : Q*Q <= n := by
    have hQr : (Q : Real)*(Q : Real) <= n := by simpa only [pow_two] using hQsq
    exact_mod_cast hQr
  have hc : ((squareRoughSurvivors n).card : Real) <=
      (((Finset.Ioc (n*n) (n*n+2*n)).filter
        (fun m => Nat.Coprime (Nat.selbergPrimeProduct Q) m)).card : Real) := by
    exact_mod_cast Finset.card_le_card (squareRoughSurvivors_subset_sifted_interval hQ)
  have hs := Nat.card_sifted_interval_le_log_reserve
    (L := n*n) (U := n*n+2*n) (by omega) hQ1
  push_cast at hs
  have he : (n : Real)*n+2*n-n*n = 2*n := by ring
  rw [he] at hs
  have hD := Real.squareSieveDenominator_pos hn1
  have hdelta := Nat.selberg_log_reserve_pos
  have hlog := Real.squareSieveCutoff_log_lower hn1
  have hsmall : 0 < Real.squareSieveDenominator n/2+(1-Real.log 2) := by
    linarith only [hD, hdelta]
  have hlarge : 0 < Real.squareSieveDenominator n+2*(1-Real.log 2) := by
    linarith only [hD, hdelta]
  have hmain : 2*(n : Real)/(Real.log ((Q : Real)+1)+(1-Real.log 2)) <=
      2*(n : Real)/(Real.squareSieveDenominator n/2+(1-Real.log 2)) :=
    _root_.div_le_div_of_nonneg_left (by positivity) hsmall (by linarith only [hlog])
  have herr := Real.squareSieveCutoff_sq_bound hn1
  have heq : 2*(n : Real)/(Real.squareSieveDenominator n/2+(1-Real.log 2)) =
      4*(n : Real)/(Real.squareSieveDenominator n+2*(1-Real.log 2)) := by
    field_simp [ne_of_gt hsmall, ne_of_gt hlarge]
    <;> ring
  rw [heq] at hmain
  exact hc.trans (hs.trans (_root_.add_le_add hmain herr))

theorem line_family_card_le_prefix_add_reserve
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {R : Finset Nat}
    (hn : 4 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    ((ownerLineFamilyHighFactorCells Gamma n T fivePrimePrefix R).card : Real) <=
      ((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+roughLogReserveAllowance n := by
  have hg := line_family_card_le_prefix_add_two_rough (Gamma := Gamma) (T := T)
    (by omega : 2 <= n) (fun ell he => fivePrimePrefix_prime he) hcut
  have hgr : ((ownerLineFamilyHighFactorCells Gamma n T fivePrimePrefix R).card : Real) <=
      ((oddSievedOwnerInSquare n 1 fivePrimePrefix).card : Real)+
        2*((squareRoughSurvivors n).card : Real) := by exact_mod_cast hg
  have hs := card_squareRoughSurvivors_le_explicit_reserve hn
  have hdouble := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : Real) <= 2)
  have he : 2*(4*(n : Real)/(Real.squareSieveDenominator n+2*(1-Real.log 2))+
      (n : Real)/(Real.log n)^2) =
      8*(n : Real)/(Real.squareSieveDenominator n+2*(1-Real.log 2))+
        2*(n : Real)/(Real.log n)^2 := by ring
  rw [he] at hdouble
  unfold roughLogReserveAllowance
  linarith only [hgr, hdouble]

theorem line_family_signed_allowance_le_reserve
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {R : Finset Nat}
    (hn : 4 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    let G := ownerLineFamilyHighFactorCells Gamma n T fivePrimePrefix R
    (G.card : Real)-lineCollisionCredit G <=
      (384/1001 : Real)*n+roughLogReserveAllowance n+31-lineCollisionCredit G := by
  have hG := line_family_card_le_prefix_add_reserve (Gamma := Gamma) (T := T) hn hcut
  have hF := five_prime_prefix_card_upper n
  dsimp only
  linarith only [hG, hF]

theorem exactPrefixCompositeAllowance_le_reserve
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n T : Nat} {R : Finset Nat}
    (hn : 4 <= n)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    let G := ownerLineFamilyHighFactorCells Gamma n T fivePrimePrefix R
    exactPrefixCompositeAllowance n G <=
      2*(n : Real)+roughLogReserveAllowance n-lineCollisionCredit G := by
  have hg := line_family_card_le_prefix_add_reserve (Gamma := Gamma) (T := T) hn hcut
  dsimp only
  unfold exactPrefixCompositeAllowance
  linarith only [hg]

theorem prime_count_ge_collision_sub_reserve
    {Gamma : Nat -> Nat -> Finset (Prod Nat Nat)} {n : Nat} {R : Finset Nat}
    (hn : 4 <= n)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell) :
    let G := ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R
    lineCollisionCredit G-roughLogReserveAllowance n <= ((squareIntervalPrimes n).card : Real) := by
  have hcomp := actual_composites_le_exactPrefixAllowance (Gamma := Gamma)
    (by omega : 2 <= n) hR hcut
  have hbound := exactPrefixCompositeAllowance_le_reserve (Gamma := Gamma) (T := 0) hn hcut
  dsimp only at hcomp hbound
  dsimp only
  linarith only [hcomp, hbound]

theorem prime_count_ge_explicit_log_reserve {n : Nat} (hn : 4 <= n) :
    -8*(n : Real)/(Real.log n-2*Real.log (Real.log n)+2*(1-Real.log 2))-
      2*(n : Real)/(Real.log n)^2 <= ((squareIntervalPrimes n).card : Real) := by
  let R := (Finset.range (n+1)).filter Nat.Prime
  let Gamma : Nat -> Nat -> Finset (Prod Nat Nat) := fun _ _ => Finset.empty
  have hR : forall ell, Membership.mem R ell -> 2 <= ell := by
    intro ell he
    exact (Finset.mem_filter.mp he).2.two_le
  have hcut : forall ell, Nat.Prime ell -> ell%2 = 1 -> ell*ell <= n -> Membership.mem R ell := by
    intro ell hp _ hs
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_range.mpr ?_) hp
    have hp2 := hp.two_le
    nlinarith
  have hp := prime_count_ge_collision_sub_reserve (Gamma := Gamma) hn hR hcut
  have hcredit := lineCollisionCredit_nonneg
    (ownerLineFamilyHighFactorCells Gamma n 0 fivePrimePrefix R)
  dsimp only at hp
  unfold roughLogReserveAllowance Real.squareSieveDenominator at hp
  have he : -8*(n : Real)/(Real.log n-2*Real.log (Real.log n)+2*(1-Real.log 2)) =
      -(8*(n : Real)/(Real.log n-2*Real.log (Real.log n)+2*(1-Real.log 2))) := by ring
  rw [he]
  linarith only [hp, hcredit]

theorem roughLogAllowance_sub_reserve {n : Nat} (hn : 4 <= n) :
    roughLogAllowance n-roughLogReserveAllowance n =
      16*(1-Real.log 2)*(n : Real)/
        (Real.squareSieveDenominator n*(Real.squareSieveDenominator n+2*(1-Real.log 2))) := by
  have hn1 : (1 : Real) < n := by exact_mod_cast (show 1 < n by omega)
  have hD := Real.squareSieveDenominator_pos hn1
  have hdelta := Nat.selberg_log_reserve_pos
  have hshift : 0 < Real.squareSieveDenominator n+2*(1-Real.log 2) := by
    linarith only [hD, hdelta]
  have hlog := Real.log_pos hn1
  unfold roughLogAllowance roughLogReserveAllowance
  field_simp [ne_of_gt hD, ne_of_gt hshift, ne_of_gt hlog]
  <;> ring

theorem roughLogReserveAllowance_lt_original {n : Nat} (hn : 4 <= n) :
    roughLogReserveAllowance n < roughLogAllowance n := by
  have hn1 : (1 : Real) < n := by exact_mod_cast (show 1 < n by omega)
  have hD := Real.squareSieveDenominator_pos hn1
  have hdelta := Nat.selberg_log_reserve_pos
  have hshift : 0 < Real.squareSieveDenominator n+2*(1-Real.log 2) := by
    linarith only [hD, hdelta]
  have hnum : 0 < 16*(1-Real.log 2)*(n : Real) := by positivity
  have hgain := _root_.div_pos hnum (mul_pos hD hshift)
  have he := roughLogAllowance_sub_reserve hn
  linarith only [he, hgain]

theorem roughLogReserveAllowance_pos {n : Nat} (hn : 4 <= n) :
    0 < roughLogReserveAllowance n := by
  have hn1 : (1 : Real) < n := by exact_mod_cast (show 1 < n by omega)
  have hD := Real.squareSieveDenominator_pos hn1
  have hdelta := Nat.selberg_log_reserve_pos
  have hshift : 0 < Real.squareSieveDenominator n+2*(1-Real.log 2) := by
    linarith only [hD, hdelta]
  have hmain : 0 < 8*(n : Real)/(Real.squareSieveDenominator n+2*(1-Real.log 2)) :=
    _root_.div_pos (by positivity) hshift
  have herr : 0 <= 2*(n : Real)/(Real.log n)^2 := by positivity
  unfold roughLogReserveAllowance
  linarith only [hmain, herr]

end Nat.PrimeSieve
