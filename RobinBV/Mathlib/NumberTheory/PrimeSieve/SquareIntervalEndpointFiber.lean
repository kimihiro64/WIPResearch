/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalGapCells

/-!
# Separated quadratic rows in the modulus-six owner expansion

The exact odd-factor geometry supplies every admissible near-center row
above the cube cutoff and separates it from every other row in its unit
class. These facts retain the full cofactor-divisibility restriction.
They do not assert a distribution estimate, prime supply, or Legendre.
-/

set_option autoImplicit false

namespace Nat.PrimeSieve

/-- Integer quadratic comparison separating a near-center row from every later center. -/
theorem quadratic_row_left_separated_int {n h j p r : Int}
    (hn : 100 <= n) (hh : 1 <= h) (hj : h + 3 <= j)
    (hp : 6*n + 7*h <= 7*p) (hpn : p <= n) (hrn : r <= n)
    (hlo : n*n < p*(2*(n+h)-p))
    (hhi : r*(2*(n+j)-r) < (n+1)*(n+1)) : r + 6 < p := by
  by_contra hnot
  have hdiff : 0 <= r+6-p := by omega
  have hother : 0 <= 2*(n+j)-r-p+6 := by omega
  have hmono := mul_nonneg hdiff hother
  have hp6 : 0 <= p-6 := by omega
  have hjdiff : 0 <= j-h-3 := by omega
  have hcenter := mul_nonneg hp6 hjdiff
  nlinarith only [hn, hh, hp, hlo, hhi, hmono, hcenter]

/-- The complete near-center quadratic band lies below one seventh of the index. -/
theorem square_small_center_halfGap_bound {n h k : Nat}
    (hh : 100*h <= n) (hk : k*k < 2*n*h+h*h) : 7*k <= n := by
  have hmul := Nat.mul_le_mul_left n hh
  have hsq := Nat.mul_le_mul hh hh
  by_contra hnot
  have hge : n <= 7*k := by omega
  have hnksq := Nat.mul_le_mul hge hge
  nlinarith only [hmul, hsq, hk, hnksq]

/-- An actual near-center factor pair is separated from all rows at least three centers later. -/
theorem OddFactorGapCell.small_center_left_separated
    {n h j p t r u : Nat} (hn : 100 <= n) (hh : 100*h <= n)
    (hc : OddFactorGapCell n p t) (hd : OddFactorGapCell n r u)
    (hcenter : p+t = n+h) (jcenter : r+u = n+j) (hj : h+3 <= j) : r+6 < p := by
  have hhp : 1 <= h := by have := hc.center_gt; omega
  have ht : 7*t <= n := square_small_center_halfGap_bound hh
    (hc.halfGap_sq_lt (by omega))
  have hpn : p <= n :=
    (semiprime_straddles (show p <= p+2*t by omega) hc.interval_lower hc.interval_upper).1
  have hrn : r <= n :=
    (semiprime_straddles (show r <= r+2*u by omega) hd.interval_lower hd.interval_upper).1
  have hcint : (n:Int)*n < (p:Int)*(p+2*t) := by exact_mod_cast hc.interval_lower
  have hdint : (r:Int)*(r+2*u) < ((n:Int)+1)*(n+1) := by exact_mod_cast hd.interval_upper
  have hce : (p:Int)+t = n+h := by exact_mod_cast hcenter
  have jde : (r:Int)+u = n+j := by exact_mod_cast jcenter
  have hple : 6*n+7*h <= 7*p := by omega
  have hsep := quadratic_row_left_separated_int
    (n := (n:Int)) (h := (h:Int)) (j := (j:Int)) (p := (p:Int)) (r := (r:Int))
    (by exact_mod_cast hn) (by exact_mod_cast hhp) (by exact_mod_cast hj)
    (by exact_mod_cast hple) (by exact_mod_cast hpn) (by exact_mod_cast hrn)
    (by nlinarith only [hcint, hce]) (by nlinarith only [hdint, jde])
  exact_mod_cast hsep

/-- Six consecutive integer half-gaps fit inside each specified near-center row. -/
theorem square_small_center_six_consecutive {n h : Nat}
    (hn : 100 <= n) (hhpos : 1 <= h) (hh : 100*h <= n) :
    let K := Nat.sqrt (2*n*h+h*h-1)
    6 <= K /\ 7*K <= n /\
      2*n*(h-1)+h*h <= (K-5)*(K-5) := by
  dsimp only
  let K := Nat.sqrt (2*n*h+h*h-1)
  have hbase : 1 <= 2*n*h+h*h := by nlinarith
  have hsub := Nat.sub_add_cancel hbase
  have hsq : K*K <= 2*n*h+h*h-1 := Nat.sqrt_le _
  have hnear : 2*n*h+h*h-1 <= K*K+K+K := Nat.sqrt_le_add _
  have hK : 7*K <= n := square_small_center_halfGap_bound hh (by omega)
  have hK6 : 6 <= K := Nat.le_sqrt.mpr (by nlinarith)
  have hs : K-5+5 = K := Nat.sub_add_cancel (by omega)
  have hhsub : h-1+1 = h := Nat.sub_add_cancel hhpos
  refine And.intro hK6 (And.intro hK ?_)
  nlinarith only [hnear, hsub, hs, hhsub, hK]

/-- Every odd class modulo six occurs in each near-center odd-factor row. -/
theorem square_small_center_residue_cell {n h a : Nat}
    (hn : 100 <= n) (hhpos : 1 <= h) (hh : 100*h <= n)
    (ha : a < 6) (haodd : a%2 = 1) :
    exists p t : Nat, OddFactorGapCell n p t /\ p+t = n+h /\ p%6 = a := by
  let K := Nat.sqrt (2*n*h+h*h-1)
  have hdata := square_small_center_six_consecutive hn hhpos hh
  change 6 <= K /\ 7*K <= n /\ 2*n*(h-1)+h*h <= (K-5)*(K-5) at hdata
  let p0 := n+h-K
  let e := (a+6-p0%6)%6
  let p := p0+e
  let t := K-e
  have he : e < 6 := Nat.mod_lt _ (by decide)
  have hcenter : p+t = n+h := by dsimp [p,p0,t]; omega
  have hpmod : p%6 = a := by dsimp [p,e]; omega
  have hpodd : p%2 = 1 := by omega
  have htpos : 0 < t := by dsimp [t]; omega
  have htK : t <= K := Nat.sub_le _ _
  have htlow : K-5 <= t := by dsimp [t]; omega
  have htlow_sq := Nat.mul_le_mul htlow htlow
  have htK_sq := Nat.mul_le_mul htK htK
  have hsq : K*K <= 2*n*h+h*h-1 := Nat.sqrt_le _
  have hhsub : h-1+1 = h := Nat.sub_add_cancel hhpos
  have hbase : 1 <= 2*n*h+h*h := by nlinarith
  have hsub := Nat.sub_add_cancel hbase
  have hcenter_sq := congrArg (fun x : Nat => x*x) hcenter
  refine Exists.intro p (Exists.intro t (And.intro ?_ (And.intro hcenter hpmod)))
  refine { odd_left := hpodd, gap_pos := htpos, interval_lower := ?_, interval_upper := ?_ }
  next => nlinarith only [hcenter_sq, htK_sq, hsq, hsub]
  next => nlinarith only [hcenter_sq, htlow_sq, hdata.2.2, hhsub]

/-- The required large smaller factors lie strictly above the cube-root sieve cutoff. -/
theorem square_cube_root_lt_of_large_factor {n p : Nat}
    (hn : 100 <= n) (hp : 6*n <= 7*p) : Nat.nthRoot 3 (n*n+2*n) < p := by
  have hhalf : n <= 2*p := by omega
  have hp50 : 50 <= p := by omega
  have hsq := Nat.mul_le_mul hhalf hhalf
  have hcube := Nat.mul_le_mul_right (p*p) hp50
  apply (Nat.nthRoot_lt_iff (by decide : Not (3 = 0))).mpr
  nlinarith only [hn, hsq, hcube]

/-- The complete smaller-factor row with odd cofactor divisible by three and unit smaller factor. -/
noncomputable def squareThirdCofactorRow (n h : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc 1 n).filter (fun p =>
    Nat.nthRoot 3 (n*n+2*n) < p /\ Not (p%3 = 0) /\
    OddFactorGapCell n p (n+h-p) /\ (p+2*(n+h-p))%3 = 0)

/-- Explicit membership retains the cube cutoff, unit class, and cofactor divisibility. -/
theorem mem_squareThirdCofactorRow (n h p : Nat) :
    Membership.mem (squareThirdCofactorRow n h) p <->
      (1 <= p /\ p <= n) /\ Nat.nthRoot 3 (n*n+2*n) < p /\ Not (p%3 = 0) /\
        OddFactorGapCell n p (n+h-p) /\ (p+2*(n+h-p))%3 = 0 := by
  simp only [squareThirdCofactorRow, Finset.mem_filter, Finset.mem_Icc]

/-- Every admissible near-center divisor-three row is nonempty above the cube cutoff. -/
theorem squareThirdCofactorRow_nonempty {n h : Nat}
    (hn : 100 <= n) (hhpos : 1 <= h) (hh : 100*h <= n)
    (hunit : Not ((n+h)%3 = 0)) : (squareThirdCofactorRow n h).Nonempty := by
  let a := if (n+h)%3 = 1 then 5 else 1
  have ha : a < 6 := by dsimp [a]; split_ifs <;> omega
  have haodd : a%2 = 1 := by dsimp [a]; split_ifs <;> omega
  choose p t hp using square_small_center_residue_cell hn hhpos hh ha haodd
  have hcell := hp.1
  have hcenter := hp.2.1
  have hpmod := hp.2.2
  have hpn : p <= n :=
    (semiprime_straddles (show p <= p+2*t by omega) hcell.interval_lower hcell.interval_upper).1
  have hp1 : 1 <= p := by have := hcell.odd_left; omega
  have ht : n+h-p = t := by omega
  have htbound : 7*t <= n := square_small_center_halfGap_bound hh
    (hcell.halfGap_sq_lt (by omega))
  have hcube := square_cube_root_lt_of_large_factor hn (show 6*n <= 7*p by omega)
  have hclass : Not (p%3 = 0) /\ (p+2*t)%3 = 0 := by
    dsimp [a] at hpmod
    split_ifs at hpmod <;> omega
  refine Exists.intro p ((mem_squareThirdCofactorRow n h p).mpr ?_)
  rw [ht]
  exact And.intro (And.intro hp1 hpn)
    (And.intro hcube (And.intro hclass.1 (And.intro hcell hclass.2)))

/-- Equal unit classes force the row centers to agree modulo three. -/
theorem squareThirdCofactorRow_center_congruence {n h j p r : Nat}
    (hp : Membership.mem (squareThirdCofactorRow n h) p)
    (hr : Membership.mem (squareThirdCofactorRow n j) r) (heq : p%6 = r%6) : h%3 = j%3 := by
  have hpd := (mem_squareThirdCofactorRow n h p).mp hp
  have hrd := (mem_squareThirdCofactorRow n j r).mp hr
  omega

/-- All points of a divisor-three odd-factor row have the same class modulo six. -/
theorem squareThirdCofactorRow_mod_six {n h p r : Nat}
    (hp : Membership.mem (squareThirdCofactorRow n h) p)
    (hr : Membership.mem (squareThirdCofactorRow n h) r) : p%6 = r%6 := by
  have hpd := (mem_squareThirdCofactorRow n h p).mp hp
  have hrd := (mem_squareThirdCofactorRow n h r).mp hr
  have hpo := hpd.2.2.2.1.odd_left
  have hro := hrd.2.2.2.1.odd_left
  omega

/-- A near-center row stays more than six from every distinct row in its own class. -/
theorem squareThirdCofactorRow_separated {n h j p r : Nat}
    (hn : 100 <= n) (hh : 100*h <= n)
    (hp : Membership.mem (squareThirdCofactorRow n h) p)
    (hr : Membership.mem (squareThirdCofactorRow n j) r)
    (heq : p%6 = r%6) (hne : Not (h = j)) : p+6 < r \/ r+6 < p := by
  have hc := squareThirdCofactorRow_center_congruence hp hr heq
  have hpd := (mem_squareThirdCofactorRow n h p).mp hp
  have hrd := (mem_squareThirdCofactorRow n j r).mp hr
  have hpc : p+(n+h-p) = n+h := by omega
  have hrc : r+(n+j-r) = n+j := by omega
  by_cases hj : h < j
  next =>
    exact Or.inr (hpd.2.2.2.1.small_center_left_separated hn hh hrd.2.2.2.1 hpc hrc (by omega))
  next =>
    have hjh : j+3 <= h := by omega
    have hjbound : 100*j <= n := by omega
    exact Or.inl (hrd.2.2.2.1.small_center_left_separated hn hjbound hpd.2.2.2.1 hrc hpc hjh)

end Nat.PrimeSieve
