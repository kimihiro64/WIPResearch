/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import PrimeNumberTheoremAnd.IEANTN.RosserSchoenfeld.RosserSchoenfeldPrime
import RobinBV.Sieve.Proof.LinnikDensePrimeBand

/-!
# Degree-uniform dense prime bands for Linnik's recurrence

This module derives one absolute dyadic prime-band threshold from the audited
Rosser--Schoenfeld theta error. It proves a polynomial threshold uniform over
the requested band cardinality, selects the exact positive prime moduli, and
feeds that exact set through the complete Vinogradov mean-value recurrence.
The resulting root-scale threshold is polynomial relative to the degree, while
every modulus is at most twice the integer root scale.
-/

open Filter

theorem theta_gap_half_of_pnt_error
    (C y : Real)
    (hpnt : forall x : Real, 2 <= x ->
      abs (Chebyshev.theta x - x) <= C * x / Real.log x ^ 2)
    (hy : 2 <= y)
    (hlogY : 6 * C <= Real.log y ^ 2)
    (hlogTwoY : 6 * C <= Real.log (2 * y) ^ 2) :
    y / 2 <= Chebyshev.theta (2 * y) - Chebyshev.theta y := by
  have hyPos : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have htwoY : 2 <= 2 * y := by linarith
  have hlogYPos : 0 < Real.log y := Real.log_pos (lt_of_lt_of_le (by norm_num) hy)
  have hlogTwoYPos : 0 < Real.log (2 * y) :=
    Real.log_pos (by nlinarith)
  have hdenY : 0 < Real.log y ^ 2 := sq_pos_of_pos hlogYPos
  have hdenTwoY : 0 < Real.log (2 * y) ^ 2 := sq_pos_of_pos hlogTwoYPos
  have herrY : C * y / Real.log y ^ 2 <= y / 6 := by
    have hCdiv : C <= Real.log y ^ 2 / 6 := by linarith
    have hnum := mul_le_mul_of_nonneg_right hCdiv (le_of_lt hyPos)
    calc
      C * y / Real.log y ^ 2 <=
          (Real.log y ^ 2 / 6) * y / Real.log y ^ 2 :=
        div_le_div_of_nonneg_right hnum (le_of_lt hdenY)
      _ = y / 6 := by field_simp
  have herrTwoY : C * (2 * y) / Real.log (2 * y) ^ 2 <= y / 3 := by
    have hCdiv : C <= Real.log (2 * y) ^ 2 / 6 := by linarith
    have hnum := mul_le_mul_of_nonneg_right hCdiv (by positivity : 0 <= 2 * y)
    calc
      C * (2 * y) / Real.log (2 * y) ^ 2 <=
          (Real.log (2 * y) ^ 2 / 6) * (2 * y) / Real.log (2 * y) ^ 2 :=
        div_le_div_of_nonneg_right hnum (le_of_lt hdenTwoY)
      _ = y / 3 := by
        field_simp
        ring
  have hpntY := hpnt y hy
  have hpntTwoY := hpnt (2 * y) htwoY
  have hthetaYUpper : Chebyshev.theta y - y <= y / 6 :=
    le_trans (le_abs_self _) (le_trans hpntY herrY)
  have hthetaTwoYLower : -(y / 3) <= Chebyshev.theta (2 * y) - 2 * y :=
    le_trans (neg_le_neg herrTwoY)
      (le_trans (neg_le_neg hpntTwoY) (neg_abs_le _))
  linarith

theorem eventually_theta_gap_half :
    Filter.Eventually
      (fun y : Nat =>
        (y : Real) / 2 <= Chebyshev.theta (2 * (y : Real)) -
          Chebyshev.theta (y : Real))
      atTop := by
  choose C _hC hpnt using RS_prime.pnt
  have hlogLim : Tendsto (fun y : Nat => Real.log (y : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun y : Nat => (y : Real)) atTop atTop)
  have hlarge := hlogLim.eventually (eventually_ge_atTop (max 1 (6 * C)))
  filter_upwards [hlarge, eventually_ge_atTop 2] with y hlog hy
  apply theta_gap_half_of_pnt_error C (y : Real) hpnt
  next => exact_mod_cast hy
  next =>
    have hOne : 1 <= Real.log (y : Real) := le_trans (le_max_left _ _) hlog
    have hCLog : 6 * C <= Real.log (y : Real) :=
      le_trans (le_max_right _ _) hlog
    nlinarith
  next =>
    have hyPos : 0 < (y : Real) := by exact_mod_cast (lt_of_lt_of_le (by omega) hy)
    have htwoYPos : 0 < 2 * (y : Real) := by positivity
    have hlogMono : Real.log (y : Real) <= Real.log (2 * (y : Real)) :=
      Real.strictMonoOn_log.monotoneOn
        (show Membership.mem (Set.Ioi 0) (y : Real) from hyPos)
        (show Membership.mem (Set.Ioi 0) (2 * (y : Real)) from htwoYPos) (by nlinarith)
    have hOne : 1 <= Real.log (2 * (y : Real)) :=
      le_trans (le_trans (le_max_left _ _) hlog) hlogMono
    have hCLog : 6 * C <= Real.log (2 * (y : Real)) :=
      le_trans (le_trans (le_max_right _ _) hlog) hlogMono
    nlinarith

theorem theta_nat_eq_sum_primesLE (n : Nat) :
    Chebyshev.theta (n : Real) =
      (Nat.primesLE n).sum (fun p => Real.log (p : Real)) := by
  rw [Chebyshev.theta_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
  simp

theorem theta_gap_le_primeBand_card_mul_log (y : Nat) (hy : 2 <= y) :
    Chebyshev.theta (2 * (y : Real)) - Chebyshev.theta (y : Real) <=
      (((Nat.primesLE (2 * y)).filter (fun p => y < p)).card : Real) *
        Real.log (2 * y : Nat) := by
  let s := (Nat.primesLE (2 * y)).filter (fun p => y < p)
  have hsmall : Nat.primesLE y <= Nat.primesLE (2 * y) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    rw [Nat.mem_primesLE]
    exact And.intro (by omega) hp.2
  have hsEq : s = Nat.primesLE (2 * y) \ Nat.primesLE y := by
    ext p
    simp only [s, Finset.mem_filter, Nat.mem_primesLE, Finset.mem_sdiff]
    constructor
    next =>
      intro hp
      apply And.intro (And.left hp)
      intro hpSmall
      exact (not_le_of_gt (And.right hp)) (And.left hpSmall)
    next =>
      intro hp
      apply And.intro (And.left hp)
      apply lt_of_not_ge
      intro hle
      exact (And.right hp) (And.intro hle (And.right (And.left hp)))
  have hsumEq : s.sum (fun p => Real.log (p : Real)) +
      (Nat.primesLE y).sum (fun p => Real.log (p : Real)) =
        (Nat.primesLE (2 * y)).sum (fun p => Real.log (p : Real)) := by
    rw [hsEq]
    exact Finset.sum_sdiff hsmall
  have hsumLe : s.sum (fun p => Real.log (p : Real)) <=
      (s.card : Real) * Real.log (2 * y : Nat) := by
    have h := Finset.sum_le_card_nsmul s (fun p => Real.log (p : Real))
      (Real.log (2 * y : Nat)) (by
        intro p hp
        have hpMem := Finset.mem_filter.mp hp
        have hpPrime : p.Prime := (Nat.mem_primesLE.mp hpMem.1).2
        have hpLe : p <= 2 * y := (Nat.mem_primesLE.mp hpMem.1).1
        have hpPos : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
        have htwoYPos : 0 < (2 * y : Nat) := by omega
        exact Real.strictMonoOn_log.monotoneOn
          (show Membership.mem (Set.Ioi 0) (p : Real) from hpPos)
          (show Membership.mem (Set.Ioi 0) ((2 * y : Nat) : Real) by
            change 0 < ((2 * y : Nat) : Real)
            exact_mod_cast htwoYPos)
          (by exact_mod_cast hpLe))
    simpa [nsmul_eq_mul] using h
  rw [show (2 : Real) * (y : Real) = ((2 * y : Nat) : Real) by norm_num]
  rw [theta_nat_eq_sum_primesLE, theta_nat_eq_sum_primesLE]
  change _ <= (s.card : Real) * Real.log (2 * y : Nat)
  linarith

theorem primeBand_card_gt_of_theta_gap (M y : Nat) (hy : 2 <= y)
    (hgap : (y : Real) / 2 <=
      Chebyshev.theta (2 * (y : Real)) - Chebyshev.theta (y : Real))
    (hsize : 2 * ((M + 1 : Nat) : Real) * Real.log (2 * y : Nat) <= y) :
    M < ((Nat.primesLE (2 * y)).filter (fun p => y < p)).card := by
  let s := (Nat.primesLE (2 * y)).filter (fun p => y < p)
  have hgapUpper := theta_gap_le_primeBand_card_mul_log y hy
  have hlogPos : 0 < Real.log (2 * y : Nat) := by
    apply Real.log_pos
    norm_cast
    omega
  by_contra hnot
  have hcard : s.card <= M := Nat.le_of_not_gt hnot
  have hcardReal : (s.card : Real) <= M := by exact_mod_cast hcard
  change _ <= (s.card : Real) * Real.log (2 * y : Nat) at hgapUpper
  have hstrict : (s.card : Real) * Real.log (2 * y : Nat) <
      ((M + 1 : Nat) : Real) * Real.log (2 * y : Nat) := by
    have hcast : (s.card : Real) < (M + 1 : Nat) := by
      exact_mod_cast (Nat.lt_succ_of_le hcard)
    exact mul_lt_mul_of_pos_right hcast hlogPos
  nlinarith

theorem primeBand_size_condition_of_square (M y : Nat)
    (hy : 32 * (M + 1) ^ 2 <= y) :
    2 * ((M + 1 : Nat) : Real) * Real.log (2 * y : Nat) <= y := by
  have hyReal : 32 * (((M + 1 : Nat) : Real) ^ 2) <= (y : Real) := by
    exact_mod_cast hy
  have hyNonneg : 0 <= (y : Real) := by positivity
  have hxNonneg : 0 <= 2 * (y : Real) := by positivity
  have hlog := Real.log_le_rpow_div hxNonneg
    (show (0 : Real) < 1 / 2 by norm_num)
  rw [(Real.sqrt_eq_rpow _).symm] at hlog
  have hlogRoot : Real.log (2 * (y : Real)) <=
      2 * Real.sqrt (2 * (y : Real)) := by
    calc
      Real.log (2 * (y : Real)) <=
          Real.sqrt (2 * (y : Real)) / (1 / 2) := hlog
      _ = 2 * Real.sqrt (2 * (y : Real)) := by ring
  have hsqrtNonneg : 0 <= Real.sqrt (2 * (y : Real)) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (2 * (y : Real)) ^ 2 = 2 * (y : Real) :=
    Real.sq_sqrt hxNonneg
  have hmul := mul_le_mul_of_nonneg_right hyReal hyNonneg
  rw [show ((2 * y : Nat) : Real) = 2 * (y : Real) by norm_num]
  have hrootBound :
      4 * ((M + 1 : Nat) : Real) * Real.sqrt (2 * (y : Real)) <= y := by
    by_contra hnot
    have hlt : (y : Real) <
        4 * ((M + 1 : Nat) : Real) * Real.sqrt (2 * (y : Real)) :=
      lt_of_not_ge hnot
    have hsqLt := mul_self_lt_mul_self hyNonneg hlt
    nlinarith
  calc
    2 * ((M + 1 : Nat) : Real) * Real.log (2 * (y : Real)) <=
        2 * ((M + 1 : Nat) : Real) *
          (2 * Real.sqrt (2 * (y : Real))) :=
      mul_le_mul_of_nonneg_left hlogRoot (by positivity)
    _ = 4 * ((M + 1 : Nat) : Real) * Real.sqrt (2 * (y : Real)) := by ring
    _ <= y := hrootBound

theorem exists_uniform_primeBand_card_gt :
    exists Y0 : Nat, forall M y : Nat,
      max Y0 (32 * (M + 1) ^ 2) <= y ->
        M < ((Nat.primesLE (2 * y)).filter (fun p => y < p)).card := by
  have hgap := eventually_theta_gap_half
  rw [eventually_atTop] at hgap
  choose Y hY using hgap
  refine Exists.intro (max 2 Y) ?_
  intro M y hy
  have hbase : max 2 Y <= y := le_trans (le_max_left _ _) hy
  have hyTwo : 2 <= y := le_trans (le_max_left _ _) hbase
  have hyY : Y <= y := le_trans (le_max_right _ _) hbase
  have hsquare : 32 * (M + 1) ^ 2 <= y := le_trans (le_max_right _ _) hy
  apply primeBand_card_gt_of_theta_gap M y hyTwo (hY y hyY)
  exact primeBand_size_condition_of_square M y hsquare

theorem exists_linnikDensePrimeBand_of_card_gt (M y : Nat)
    (hcard : M < ((Nat.primesLE (2 * y)).filter (fun p => y < p)).card) :
    exists P : Finset {p : Nat // 0 < p},
      P.card = M + 1 /\
        (forall p, Membership.mem P p ->
          p.val.Prime /\ y < p.val /\ p.val <= 2 * y) := by
  let s := (Nat.primesLE (2 * y)).filter (fun p => y < p)
  have hMCard : M + 1 <= s.card := Nat.succ_le_of_lt hcard
  cases Finset.exists_subset_card_eq hMCard with
  | intro t ht =>
      let e : {q : Nat // Membership.mem t q} -> {p : Nat // 0 < p} := fun q =>
        Subtype.mk q.val (by
          have hqs : Membership.mem s q.val := ht.1 q.property
          have hqPrime : q.val.Prime := (Nat.mem_primesLE.mp
            (Finset.mem_filter.mp hqs).1).2
          exact hqPrime.pos)
      have heInj : Function.Injective e := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun p : {p : Nat // 0 < p} => p.val) hab
      let emb : Function.Embedding {q : Nat // Membership.mem t q}
          {p : Nat // 0 < p} := Function.Embedding.mk e heInj
      let P : Finset {p : Nat // 0 < p} := t.attach.map emb
      refine Exists.intro P (And.intro ?_ ?_)
      next => simpa [P] using ht.2
      next =>
        intro p hp
        change Membership.mem (t.attach.map emb) p at hp
        rw [Finset.mem_map] at hp
        choose q hqAttach hqEq using hp
        have hpEq : emb q = p := hqEq
        subst p
        have hqs : Membership.mem s q.val := ht.1 q.property
        have hqMem := Finset.mem_filter.mp hqs
        have hqPrime : q.val.Prime := (Nat.mem_primesLE.mp hqMem.1).2
        have hqUpper : q.val <= 2 * y := (Nat.mem_primesLE.mp hqMem.1).1
        exact And.intro hqPrime (And.intro hqMem.2 hqUpper)

theorem exists_uniform_linnikDensePrimeBand :
    exists Y0 : Nat, forall M y : Nat,
      max Y0 (32 * (M + 1) ^ 2) <= y ->
        exists P : Finset {p : Nat // 0 < p},
          P.card = M + 1 /\
            (forall p, Membership.mem P p ->
              p.val.Prime /\ y < p.val /\ p.val <= 2 * y) := by
  choose Y0 hY0 using exists_uniform_primeBand_card_gt
  refine Exists.intro Y0 ?_
  intro M y hy
  exact exists_linnikDensePrimeBand_of_card_gt M y (hY0 M y hy)

namespace Finset

/-- Degree-uniform dense prime band with the exact finite modulus sum retained.
This is the sharp recurrence input: the modulus powers must be combined with
the lower-level mean value before any common modulus bound is applied. -/
theorem exists_uniform_vinogradovMeanValue_dense_sum_recurrence :
    exists Y0 : Nat, forall k r X : Nat,
      0 < k -> 1 < r -> 2 <= k * r ->
      (max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)) ^ k <= X ->
      exists P : Finset {p : Nat // 0 < p},
        P.card = k ^ 3 + 1 /\
          (forall p, Membership.mem P p ->
            p.val.Prime /\ Nat.nthRoot k X < p.val /\
              p.val <= 2 * Nat.nthRoot k X) /\
          vinogradovMeanValue k (k * r) X <=
            max
              (4 * (P.card * P.sum (fun p =>
                p.val ^ (2 * (k * (r - 1))) *
                  ((X ^ k * (k.factorial *
                    p.val ^ (k * (k - 1) / 2))) *
                      vinogradovMeanValue k (k * (r - 1))
                        (1 + X / p.val)))))
              (4 ^ (k * r) * k ^ (4 * (k * r))) := by
  choose Y0 hY0 using exists_uniform_linnikDensePrimeBand
  refine Exists.intro Y0 ?_
  intro k r X hk hr hm hthreshold
  let B := max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)
  have hBRoot : B <= Nat.nthRoot k X :=
    (Nat.le_nthRoot_iff hk.ne').mpr hthreshold
  have hBandRoot : max Y0 (32 * (k ^ 3 + 1) ^ 2) <= Nat.nthRoot k X := by
    apply max_le
    next => exact le_trans (le_trans (le_max_right k Y0) (le_max_left _ _)) hBRoot
    next => exact le_trans (le_max_right _ _) hBRoot
  have hkRoot : k <= Nat.nthRoot k X :=
    le_trans (le_trans (le_max_left k Y0) (le_max_left _ _)) hBRoot
  have hPX := hY0 (k ^ 3) (Nat.nthRoot k X) hBandRoot
  cases hPX with
  | intro P hP =>
      have hXRoot : X < (Nat.nthRoot k X + 1) ^ k :=
        Nat.lt_pow_nthRoot_add_one hk.ne' X
      have hgeom : X <= (Nat.nthRoot k X + 1) ^ (k + 1) := by
        exact le_trans (Nat.le_of_lt hXRoot)
          (Nat.pow_le_pow_right (by omega) (by omega))
      have hdistinct := linnikDistinctSquareSum_le_primeBand_vinogradovMeanValue
        P k r X (Nat.nthRoot k X) hk hr
        (fun p hpP => (hP.2 p hpP).1)
        (fun p hpP => (hP.2 p hpP).2.1)
        (by omega) hgeom
        (fun p hpP => lt_of_le_of_lt hkRoot (hP.2 p hpP).2.1)
        (fun p hpP => lt_of_lt_of_le hXRoot
          (Nat.pow_le_pow_left
            (Nat.succ_le_of_lt (hP.2 p hpP).2.1) k))
      have hrec := vinogradovMeanValue_le_max_of_distinctSquareSum_le
        k r X
          (P.card * P.sum (fun p =>
            p.val ^ (2 * (k * (r - 1))) *
              ((X ^ k * (k.factorial *
                p.val ^ (k * (k - 1) / 2))) *
                  vinogradovMeanValue k (k * (r - 1))
                    (1 + X / p.val))))
          (lt_trans (by omega) hr) hm hdistinct
      refine Exists.intro P (And.intro hP.1 (And.intro ?_ hrec))
      intro p hpP
      exact hP.2 p hpP

theorem exists_uniform_vinogradovMeanValue_dense_recurrence :
    exists Y0 : Nat, forall k r X : Nat,
      0 < k -> 1 < r -> 2 <= k * r ->
      (max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)) ^ k <= X ->
      vinogradovMeanValue k (k * r) X <=
        max
          (4 * ((k ^ 3 + 1) ^ 2 *
            ((2 * Nat.nthRoot k X) ^ (2 * (k * (r - 1))) *
              ((X ^ k * (k.factorial *
                  (2 * Nat.nthRoot k X) ^ (k * (k - 1) / 2))) *
                vinogradovMeanValue k (k * (r - 1))
                  (1 + X / (Nat.nthRoot k X + 1))))))
          (4 ^ (k * r) * k ^ (4 * (k * r))) := by
  choose Y0 hY0 using exists_uniform_linnikDensePrimeBand
  refine Exists.intro Y0 ?_
  intro k r X hk hr hm hthreshold
  let B := max (max k Y0) (32 * (k ^ 3 + 1) ^ 2)
  have hBRoot : B <= Nat.nthRoot k X :=
    (Nat.le_nthRoot_iff hk.ne').mpr hthreshold
  have hBandRoot : max Y0 (32 * (k ^ 3 + 1) ^ 2) <= Nat.nthRoot k X := by
    apply max_le
    next => exact le_trans (le_trans (le_max_right k Y0) (le_max_left _ _)) hBRoot
    next => exact le_trans (le_max_right _ _) hBRoot
  have hkRoot : k <= Nat.nthRoot k X :=
    le_trans (le_trans (le_max_left k Y0) (le_max_left _ _)) hBRoot
  have hPX := hY0 (k ^ 3) (Nat.nthRoot k X) hBandRoot
  cases hPX with
  | intro P hP =>
      have hXRoot : X < (Nat.nthRoot k X + 1) ^ k :=
        Nat.lt_pow_nthRoot_add_one hk.ne' X
      have hgeom : X <= (Nat.nthRoot k X + 1) ^ (k + 1) := by
        exact le_trans (Nat.le_of_lt hXRoot)
          (Nat.pow_le_pow_right (by omega) (by omega))
      have hrec := vinogradovMeanValue_le_primeBand_uniform
        P k r X (Nat.nthRoot k X) (2 * Nat.nthRoot k X)
          (vinogradovMeanValue k (k * (r - 1))
            (1 + X / (Nat.nthRoot k X + 1)))
          hk hr hm
          (fun p hpP => (hP.2 p hpP).1)
          (fun p hpP => (hP.2 p hpP).2.1)
          (by omega) hgeom
          (fun p hpP => lt_of_le_of_lt hkRoot (hP.2 p hpP).2.1)
          (fun p hpP => lt_of_lt_of_le hXRoot
            (Nat.pow_le_pow_left
              (Nat.succ_le_of_lt (hP.2 p hpP).2.1) k))
          (fun p hpP => (hP.2 p hpP).2.2)
          (by
            intro p hpP
            apply vinogradovMeanValue_mono
            apply Nat.add_le_add_left
            exact Nat.div_le_div_left
              (Nat.succ_le_of_lt (hP.2 p hpP).2.1) (by omega))
      rw [hP.1] at hrec
      exact hrec

end Finset

