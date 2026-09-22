/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
/-
# Fifth-incidence square-interval packets

This module counts the fifth-power incidence configurations used by the
owner-band refinements of the square-interval sieve.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalRepeatedHyperbola

/-!
# Fifth-degree incidence minorants and unavoidable multiplicity loss

The shifted-root polynomial is nonpositive at positive integer multiplicities.
Its exact loss has a uniform lower bound from the four- and six-factor cells.
The actual two-stage square sieve identifies zero multiplicity with primes,
giving the exact corrected-moment identity without assuming prime existence.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- The fifth-degree incidence polynomial with its positive normalization denominator cleared. -/
def fifthRootNumerator (b r : Nat) : Int :=
  (1-(r : Int))*((r : Int)-2)*((r : Int)-3)*
    ((r : Int)-(b : Int))*((r : Int)-(b : Int)-1)

/-- The exact nonnegative loss from the zero-multiplicity indicator, with denominator cleared. -/
def fifthLossNumerator (b r : Nat) : Int :=
  if r = 0 then 0 else -fifthRootNumerator b r

/-- The product of consecutive integers is nonnegative. -/
theorem integer_mul_pred_nonneg (z : Int) : 0 <= z*(z-1) := by
  by_cases h : z <= 0
  next => exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
  next => exact mul_nonneg (by omega) (by omega)

/-- The fifth numerator is nonpositive at every positive integer multiplicity. -/
theorem fifthRootNumerator_nonpos {b r : Nat} (hr : 1 <= r) :
    fifthRootNumerator b r <= 0 := by
  have h23 := integer_mul_pred_nonneg ((r : Int)-2)
  have hbb := integer_mul_pred_nonneg ((r : Int)-(b : Int))
  have hp := mul_nonneg h23 hbb
  have hneg : 1-(r : Int) <= 0 := by omega
  have hz := mul_nonpos_of_nonpos_of_nonneg hneg hp
  unfold fifthRootNumerator
  nlinarith only [hz]

/-- Every cleared-denominator loss is nonnegative, including the zero-multiplicity case. -/
theorem fifthLossNumerator_nonneg (b r : Nat) : 0 <= fifthLossNumerator b r := by
  unfold fifthLossNumerator
  split_ifs with hr
  next => exact le_rfl
  next => have h := fifthRootNumerator_nonpos (b := b) (show 1 <= r by omega); omega

/-- The minorant numerator plus its exact loss is the scaled zero-multiplicity indicator. -/
theorem fifthRootNumerator_add_loss (b r : Nat) :
    fifthRootNumerator b r + fifthLossNumerator b r =
      if r = 0 then 6*(b : Int)*((b : Int)+1) else 0 := by
  by_cases hr : r = 0
  next => subst r; simp [fifthRootNumerator, fifthLossNumerator]; ring
  next => simp [fifthLossNumerator, hr]

/-- The exact loss coefficient at multiplicity four. -/
theorem fifthLossNumerator_four (b : Nat) :
    fifthLossNumerator b 4 = 6*((b : Int)-4)*((b : Int)-3) := by
  norm_num [fifthLossNumerator, fifthRootNumerator]
  ring

/-- The exact loss coefficient at multiplicity six. -/
theorem fifthLossNumerator_six (b : Nat) :
    fifthLossNumerator b 6 = 60*((b : Int)-6)*((b : Int)-5) := by
  norm_num [fifthLossNumerator, fifthRootNumerator]
  ring

/-- No integer shift simultaneously suppresses the four- and six-factor losses. -/
theorem fifthLossNumerator_four_six (b : Nat) :
    6*(b : Int)*((b : Int)+1) <=
      15*(fifthLossNumerator b 4 + fifthLossNumerator b 6) := by
  rw [fifthLossNumerator_four, fifthLossNumerator_six]
  have h : 0 <= ((b : Int)-5)*(41*(b : Int)-234) := by
    by_cases hb : b <= 5
    next => exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    next => exact mul_nonneg (by omega) (by omega)
  nlinarith only [h]

/-- Summing the pointwise identity preserves the complete finite correction. -/
theorem sum_fifthRootNumerator_add_loss {alpha : Type*} (s : Finset alpha)
    (r : alpha -> Nat) (b : Nat) :
    s.sum (fun x => fifthRootNumerator b (r x)) +
      s.sum (fun x => fifthLossNumerator b (r x)) =
      6*(b : Int)*((b : Int)+1)*((s.filter (fun x => r x = 0)).card : Int) := by
  rw [<- Finset.sum_add_distrib]
  simp_rw [fifthRootNumerator_add_loss]
  rw [<- Finset.sum_filter]
  simp [mul_comm]

/-- The complete loss dominates the actual four- and six-multiplicity subcounts. -/
theorem sum_fifthLossNumerator_ge_four_six {alpha : Type*} (s : Finset alpha)
    (r : alpha -> Nat) (b : Nat) :
    ((s.filter (fun x => r x = 4)).card : Int)*fifthLossNumerator b 4 +
      ((s.filter (fun x => r x = 6)).card : Int)*fifthLossNumerator b 6 <=
      s.sum (fun x => fifthLossNumerator b (r x)) := by
  have hs : s.sum (fun x => (if r x = 4 then fifthLossNumerator b 4 else 0) +
      (if r x = 6 then fifthLossNumerator b 6 else 0)) <=
      s.sum (fun x => fifthLossNumerator b (r x)) := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases h4 : r x = 4
    next => simp [h4]
    next =>
      by_cases h6 : r x = 6
      next => simp [h6]
      next => simpa [h4, h6] using fifthLossNumerator_nonneg b (r x)
  rw [Finset.sum_add_distrib] at hs
  simpa only [<- Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] using hs

/-- A uniform loss lower bound in terms of the smaller of the two retained multiplicity counts. -/
theorem sum_fifthLossNumerator_min_lower {alpha : Type*} (s : Finset alpha)
    (r : alpha -> Nat) (b : Nat) :
    6*(b : Int)*((b : Int)+1)*
      ((min (s.filter (fun x => r x = 4)).card (s.filter (fun x => r x = 6)).card : Nat) : Int) <=
      15*s.sum (fun x => fifthLossNumerator b (r x)) := by
  let k := min (s.filter (fun x => r x = 4)).card (s.filter (fun x => r x = 6)).card
  have h4 : (k : Int) <= ((s.filter (fun x => r x = 4)).card : Int) := by dsimp [k]; omega
  have h6 : (k : Int) <= ((s.filter (fun x => r x = 6)).card : Int) := by dsimp [k]; omega
  have ha := fifthLossNumerator_nonneg b 4
  have hc := fifthLossNumerator_nonneg b 6
  have hm4 := mul_le_mul_of_nonneg_right h4 ha
  have hm6 := mul_le_mul_of_nonneg_right h6 hc
  have hpoint := mul_le_mul_of_nonneg_right (fifthLossNumerator_four_six b)
    (show (0 : Int) <= (k : Int) by omega)
  have hs := sum_fifthLossNumerator_ge_four_six s r b
  change 6*(b : Int)*((b : Int)+1)*(k : Int) <= _
  nlinarith only [hpoint, hm4, hm6, hs]

/-- Odd square-interval cells retaining every exclusion by primes above the chosen cutoff through the index. -/
noncomputable def squareMomentSurvivors (n z : Nat) : Finset Nat := by
  classical
  exact (Finset.range ((n+1)*(n+1))).filter (fun m => n*n < m /\ m%2 = 1 /\
    forall p, Membership.mem (oddPrimesBetween (z+1) n) p -> Not (Dvd.dvd p m))

/-- The actual number of distinct small odd prime divisors of a cell. -/
def squareMomentMultiplicity (z m : Nat) : Nat :=
  ((oddPrimesBetween 3 z).filter (fun p => Dvd.dvd p m)).card

/-- Membership states both exact interval endpoints, odd parity, and the full larger-prime exclusion history. -/
theorem mem_squareMomentSurvivors {n z m : Nat} :
    Membership.mem (squareMomentSurvivors n z) m <->
      m < (n+1)*(n+1) /\ n*n < m /\ m%2 = 1 /\
      forall p, Membership.mem (oddPrimesBetween (z+1) n) p -> Not (Dvd.dvd p m) := by
  simp only [squareMomentSurvivors, Finset.mem_filter, Finset.mem_range]

/-- Within the fully retained two-stage support, zero small multiplicity is equivalent to primality. -/
theorem squareMomentMultiplicity_zero_iff_prime {n z m : Nat} (hn : 2 <= n)
    (hz : z <= n) (hm : Membership.mem (squareMomentSurvivors n z) m) :
    squareMomentMultiplicity z m = 0 <-> Nat.Prime m := by
  classical
  have hm' := mem_squareMomentSurvivors.mp hm
  have hhi := hm'.1
  have hlo := hm'.2.1
  have hodd := hm'.2.2.1
  constructor
  next =>
    intro hzero
    by_contra hcomp
    have hmpos : 0 < m := by nlinarith
    have hp : Nat.Prime m.minFac := Nat.minFac_prime (by nlinarith)
    have hpd := Nat.minFac_dvd m
    have hsq := Nat.minFac_sq_le_self hmpos hcomp
    have hpn : m.minFac <= n := by nlinarith
    have hpodd : m.minFac%2 = 1 := hp.eq_two_or_odd.resolve_left (by
      intro he
      rw [he] at hpd
      have heven := Nat.dvd_iff_mod_eq_zero.mp hpd
      omega)
    have hp3 : 3 <= m.minFac := by have h := hp.two_le; omega
    by_cases hpz : m.minFac <= z
    next =>
      have hmem : Membership.mem ((oddPrimesBetween 3 z).filter (fun p => Dvd.dvd p m)) m.minFac :=
        Finset.mem_filter.mpr (And.intro (Finset.mem_filter.mpr
          (And.intro (Finset.mem_range.mpr (by omega)) (And.intro hp (And.intro hpodd hp3)))) hpd)
      have hpos := Finset.card_pos.mpr (Exists.intro m.minFac hmem)
      change ((oddPrimesBetween 3 z).filter (fun p => Dvd.dvd p m)).card = 0 at hzero
      omega
    next =>
      have hmem : Membership.mem (oddPrimesBetween (z+1) n) m.minFac :=
        Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega))
          (And.intro hp (And.intro hpodd (by omega))))
      exact hm'.2.2.2 m.minFac hmem hpd
  next =>
    intro hp
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hpm
    have hdiv := Finset.mem_filter.mp hpm
    have hsmall := Finset.mem_filter.mp hdiv.1
    have hprange := Finset.mem_range.mp hsmall.1
    have he : p = m := (hp.eq_one_or_self_of_dvd p hdiv.2).resolve_left hsmall.2.1.ne_one
    nlinarith

/-- The zero-multiplicity cells are exactly the actual square-interval primes. -/
theorem squareMomentSurvivors_filter_zero {n z : Nat} (hn : 2 <= n) (hz : z <= n) :
    (squareMomentSurvivors n z).filter (fun m => squareMomentMultiplicity z m = 0) =
      squareIntervalPrimes n := by
  classical
  ext m
  constructor
  next =>
    intro hm
    have h := Finset.mem_filter.mp hm
    have hs := mem_squareMomentSurvivors.mp h.1
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr hs.1)
      (And.intro hs.2.1 ((squareMomentMultiplicity_zero_iff_prime hn hz h.1).mp h.2)))
  next =>
    intro hm
    have h := Finset.mem_filter.mp hm
    have hp := h.2.2
    have hodd : m%2 = 1 := hp.eq_two_or_odd.resolve_left (by nlinarith [h.2.1])
    have hs : Membership.mem (squareMomentSurvivors n z) m := by
      apply mem_squareMomentSurvivors.mpr
      refine And.intro (Finset.mem_range.mp h.1) (And.intro h.2.1 (And.intro hodd ?_))
      intro p hpm hpd
      have hc := Finset.mem_filter.mp hpm
      have hpn := Finset.mem_range.mp hc.1
      have he : p = m := (hp.eq_one_or_self_of_dvd p hpd).resolve_left hc.2.1.ne_one
      nlinarith [h.2.1]
    exact Finset.mem_filter.mpr (And.intro hs
      ((squareMomentMultiplicity_zero_iff_prime hn hz hs).mpr hp))

/-- The complete fifth numerator and its retained correction give the exact scaled interval prime count. -/
theorem square_fifth_numerator_add_loss {n z : Nat} (hn : 2 <= n) (hz : z <= n) (b : Nat) :
    (squareMomentSurvivors n z).sum (fun m => fifthRootNumerator b (squareMomentMultiplicity z m)) +
      (squareMomentSurvivors n z).sum (fun m => fifthLossNumerator b (squareMomentMultiplicity z m)) =
      6*(b : Int)*((b : Int)+1)*((squareIntervalPrimes n).card : Int) := by
  have h := sum_fifthRootNumerator_add_loss (squareMomentSurvivors n z) (squareMomentMultiplicity z) b
  rw [squareMomentSurvivors_filter_zero hn hz] at h
  exact h

/-- The actual fifth minorant has an unavoidable loss controlled by its four- and six-factor subcounts. -/
theorem square_fifth_numerator_four_six_upper {n z : Nat}
    (hn : 2 <= n) (hz : z <= n) (b : Nat) :
    let s := squareMomentSurvivors n z;
    15*s.sum (fun m => fifthRootNumerator b (squareMomentMultiplicity z m)) +
      6*(b : Int)*((b : Int)+1)*
        ((min (s.filter (fun m => squareMomentMultiplicity z m = 4)).card
          (s.filter (fun m => squareMomentMultiplicity z m = 6)).card : Nat) : Int) <=
      15*(6*(b : Int)*((b : Int)+1)*((squareIntervalPrimes n).card : Int)) := by
  have he := square_fifth_numerator_add_loss hn hz b
  have hbound := sum_fifthLossNumerator_min_lower (squareMomentSurvivors n z)
    (squareMomentMultiplicity z) b
  dsimp only
  nlinarith only [he, hbound]

/-- Strict positivity of the complete fifth numerator is a sufficient condition for a prime in the interval. -/
theorem square_fifth_numerator_pos_implies_prime {n z b : Nat}
    (hn : 2 <= n) (hz : z <= n)
    (hpos : 0 < (squareMomentSurvivors n z).sum
      (fun m => fifthRootNumerator b (squareMomentMultiplicity z m))) :
    exists p : Nat, n*n < p /\ p < (n+1)*(n+1) /\ Nat.Prime p := by
  have he := square_fifth_numerator_add_loss hn hz b
  have hloss : 0 <= (squareMomentSurvivors n z).sum
      (fun m => fifthLossNumerator b (squareMomentMultiplicity z m)) :=
    Finset.sum_nonneg (fun m _ => fifthLossNumerator_nonneg b (squareMomentMultiplicity z m))
  have hcard : 0 < (squareIntervalPrimes n).card := by
    by_contra h
    have hzero : (squareIntervalPrimes n).card = 0 := by omega
    rw [hzero] at he
    norm_num at he
    omega
  choose p hp using Finset.card_pos.mp hcard
  have hm := Finset.mem_filter.mp hp
  exact Exists.intro p (And.intro hm.2.1 (And.intro (Finset.mem_range.mp hm.1) hm.2.2))

/-- Exact binomial-basis expansion of the fifth-degree numerator, valid also at small multiplicities. -/
theorem fifthRootNumerator_eq_binomial (b r : Nat) :
    fifthRootNumerator b r =
      6*(b : Int)*((b : Int)+1)*(1-(r : Int)+(r.choose 2 : Int)-(r.choose 3 : Int)) +
      (48*(b : Int)-72)*(r.choose 4 : Int)-120*(r.choose 5 : Int) := by
  have hk (k : Nat) : (k.factorial : Int)*(r.choose k : Int) =
      (_root_.descPochhammer Int k).eval (r : Int) := by
    rw [_root_.descPochhammer_eval_eq_descFactorial]
    have he := congrArg (fun a : Nat => (a : Int))
      (Nat.descFactorial_eq_factorial_mul_choose r k)
    simpa only [Nat.cast_mul] using he.symm
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  have h5 := hk 5
  norm_num [Nat.factorial, _root_.descPochhammer_succ_eval,
    _root_.descPochhammer_zero, Polynomial.eval_one] at h2 h3 h4 h5
  have hs2 := congrArg (fun a : Int => 3*(b : Int)*((b : Int)+1)*a) h2
  have hs3 := congrArg (fun a : Int => (b : Int)*((b : Int)+1)*a) h3
  have hs4 := congrArg (fun a : Int => (2*(b : Int)-3)*a) h4
  unfold fifthRootNumerator
  nlinarith only [hs2, hs3, hs4, h5]

/-- The exact binomial incidence moment after retaining all higher-prime exclusions. -/
noncomputable def squareCorrectedMoment (n z k : Nat) : Int :=
  (squareMomentSurvivors n z).sum (fun m => ((squareMomentMultiplicity z m).choose k : Int))

/-- The original corrected fifth-moment combination with the denominator cleared. -/
noncomputable def squareFifthMomentNumerator (n z b : Nat) : Int :=
  6*(b : Int)*((b : Int)+1)*(squareCorrectedMoment n z 0-squareCorrectedMoment n z 1+
    squareCorrectedMoment n z 2-squareCorrectedMoment n z 3) +
    (48*(b : Int)-72)*squareCorrectedMoment n z 4-120*squareCorrectedMoment n z 5

/-- Summing the binomial expansion gives exactly the corrected six-moment expression. -/
theorem sum_fifthRootNumerator_eq_corrected_moments (n z b : Nat) :
    (squareMomentSurvivors n z).sum (fun m => fifthRootNumerator b (squareMomentMultiplicity z m)) =
      squareFifthMomentNumerator n z b := by
  unfold squareFifthMomentNumerator squareCorrectedMoment
  simp_rw [fifthRootNumerator_eq_binomial]
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one,
    mul_sub, mul_add, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    <- Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- An exact cross-multiplied comparison between adjacent root shifts, with all base moments canceled. -/
theorem squareFifthMomentNumerator_succ_cross (n z b : Nat) :
    (b : Int)*squareFifthMomentNumerator n z (b+1)-
      ((b : Int)+2)*squareFifthMomentNumerator n z b =
      48*((3-(b : Int))*squareCorrectedMoment n z 4+5*squareCorrectedMoment n z 5) := by
  unfold squareFifthMomentNumerator
  push_cast
  ring

/-- Strict positivity of the original corrected fifth-moment combination supplies a square-interval prime. -/
theorem square_fifth_moment_pos_implies_prime {n z b : Nat}
    (hn : 2 <= n) (hz : z <= n) (hpos : 0 < squareFifthMomentNumerator n z b) :
    exists p : Nat, n*n < p /\ p < (n+1)*(n+1) /\ Nat.Prime p := by
  apply square_fifth_numerator_pos_implies_prime hn hz
  rw [sum_fifthRootNumerator_eq_corrected_moments]
  exact hpos

end Nat.PrimeSieve
