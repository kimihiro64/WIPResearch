/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.SelbergSieve.FiniteWeights

/-!
# DownsetMass

Finite Selberg sieve input, proved from Mathlib primitives.
The classical sieve argument follows D. R. Heath-Brown, Lectures on sieves,
Sections 2-3 (https://arxiv.org/abs/math/0209360).
No prime-distribution or unproved analytic hypothesis is introduced.
-/

set_option autoImplicit false
open scoped Classical

namespace Nat

theorem squarefree_quotient_lcm {e d l : Nat} (he : Squarefree e)
    (hd : Dvd.dvd d e) (hl : Dvd.dvd l d) :
    Nat.lcm (e/l) d = e := by
  have hle : Dvd.dvd l e := dvd_trans hl hd
  apply Nat.dvd_antisymm
  next => exact Nat.lcm_dvd_iff.mpr (And.intro (Nat.div_dvd_of_dvd hle) hd)
  next =>
    have hc : Nat.Coprime (e/l) l := Nat.coprime_of_squarefree_mul (by
      rw [Nat.div_mul_cancel hle]
      exact he)
    have hm := hc.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_left (e/l) d)
      (dvd_trans hl (Nat.dvd_lcm_right (e/l) d))
    simpa only [Nat.div_mul_cancel hle] using hm

end Nat

namespace BoundingSieve

/-- A downward-closed finite sieve support has no excessive upper-divisor
mass. The injection (e,l)->e/l preserves every weight and is recovered by
lcm with d. This is the actual estimate needed for |lambda_d|<=1. -/
theorem finiteSelberg_upper_divisor_mass (s : BoundingSieve) (D : Finset Nat)
    (hD : forall e, Membership.mem D e -> Dvd.dvd e s.prodPrimes)
    (hdown : forall e, Membership.mem D e -> forall k, Dvd.dvd k e -> Membership.mem D k)
    {d : Nat} (hd : Dvd.dvd d s.prodPrimes) :
    Inv.inv (s.nu d)*D.sum (fun e => if Dvd.dvd d e then s.selbergTerms e else 0) <=
      s.finiteSelbergDenominator D := by
  let E := D.filter (fun e => Dvd.dvd d e)
  let B := E.product d.divisors
  have hdata : forall x : Prod Nat Nat, Membership.mem B x ->
      Membership.mem D x.1 /\ Dvd.dvd d x.1 /\ Dvd.dvd x.2 d := by
    intro x hx
    have hp := Finset.mem_product.mp hx
    have he := Finset.mem_filter.mp hp.1
    exact And.intro he.1 (And.intro he.2 (Nat.dvd_of_mem_divisors hp.2))
  have hinj : Set.InjOn (fun x : Prod Nat Nat => x.1/x.2) B := by
    intro x hx y hy hxy
    have hxd := hdata x hx
    have hyd := hdata y hy
    have hxs := s.squarefree_of_dvd_prodPrimes (hD x.1 hxd.1)
    have hys := s.squarefree_of_dvd_prodPrimes (hD y.1 hyd.1)
    have hxe := Nat.squarefree_quotient_lcm hxs hxd.2.1 hxd.2.2
    have hye := Nat.squarefree_quotient_lcm hys hyd.2.1 hyd.2.2
    have he : x.1 = y.1 := hxe.symm.trans
      ((congrArg (fun v => Nat.lcm v d) hxy).trans hye)
    have hxr := Nat.divisor_complement_complement
      (Nat.pos_of_ne_zero hxs.ne_zero) (dvd_trans hxd.2.2 hxd.2.1)
    have hyr := Nat.divisor_complement_complement
      (Nat.pos_of_ne_zero hys.ne_zero) (dvd_trans hyd.2.2 hyd.2.1)
    have hdiv : x.1/(x.1/x.2) = y.1/(y.1/y.2) :=
      (congrArg (fun v => v/(x.1/x.2)) he).trans (congrArg (fun v => y.1/v) hxy)
    have hl : x.2 = y.2 := hxr.symm.trans (hdiv.trans hyr)
    exact Prod.ext he hl
  have hsub : B.image (fun x => x.1/x.2) <= D := by
    intro k hk
    choose x hx using Finset.mem_image.mp hk
    have hxd := hdata x hx.1
    rw [<- hx.2]
    exact hdown x.1 hxd.1 (x.1/x.2)
      (Nat.div_dvd_of_dvd (dvd_trans hxd.2.2 hxd.2.1))
  have hsumle : (B.image (fun x => x.1/x.2)).sum s.selbergTerms <= D.sum s.selbergTerms :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun e he _ => le_of_lt (s.selbergTerms_pos (hD e he)))
  have him : (B.image (fun x => x.1/x.2)).sum s.selbergTerms =
      B.sum (fun x => s.selbergTerms (x.1/x.2)) := Finset.sum_image hinj
  rw [him] at hsumle
  have hnu := s.nu_inv_eq_sum_divisors_inv_selbergTerms hd
  rw [<- Finset.sum_filter,
    Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hd] at hnu
  have hpoint : forall e, Membership.mem E e ->
      d.divisors.sum (fun l => s.selbergTerms (e/l)) =
        s.selbergTerms e*Inv.inv (s.nu d) := by
    intro e he
    have hed := Finset.mem_filter.mp he
    have hes := s.squarefree_of_dvd_prodPrimes (hD e hed.1)
    rw [hnu, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hld := Nat.dvd_of_mem_divisors hl
    have hle : Dvd.dvd l e := dvd_trans hld hed.2
    have hcop : Nat.Coprime (e/l) l := Nat.coprime_of_squarefree_mul (by
      rw [Nat.div_mul_cancel hle]
      exact hes)
    have heq := s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop
    rw [Nat.div_mul_cancel hle] at heq
    have hg0 : Not (s.selbergTerms l = 0) :=
      ne_of_gt (s.selbergTerms_pos (dvd_trans hld hd))
    calc
      s.selbergTerms (e/l) = s.selbergTerms (e/l)*
          (s.selbergTerms l*Inv.inv (s.selbergTerms l)) := by simp [hg0]
      _ = (s.selbergTerms (e/l)*s.selbergTerms l)*Inv.inv (s.selbergTerms l) := by ring
      _ = s.selbergTerms e*Inv.inv (s.selbergTerms l) := by rw [<- heq]
  have hsum : B.sum (fun x => s.selbergTerms (x.1/x.2)) =
      Inv.inv (s.nu d)*E.sum s.selbergTerms := by
    have hprod : B.sum (fun x => s.selbergTerms (x.1/x.2)) =
        E.sum (fun e => d.divisors.sum (fun l => s.selbergTerms (e/l))) :=
      Finset.sum_finset_product B E (fun _ => d.divisors) (fun _ => Finset.mem_product)
    rw [hprod]
    calc
      E.sum (fun e => d.divisors.sum (fun l => s.selbergTerms (e/l))) =
          E.sum (fun e => s.selbergTerms e*Inv.inv (s.nu d)) :=
        Finset.sum_congr rfl hpoint
      _ = Inv.inv (s.nu d)*E.sum s.selbergTerms := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
  rw [hsum] at hsumle
  simpa only [E, Finset.sum_filter, finiteSelbergDenominator] using hsumle

end BoundingSieve
