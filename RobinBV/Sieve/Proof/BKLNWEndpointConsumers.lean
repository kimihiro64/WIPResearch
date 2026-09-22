/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import RobinBV.Sieve.Proof.BKLNWZeroesRect

/-!
# Endpoint consumers for the BKLNW height partition

These focused consumers close the two singleton-endpoint obligations used by
the Ioc height-band estimate: exact multiplicity mass from a density bound,
and the zero-free pointwise weight at the endpoint.
-/

set_option autoImplicit false

namespace RobinBV.Sieve

theorem rob_bv_zeroes_rect_endpoint_mass_le_density
    (a b y sigma d : Real) (ZDB : zero_density_bound)
    (hsigma : sigma < a) (hb : b < 1) (hy : 0 < y) (hupper : y < d)
    (hT0 : rob_bv_density_T0 ZDB <= d)
    (hrange : Membership.mem (rob_bv_density_range ZDB) sigma) :
    let S := riemannZeta.zeroes_rect (Set.Icc a b) ({y} : Set Real)
    let hfin : S.Finite :=
      (rob_bv_zeroes_rect_Icc_finite a b (y - 1) (y + 1)).subset (by
        intro z hz
        have hlow : y - 1 < (z : Complex).im := by
          have h := Set.mem_singleton_iff.mp hz.2.1
          linarith
        have hhigh : (z : Complex).im < y + 1 := by
          have h := Set.mem_singleton_iff.mp hz.2.1
          linarith
        exact And.intro hz.1
          (And.intro (And.intro hlow hhigh) hz.2.2))
    letI : Fintype S := hfin.fintype
    Finset.univ.sum (fun z : S =>
      ((riemannZeta.order (z : Complex) : Int) : Real)) <= ZDB.N sigma d := by
  let S := riemannZeta.zeroes_rect (Set.Icc a b) ({y} : Set Real)
  let hfin : S.Finite :=
    (rob_bv_zeroes_rect_Icc_finite a b (y - 1) (y + 1)).subset (by
      intro z hz
      have hlow : y - 1 < (z : Complex).im := by
        have h := Set.mem_singleton_iff.mp hz.2.1
        linarith
      have hhigh : (z : Complex).im < y + 1 := by
        have h := Set.mem_singleton_iff.mp hz.2.1
        linarith
      exact And.intro hz.1
        (And.intro (And.intro hlow hhigh) hz.2.2))
  letI : Fintype S := hfin.fintype
  refine rob_bv_zeroes_rect_mass_le_density_bound sigma d S hfin ?_ ?_ ?_ ?_ ?_
    ZDB hT0 hrange
  next =>
    intro z
    exact z.property.2.2
  next =>
    intro z
    exact lt_of_lt_of_le hsigma (Set.mem_Icc.mp z.property.1).1
  next =>
    intro z
    exact lt_of_le_of_lt (Set.mem_Icc.mp z.property.1).2 hb
  next =>
    intro z
    have heq := Set.mem_singleton_iff.mp z.property.2.1
    rw [heq]
    exact hy
  next =>
    intro z
    have heq := Set.mem_singleton_iff.mp z.property.2.1
    rw [heq]
    exact hupper

theorem rob_bv_zeroes_rect_endpoint_pointwise_zero_free
    (a b x y R : Real) (hx : 1 < x) (hy : 1 < y) (hR : 0 < R)
    (hre : forall z : riemannZeta.zeroes_rect (Set.Icc a b) ({y} : Set Real),
      (z : Complex).re <= 1 - 1 / (R * Real.log y)) :
    forall z : riemannZeta.zeroes_rect (Set.Icc a b) ({y} : Set Real),
      norm ((x : Complex) ^ ((z : Complex) - 1) / (z : Complex)) <=
        x ^ (-(1 / (R * Real.log y))) / y := by
  intro z
  have heq := Set.mem_singleton_iff.mp z.property.2.1
  have himpos : 0 < (z : Complex).im := by
    rw [heq]
    positivity
  have hgeom : y <= norm (z : Complex) := by
    have habs : y <= abs (z : Complex).im := by
      rw [abs_of_pos himpos, heq]
    exact habs.trans (Complex.abs_im_le_norm (z : Complex))
  exact Complex.norm_cpow_div_zero_free_bound hx hy hgeom hR (hre z)

end RobinBV.Sieve
