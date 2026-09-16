/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exponential Fourier kernel

The Fourier integral of exp(-a*abs(u)) is evaluated for every positive
real a and every real frequency. Both half-lines are included.
-/

set_option autoImplicit false

namespace Complex

theorem integral_exp_neg_mul_abs_fourier {a : Real} (ha : 0 < a) (r : Real) :
    MeasureTheory.integral MeasureTheory.volume
      (fun u : Real => Complex.exp (-(a : Complex)*abs u - Complex.I*r*u)) =
        2*(a : Complex)/((a : Complex)^2+(r : Complex)^2) := by
  let f : Real -> Complex := fun u =>
    Complex.exp (-(a : Complex)*abs u - Complex.I*r*u)
  have hpRe : (-(a : Complex)-Complex.I*r).re < 0 := by
    simpa using (neg_lt_zero.mpr ha)
  have hnRe : 0 < ((a : Complex)-Complex.I*r).re := by
    simpa using ha
  have hpEq : Set.EqOn f
      (fun u : Real => Complex.exp ((-(a : Complex)-Complex.I*r)*u))
      (Set.Ioi 0) := by
    intro u hu
    dsimp [f]
    rw [abs_of_pos hu]
    congr 1
    ring
  have hnEq : Set.EqOn f
      (fun u : Real => Complex.exp (((a : Complex)-Complex.I*r)*u))
      (Set.Iic 0) := by
    intro u hu
    dsimp [f]
    rw [abs_of_nonpos hu, Complex.ofReal_neg]
    congr 1
    ring
  have hp : MeasureTheory.IntegrableOn f (Set.Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hpRe 0).congr_fun
      (fun u hu => (hpEq hu).symm) measurableSet_Ioi
  have hn : MeasureTheory.IntegrableOn f (Set.Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hnRe 0).congr_fun
      (fun u hu => (hnEq hu).symm) measurableSet_Iic
  have hf : MeasureTheory.Integrable f := by
    have hu := hp.union hn
    have he : Union.union (Set.Ioi (0 : Real)) (Set.Iic 0) = Set.univ := by
      ext u
      simp
    rw [he, MeasureTheory.integrableOn_univ] at hu
    exact hu
  have hpInt :
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi 0)) f =
        -1/(-(a : Complex)-Complex.I*r) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => hpEq hu)]
    rw [integral_exp_mul_complex_Ioi hpRe]
    simp
  have hnInt :
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Iic 0)) f =
        1/((a : Complex)-Complex.I*r) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic (fun u hu => hnEq hu)]
    rw [integral_exp_mul_complex_Iic hnRe]
    simp
  have hp0 : Not ((a : Complex)+Complex.I*r = 0) := by
    intro h
    have h0 : a = 0 := by simpa using congrArg Complex.re h
    exact ha.ne' h0
  have hn0 : Not ((a : Complex)-Complex.I*r = 0) := by
    intro h
    have h0 : a = 0 := by simpa using congrArg Complex.re h
    exact ha.ne' h0
  have hprod : ((a : Complex)+Complex.I*r)*((a : Complex)-Complex.I*r) =
      (a : Complex)^2+(r : Complex)^2 := by
    calc
      _ = (a : Complex)^2-Complex.I^2*(r : Complex)^2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  change MeasureTheory.integral MeasureTheory.volume f = _
  rw [<- MeasureTheory.integral_add_compl (s := Set.Ioi 0) measurableSet_Ioi hf,
    Set.compl_Ioi, hpInt, hnInt]
  rw [show -(a : Complex)-Complex.I*r = -((a : Complex)+Complex.I*r) by ring,
    neg_div_neg_eq, <- hprod]
  field_simp [hp0, hn0]
  ring


end Complex
