import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ChebyshevCorrection
import RobinBV.NumberField.Proof.DirichletCharacterReweight

/-!
# Complete endpoint correction on passing to the conductor

The actual complex weighted integrals differ by the integral of the complete
Chebyshev correction. A uniform explicit inverse-cutoff bound is proved
without ERH. This bound transports the critical scale; it does not replace
the separate sharp resonant and periodic prime-power expansion.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set

noncomputable section

/-- The exact change of level in the complete endpoint integral. -/
theorem dirichletWeightedIntegral_sub_primitive_eq
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Not (chi = 1)) {x : Real} (hx : 3 <= x) :
    dirichletCharacterWeightedIntegral chi 1 x -
        dirichletCharacterWeightedIntegral chi.primitiveCharacter 1 x =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (characterChebyshevSum (Nat.floor t) chi -
          characterChebyshevSum (Nat.floor t) chi.primitiveCharacter) *
            (Robin1984.robinRealWeight 1 t : Complex)) := by
  have hPrimitive := BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
    chi hchi
  have hLeft := (integrableOn_characterChebyshevStep_mul_weight_one chi hchi).mono_set
    (Ioi_subset_Ioi hx)
  have hRight := (integrableOn_characterChebyshevStep_mul_weight_one
    chi.primitiveCharacter hPrimitive).mono_set (Ioi_subset_Ioi hx)
  simp only [dirichletCharacterWeightedIntegral, sub_mul]
  exact (integral_sub hLeft hRight).symm

/-- Pointwise complete correction majorant. It uses all prime powers and
requires no nonprincipality or ERH assumption. -/
theorem norm_imprimitiveChebyshevStep_mul_weight_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x t : Real} (hx : 3 <= x) (ht : x <= t) :
    norm ((characterChebyshevSum (Nat.floor t) chi -
      characterChebyshevSum (Nat.floor t) chi.primitiveCharacter) *
        (Robin1984.robinRealWeight 1 t : Complex)) <=
      (Real.log N / Real.log 2 * (1 + 1 / Real.log x)) * t ^ (-2 : Real) := by
  have hxPos : 0 < x := by linarith
  have htPos : 0 < t := hxPos.trans_le ht
  have hxOne : 1 < x := by linarith
  have htOne : 1 < t := hxOne.trans_le ht
  have hLogN : 0 <= Real.log N :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)))
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hLogX : 0 < Real.log x := Real.log_pos hxOne
  have hLogT : 0 < Real.log t := Real.log_pos htOne
  have hFloor : 0 < Nat.floor t := by
    have hThree : 3 <= Nat.floor t := Nat.le_floor (hx.trans ht)
    omega
  have hFloorPos : (0 : Real) < (Nat.floor t : Nat) := by exact_mod_cast hFloor
  have hLogFloor : Real.log (Nat.floor t : Nat) <= Real.log t :=
    Real.log_le_log hFloorPos (Nat.floor_le htPos.le)
  have hRaw := norm_characterChebyshevSum_sub_primitive_le (NeZero.ne N) chi hFloor
  have hStep : norm (characterChebyshevSum (Nat.floor t) chi -
      characterChebyshevSum (Nat.floor t) chi.primitiveCharacter) <=
        Real.log N * Real.log t / Real.log 2 := by
    exact hRaw.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hLogFloor hLogN) hLogTwo.le)
  have hWeight : 0 <= Robin1984.robinRealWeight 1 t :=
    Robin1984.robinRealWeight_nonneg htOne
  have hInvLog : 1 / Real.log t <= 1 / Real.log x :=
    one_div_le_one_div_of_le hLogX (Real.log_le_log hxPos ht)
  have hPow : t ^ (-2 : Real) = Inv.inv (t ^ (2 : Nat)) := by
    rw [Real.rpow_neg htPos.le]
    norm_num
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWeight]
  calc
    _ <= (Real.log N * Real.log t / Real.log 2) *
        Robin1984.robinRealWeight 1 t := mul_le_mul_of_nonneg_right hStep hWeight
    _ = (Real.log N / Real.log 2) * (1 + 1 / Real.log t) * t ^ (-2 : Real) := by
      rw [quadraticDedekindRealWeight_one_eq_nicolasTailKernel htOne, hPow]
      unfold quadraticDedekindNicolasTailKernel
      field_simp [htPos.ne', hLogT.ne', hLogTwo.ne']
    _ <= (Real.log N / Real.log 2) * (1 + 1 / Real.log x) * t ^ (-2 : Real) := by
      apply mul_le_mul_of_nonneg_right
      next =>
        exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hLogN hLogTwo.le)
      next =>
        exact Real.rpow_nonneg htPos.le _
    _ = _ := by ring

/-- The weighted Chebyshev difference is integrable for every character,
including principal characters. This does not split either divergent
uncentered principal endpoint integral. -/
theorem integrableOn_imprimitiveChebyshevStep_mul_weight
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Real} (hx : 3 <= x) :
    IntegrableOn (fun t : Real =>
      (characterChebyshevSum (Nat.floor t) chi -
        characterChebyshevSum (Nat.floor t) chi.primitiveCharacter) *
          (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
  have hxPos : 0 < x := by linarith
  let C : Real := Real.log N / Real.log 2 * (1 + 1 / Real.log x)
  have hMajor : IntegrableOn (fun t : Real => C * t ^ (-2 : Real)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : Real) < -1) hxPos).const_mul C
  have hFirst : Measurable (fun t : Real => characterChebyshevSum (Nat.floor t) chi) :=
    (measurable_of_countable (fun k : Nat => characterChebyshevSum k chi)).comp Nat.measurable_floor
  have hSecond : Measurable
      (fun t : Real => characterChebyshevSum (Nat.floor t) chi.primitiveCharacter) :=
    (measurable_of_countable (fun k : Nat =>
      characterChebyshevSum k chi.primitiveCharacter)).comp Nat.measurable_floor
  have hWeight : Measurable (fun t : Real => (Robin1984.robinRealWeight 1 t : Complex)) := by
    unfold Robin1984.robinRealWeight
    fun_prop
  apply hMajor.mono' ((hFirst.sub hSecond).mul hWeight).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_imprimitiveChebyshevStep_mul_weight_le chi hx ht.le

/-- An unconditional explicit inverse-cutoff estimate for the actual complete
change-of-level endpoint correction. -/
theorem norm_dirichletWeightedIntegral_sub_primitive_le
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Not (chi = 1)) {x : Real} (hx : 3 <= x) :
    norm (dirichletCharacterWeightedIntegral chi 1 x -
      dirichletCharacterWeightedIntegral chi.primitiveCharacter 1 x) <=
        (Real.log N / Real.log 2 * (1 + 1 / Real.log x)) / x := by
  have hxPos : 0 < x := by linarith
  let C : Real := Real.log N / Real.log 2 * (1 + 1 / Real.log x)
  have hMajor : IntegrableOn (fun t : Real => C * t ^ (-2 : Real)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : Real) < -1) hxPos).const_mul C
  rw [dirichletWeightedIntegral_sub_primitive_eq chi hchi hx]
  have hBound := norm_integral_le_of_norm_le hMajor
    (show Filter.Eventually (fun t : Real =>
      norm ((characterChebyshevSum (Nat.floor t) chi -
        characterChebyshevSum (Nat.floor t) chi.primitiveCharacter) *
          (Robin1984.robinRealWeight 1 t : Complex)) <= C * t ^ (-2 : Real))
      (ae (volume.restrict (Ioi x))) from by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact norm_imprimitiveChebyshevStep_mul_weight_le chi hx ht.le)
  refine hBound.trans_eq ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : Real) < -1) hxPos]
  norm_num [C, Real.rpow_neg hxPos.le, div_eq_mul_inv]

end

end RobinBV.NumberField
