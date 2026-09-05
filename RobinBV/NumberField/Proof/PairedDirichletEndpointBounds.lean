import RobinBV.NumberField.Helpers.RobinEndpointRemainder
import RobinBV.NumberField.Proof.PairedDirichletEndpoint

/-!
# Explicit parity-sensitive paired endpoint corrections

Both constants are explicit in the conductor and the single-character zero
mass. The even correction has a reciprocal term from the origin, whereas the
odd correction keeps a full logarithmic gain. The endpoint transfer retains
its asymptotically unit coefficient.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open Complex MeasureTheory Set

noncomputable section

/-- Explicit even-parity coefficient for the logarithmic remainder. -/
def pairedDirichletEvenRemainderConstant (N : Nat) (Z : Real) : Real :=
  abs (Real.log N + Z - Real.eulerMascheroniConstant - Real.log Real.pi) +
    4 * Real.log (2 * Real.pi) + 1

/-- Explicit odd-parity coefficient, retaining the exact gamma constant. -/
def pairedDirichletOddRemainderConstant (N : Nat) (Z : Real) : Real :=
  norm (((Real.log N + Z - Real.eulerMascheroniConstant - Real.log Real.pi : Real) :
    Complex) + 2 * quadraticOddGammaConstant) + 2

theorem pairedDirichletEvenRemainderConstant_nonneg (N : Nat) (Z : Real) :
    0 <= pairedDirichletEvenRemainderConstant N Z := by
  have hLog : 0 <= Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  unfold pairedDirichletEvenRemainderConstant
  positivity

theorem pairedDirichletOddRemainderConstant_nonneg (N : Nat) (Z : Real) :
    0 <= pairedDirichletOddRemainderConstant N Z := by
  unfold pairedDirichletOddRemainderConstant
  positivity

/-- The full paired even remainder has an explicit two-scale majorant. -/
theorem norm_pairedDirichletEvenWeightedRemainder_two_le
    (N : Nat) (Z : Real) {x : Real} (hx : 2 <= x) :
    norm (pairedDirichletEvenWeightedRemainder N Z 2 x) <=
      x ^ (-(2 : Real)) * (2 + pairedDirichletEvenRemainderConstant N Z / Real.log x) := by
  let A : Complex :=
    ((Real.log N + Z - Real.eulerMascheroniConstant - Real.log Real.pi : Real) : Complex)
  let T : Complex := Robin1984.robinCutoffMellinTest 2 x 1
  let S : Complex := tsum (fun k : Nat =>
    Robin1984.robinZeroKernel 2 (-(2 * ((k : Complex) + 1))) x /
      (2 * ((k : Complex) + 1)))
  let O : Complex := quadraticCharacterEvenOriginCorrection 2 x
  change norm (A * T + 2 * S - 2 * O) <= _
  have hT := norm_robinCutoffMellinTest_two_one_eq (by linarith : 1 < x)
  have hS := norm_tsum_quadraticNegativeEvenKernels_two_le hx
  have hO := norm_quadraticCharacterEvenOriginCorrection_le (by linarith : 1 < x)
  have hTwo : norm (2 : Complex) = (2 : Real) := by norm_num
  calc
    _ <= (norm (A * T) + norm (2 * S)) + norm (2 * O) :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = norm A * (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) +
        2 * norm S + 2 * norm O := by
      rw [norm_mul, norm_mul, norm_mul, hTwo, hT]
    _ <= norm A * (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) +
        2 * (2 * Real.log (2 * Real.pi) * x ^ (-(2 : Real)) * Inv.inv (Real.log x)) +
        2 * (x ^ (-(2 : Real)) + (x ^ (-(2 : Real)) / 2) * Inv.inv (Real.log x)) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hS (by norm_num)))
        (mul_le_mul_of_nonneg_left hO (by norm_num))
    _ = _ := by
      dsimp only [A, pairedDirichletEvenRemainderConstant]
      rw [Complex.norm_real, Real.norm_eq_abs]
      ring

/-- The odd remainder has no reciprocal-square origin term. -/
theorem norm_pairedDirichletOddWeightedRemainder_two_le
    (N : Nat) (Z : Real) {x : Real} (hx : 2 <= x) :
    norm (pairedDirichletOddWeightedRemainder N Z 2 x) <=
      x ^ (-(2 : Real)) * (pairedDirichletOddRemainderConstant N Z / Real.log x) := by
  let A : Complex :=
    ((Real.log N + Z - Real.eulerMascheroniConstant - Real.log Real.pi : Real) : Complex) +
      2 * quadraticOddGammaConstant
  let T : Complex := Robin1984.robinCutoffMellinTest 2 x 1
  let S : Complex := tsum (fun k : Nat =>
    Robin1984.robinZeroKernel 2 (-(2 * (k : Complex) + 1)) x / (2 * (k : Complex) + 1))
  have hForm : pairedDirichletOddWeightedRemainder N Z 2 x = A * T + 2 * S := by
    unfold pairedDirichletOddWeightedRemainder
    dsimp only [A, T, S]
    ring
  rw [hForm]
  have hT := norm_robinCutoffMellinTest_two_one_eq (by linarith : 1 < x)
  have hS := norm_tsum_quadraticNegativeOddKernels_two_le_explicit hx
  have hTwo : norm (2 : Complex) = (2 : Real) := by norm_num
  calc
    _ <= norm (A * T) + norm (2 * S) := norm_add_le _ _
    _ = norm A * (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) + 2 * norm S := by
      rw [norm_mul, norm_mul, hTwo, hT]
    _ <= norm A * (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) +
        2 * (x ^ (-(2 : Real)) * Inv.inv (Real.log x)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hS (by norm_num))
    _ = _ := by dsimp only [A, pairedDirichletOddRemainderConstant]; ring

/-- Explicit endpoint bound for the complete even paired correction. -/
theorem norm_pairedDirichletEvenEndpointCorrection_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hEven : DirichletCharacter.Even chi) (hERH : DirichletERH chi)
    {x : Real} (hx : 3 <= x) :
    norm (dirichletEndpointCorrection
      (pairedDirichletEvenWeightedRemainder N (quadraticLZeroMass chi) 2) x) <=
      (1 + 1 / (2 * Real.log x + 1)) *
        (2 + pairedDirichletEvenRemainderConstant N (quadraticLZeroMass chi) / Real.log x) *
          x ^ (-(1 : Real)) := by
  have hInt := (pairedDirichletWeightedIntegral_one_eq_even_explicit
    hchi hPrimitive hEven hERH hx).1
  exact norm_robinEndpointReweight_remainder_le (by linarith)
    (by norm_num : (0 : Real) <= 2)
    (pairedDirichletEvenRemainderConstant_nonneg N (quadraticLZeroMass chi))
    (fun t ht => norm_pairedDirichletEvenWeightedRemainder_two_le N _
      (le_trans (by linarith : 2 <= x) ht)) hInt

/-- Odd parity retains the extra logarithmic decay at exponent one. -/
theorem norm_pairedDirichletOddEndpointCorrection_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hOdd : DirichletCharacter.Odd chi) (hERH : DirichletERH chi)
    {x : Real} (hx : 3 <= x) :
    norm (dirichletEndpointCorrection
      (pairedDirichletOddWeightedRemainder N (quadraticLZeroMass chi) 2) x) <=
      (1 + 1 / (2 * Real.log x + 1)) *
        (pairedDirichletOddRemainderConstant N (quadraticLZeroMass chi) / Real.log x) *
          x ^ (-(1 : Real)) := by
  have hInt := (pairedDirichletWeightedIntegral_one_eq_odd_explicit
    hchi hPrimitive hOdd hERH hx).1
  have hBound := norm_robinEndpointReweight_remainder_le (by linarith : 1 < x)
    (B := 0) (by norm_num) (pairedDirichletOddRemainderConstant_nonneg N (quadraticLZeroMass chi))
    (R := pairedDirichletOddWeightedRemainder N (quadraticLZeroMass chi) 2)
    (fun t ht => by
      simpa only [zero_add] using norm_pairedDirichletOddWeightedRemainder_two_le N
        (quadraticLZeroMass chi) (le_trans (by linarith : 2 <= x) ht)) hInt
  simpa only [zero_add, dirichletEndpointCorrection] using hBound

end

end RobinBV.NumberField
