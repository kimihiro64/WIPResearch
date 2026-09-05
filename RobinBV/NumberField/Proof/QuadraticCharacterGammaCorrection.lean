import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardFactorization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivative
import Robin1984.NicolasLandau.WeightedGammaPairing
import RobinBV.NumberField.Proof.QuadraticCharacterWeightedArithmetic

/-!
# Completed quadratic L zero pairing and gamma corrections

The finite-order completed quadratic L-function has every inverse zero moment
strictly above one. Under Dirichlet ERH, the three-halves moment justifies
absolute interchange of the complete Hadamard zero series with Robin's
safe-line Mellin cutoff.
-/

open Lean Elab Tactic

elab "apply_decl_named_by_ascii_string " s:str : tactic => do
  let parts := s.getString.splitOn "."
  let name := List.foldl (fun acc part => Name.str acc part)
    Name.anonymous parts
  let id := mkIdent name
  let tacStx <- `(tactic| apply $id)
  evalTactic tacStx

namespace RobinBV.NumberField

open Complex MeasureTheory Set
open DirichletCharacter
open BombieriVinogradov.SiegelWalfisz

noncomputable section

variable {N : Nat} [NeZero N]

theorem summable_quadraticLZero_norm_inv_rpow
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {a : Real} (ha : 1 < a) :
    Summable (fun p : QuadraticLZeroIndex chi =>
      (Inv.inv (norm (quadraticLZeroValue p))) ^ a) := by
  have hMid : (1 : Real) < (1 + a) / 2 := by linarith
  have hMidNonneg : (0 : Real) <= (1 + a) / 2 := by linarith
  have hMidLt : (1 + a) / 2 < a := by linarith
  apply_decl_named_by_ascii_string "Complex.Hadamard.summable_norm_inv_rpow_divisorZeroIndex\u2080_of_growth"
  next => exact hMidNonneg
  next => exact hMidLt
  next =>
    exact (symmetricCompletedLFunction_entireOfOrderAtMost_one
      hchi hPrimitive).differentiable
  next =>
    exact Exists.intro 2 (symmetricCompletedLFunction_two_ne_zero hchi)
  next =>
    exact (symmetricCompletedLFunction_entireOfOrderAtMost_one
      hchi hPrimitive).exists_log_growth hMid hMidNonneg

theorem summable_integral_norm_quadraticL_paired_atoms
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi)
    {H : Real -> Complex} (hH : Integrable H)
    {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) +
        (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    Summable (fun p : QuadraticLZeroIndex chi =>
      integral volume (fun t : Real => norm (H t *
        (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I -
          quadraticLZeroValue p) + 1 / quadraticLZeroValue p)))) := by
  let K : Real -> Real -> Real := fun a t =>
    (Inv.inv (norm ((a : Complex) +
      (t : Complex) * Complex.I))) ^ (3 / 2 : Real)
  let F : QuadraticLZeroIndex chi -> Real -> Complex := fun p t =>
    H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I -
      quadraticLZeroValue p) + 1 / quadraticLZeroValue p)
  have hKLeft : Integrable (K (3 / 2)) :=
    Robin1984.integrable_three_halves_verticalLine (by norm_num)
  have hKRight : Integrable (K 1) :=
    Robin1984.integrable_three_halves_verticalLine le_rfl
  have hF : forall p : QuadraticLZeroIndex chi, Integrable (F p) := by
    intro p
    exact Robin1984.integrable_paired_xi_atom hH
      (quadraticLZeroValue_re_eq_half_of_dirichletERH
        hchi hPrimitive hERH p)
  have hMajorIntegral : forall p : QuadraticLZeroIndex chi,
      integral volume (fun t : Real => norm (F p t)) <=
        (2 * C *
          (integral volume (K (3 / 2)) + integral volume (K 1))) *
          (Inv.inv (norm (quadraticLZeroValue p))) ^
            (3 / 2 : Real) := by
    intro p
    let rho : Complex := quadraticLZeroValue p
    let W : Real := (Inv.inv (norm rho)) ^ (3 / 2 : Real)
    have hShiftInt : Integrable (fun t : Real => K 1 (t - rho.im)) :=
      hKRight.comp_sub_right rho.im
    have hMajorInt : Integrable (fun t : Real =>
        2 * C * W * (K (3 / 2) t + K 1 (t - rho.im))) :=
      (hKLeft.add hShiftInt).const_mul _
    calc
      integral volume (fun t : Real => norm (F p t)) <=
          integral volume (fun t : Real =>
            2 * C * W * (K (3 / 2) t + K 1 (t - rho.im))) := by
        apply integral_mono_ae (hF p).norm hMajorInt
        filter_upwards with t
        simpa [F, K, W, rho] using
          Robin1984.norm_paired_hadamard_atom_mul_le hC
            (quadraticLZeroValue_re_eq_half_of_dirichletERH
              hchi hPrimitive hERH p) (hBound t)
      _ = _ := by
        rw [integral_const_mul, integral_add hKLeft hShiftInt,
          integral_sub_right_eq_self]
        dsimp [W, rho]
        ring
  have hSum : Summable (fun p : QuadraticLZeroIndex chi =>
      (2 * C *
        (integral volume (K (3 / 2)) + integral volume (K 1))) *
        (Inv.inv (norm (quadraticLZeroValue p))) ^
          (3 / 2 : Real)) :=
    (summable_quadraticLZero_norm_inv_rpow
      hchi hPrimitive (by norm_num : (1 : Real) < 3 / 2)).mul_left _
  exact Summable.of_nonneg_of_le
    (fun p => integral_nonneg (fun t => norm_nonneg (F p t)))
    hMajorIntegral hSum

theorem integral_tsum_quadraticL_paired_atoms
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi)
    {H : Real -> Complex} (hH : Integrable H)
    {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) +
        (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    tsum (fun p : QuadraticLZeroIndex chi =>
      integral volume (fun t : Real =>
        H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I -
          quadraticLZeroValue p) + 1 / quadraticLZeroValue p))) =
      integral volume (fun t : Real =>
        tsum (fun p : QuadraticLZeroIndex chi =>
          H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I -
            quadraticLZeroValue p) + 1 / quadraticLZeroValue p))) := by
  have hSupport : Function.support (fun p : QuadraticLZeroIndex chi =>
      (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat)) =
      Set.univ := by
    ext p
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact pow_ne_zero _ (inv_ne_zero
      (norm_ne_zero_iff.mpr p.property))
  have hCount :=
    (summable_quadraticLZeroWeight hchi hPrimitive).countable_support
  rw [hSupport] at hCount
  letI : Countable (QuadraticLZeroIndex chi) :=
    Set.countable_univ_iff.mp hCount
  exact integral_tsum_of_summable_integral_norm
    (fun p => Robin1984.integrable_paired_xi_atom hH
      (quadraticLZeroValue_re_eq_half_of_dirichletERH
        hchi hPrimitive hERH p))
    (summable_integral_norm_quadraticL_paired_atoms
      hchi hPrimitive hERH hH hC hBound)

theorem quadraticCharacter_robinCutoffMellin_complete_zero_pairing
    (D : NumberField.OddFundamentalDiscriminant)
    (hERH : DirichletERH D.character)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (Robin1984.robinCutoffMellinTest n x)
              ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
            tsum (fun p : QuadraticLZeroIndex D.character =>
              1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I -
                quadraticLZeroValue p) +
              1 / quadraticLZeroValue p)) =
      tsum (fun p : QuadraticLZeroIndex D.character =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) x /
          quadraticLZeroValue p) := by
  choose C hC hBound using
    Robin1984.exists_robinCutoffMellin_safeLine_majorant hn hx
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcLt : (3 / 2 : Real) < n := by linarith
  let H : Real -> Complex := fun t =>
    mellin (Robin1984.robinCutoffMellinTest n x)
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using!
      Robin1984.verticalIntegrable_mellin_robinCutoffMellinTest
        hnOne hx (by norm_num : (0 : Real) < 3 / 2) hcLt
  have hSwap :=
    integral_tsum_quadraticL_paired_atoms
      (quadraticCharacter_ne_one D) D.character_isPrimitive hERH
      hH hC hBound
  have hIntegral : integral volume (fun t : Real => H t *
      tsum (fun p : QuadraticLZeroIndex D.character =>
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I -
          quadraticLZeroValue p) +
        1 / quadraticLZeroValue p)) =
      tsum (fun p : QuadraticLZeroIndex D.character =>
        integral volume (fun t : Real =>
          H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I -
            quadraticLZeroValue p) +
          1 / quadraticLZeroValue p))) := by
    rw [hSwap]
    apply integral_congr_ae
    filter_upwards with t
    rw [tsum_mul_left]
  change (((1 / (2 * Real.pi) : Real) : Complex)) *
    integral volume (fun t : Real => H t *
      tsum (fun p : QuadraticLZeroIndex D.character =>
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I -
          quadraticLZeroValue p) +
        1 / quadraticLZeroValue p)) = _
  rw [hIntegral, <- tsum_mul_left]
  apply tsum_congr
  intro p
  have hRe :=
    quadraticLZeroValue_re_eq_half_of_dirichletERH
      (quadraticCharacter_ne_one D) D.character_isPrimitive hERH p
  simpa [H] using!
    Robin1984.robinCutoffMellin_paired_zero_atom
      hnOne hx (by norm_num : (0 : Real) < 3 / 2) hcLt
      p.property
      (by rw [hRe]; norm_num :
        (quadraticLZeroValue p).re < (3 / 2 : Real))

theorem logDeriv_gammaFactor_of_even_eq_shifted
    {chi : DirichletCharacter Complex N}
    (hEven : DirichletCharacter.Even chi)
    {s : Complex} (hs : 0 < s.re) :
    logDeriv chi.gammaFactor s =
      -(Real.log Real.pi : Complex) / 2 -
        (Real.eulerMascheroniConstant : Complex) / 2 +
        ((1 / 2 : Complex) * Complex.digamma (s / 2 + 1) +
          (Real.eulerMascheroniConstant : Complex) / 2) -
        1 / s := by
  have hPoles : forall k : Nat, Not (s / 2 = -(k : Complex)) := by
    intro k h
    have hRe := congrArg Complex.re h
    simp at hRe
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have hRec := Complex.digamma_apply_add_one (s / 2) hPoles
  rw [logDeriv_gammaFactor_of_even hEven hs, hRec]
  have hsZero : Not (s = 0) := by
    intro h
    rw [h] at hs
    norm_num at hs
  field_simp [hsZero]
  ring

def quadraticCharacterEvenOriginCorrection
    (n : Nat) (x : Real) : Complex :=
  (((1 / (2 * Real.pi) : Real) : Complex)) *
    integral volume (fun t : Real =>
      mellin (Robin1984.robinCutoffMellinTest n x)
          ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
        ((3 / 2 : Complex) + (t : Complex) * Complex.I))

theorem quadraticCharacter_even_gamma_pairing
    {chi : DirichletCharacter Complex N}
    (hEven : DirichletCharacter.Even chi)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (Robin1984.robinCutoffMellinTest n x)
              ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
            logDeriv chi.gammaFactor
              ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
      (-(Real.log Real.pi : Complex) / 2 -
          (Real.eulerMascheroniConstant : Complex) / 2) *
        Robin1984.robinCutoffMellinTest n x 1 +
      tsum (fun k : Nat =>
        Robin1984.robinZeroKernel n
            (-(2 * ((k : Complex) + 1))) x /
          (2 * ((k : Complex) + 1))) -
      quadraticCharacterEvenOriginCorrection n x := by
  choose C hC hBound using
    Robin1984.exists_robinCutoffMellin_safeLine_majorant hn hx
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcPos : (0 : Real) < 3 / 2 := by norm_num
  have hcLt : (3 / 2 : Real) < n := by linarith
  let K : Complex := (((1 / (2 * Real.pi) : Real) : Complex))
  let H : Real -> Complex := fun t =>
    mellin (Robin1984.robinCutoffMellinTest n x)
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let C0 : Complex :=
    -(Real.log Real.pi : Complex) / 2 -
      (Real.eulerMascheroniConstant : Complex) / 2
  let G : Real -> Complex := fun t =>
    H t * ((1 / 2 : Complex) * Complex.digamma
      (((3 / 2 : Complex) + (t : Complex) * Complex.I) / 2 + 1) +
        (Real.eulerMascheroniConstant : Complex) / 2)
  let O : Real -> Complex := fun t =>
    H t / ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using!
      Robin1984.verticalIntegrable_mellin_robinCutoffMellinTest
        hnOne hx hcPos hcLt
  have hG : Integrable G := by
    simpa [G, H] using!
      Robin1984.integrable_shifted_gamma_test hH hC hBound
  have hO : Integrable O := by
    simpa [O] using!
      Robin1984.integrable_vertical_resolvent hH
        (c := (3 / 2 : Real)) (rho := 0) (by norm_num)
  have hConst : Integrable (fun t : Real => C0 * H t) :=
    hH.const_mul C0
  have hSource : forall t : Real,
      H t * logDeriv chi.gammaFactor
        ((3 / 2 : Complex) + (t : Complex) * Complex.I) =
      C0 * H t + G t - O t := by
    intro t
    rw [logDeriv_gammaFactor_of_even_eq_shifted hEven
      (by norm_num)]
    dsimp only [C0, G, O]
    ring
  have hIntegral :
      integral volume (fun t : Real =>
        H t * logDeriv chi.gammaFactor
          ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
        C0 * integral volume H + integral volume G -
          integral volume O := by
    calc
      _ = integral volume (fun t : Real =>
          C0 * H t + G t - O t) :=
        integral_congr_ae (Filter.Eventually.of_forall hSource)
      _ = _ := by
        have hSub := integral_sub (hConst.add hG) hO
        have hAdd := integral_add hConst hG
        simp only [Pi.add_apply, Pi.sub_apply] at hSub hAdd
        rw [hSub, hAdd, integral_const_mul]
  have hAtOne :
      K * integral volume H =
        Robin1984.robinCutoffMellinTest n x 1 := by
    have h := Robin1984.mellinInv_mellin_robinCutoffMellinTest
      hnOne hx hcPos hcLt Real.zero_lt_one
    simpa [mellinInv, RCLike.real_smul_eq_coe_mul,
      smul_eq_mul, H, K] using! h
  have hGamma :
      K * integral volume G =
        tsum (fun k : Nat =>
          Robin1984.robinZeroKernel n
              (-(2 * ((k : Complex) + 1))) x /
            (2 * ((k : Complex) + 1))) := by
    simpa [K, G, H] using!
      Robin1984.robinCutoffMellin_complete_gamma_pairing hn hx
  have hOrigin :
      K * integral volume O =
        quadraticCharacterEvenOriginCorrection n x := by
    rfl
  change K * integral volume (fun t : Real =>
    H t * logDeriv chi.gammaFactor
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)) = _
  rw [hIntegral]
  rw [show K * (C0 * integral volume H + integral volume G -
      integral volume O) =
    C0 * (K * integral volume H) + K * integral volume G -
      K * integral volume O by ring]
  rw [hAtOne, hGamma, hOrigin]

end

end RobinBV.NumberField
