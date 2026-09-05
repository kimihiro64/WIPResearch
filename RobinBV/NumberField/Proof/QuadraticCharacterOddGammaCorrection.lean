import RobinBV.NumberField.Proof.QuadraticCharacterGammaCorrection

/-!
# Odd quadratic-character gamma correction

The odd gamma factor is expanded into its constant and regularized atoms.
The resulting absolutely convergent series is paired termwise with Robin's
Mellin cutoff.
-/

namespace RobinBV.NumberField

open Complex MeasureTheory Set
open DirichletCharacter
open BombieriVinogradov.SiegelWalfisz

noncomputable section

variable {N : Nat} [NeZero N]

def quadraticOddGammaConstantAtom (k : Nat) : Complex :=
  1 / (2 * ((k : Complex) + 1)) -
    1 / (2 * (k : Complex) + 1)

def quadraticOddGammaConstant : Complex :=
  tsum quadraticOddGammaConstantAtom

theorem norm_quadraticOddGammaConstantAtom_le
    (k : Nat) :
    norm (quadraticOddGammaConstantAtom k) <=
      (Inv.inv ((k : Real) + 1)) ^ (2 : Real) := by
  have hk : 0 <= (k : Real) := Nat.cast_nonneg k
  have hLeftPos : 0 < ((k : Real) + 1) ^ (2 : Nat) := by
    positivity
  have hRightPos :
      0 < (2 * ((k : Real) + 1)) * (2 * (k : Real) + 1) := by
    positivity
  have hDen :
      ((k : Real) + 1) ^ (2 : Nat) <=
        (2 * ((k : Real) + 1)) * (2 * (k : Real) + 1) := by
    nlinarith
  have hInv :
      1 / ((2 * ((k : Real) + 1)) * (2 * (k : Real) + 1)) <=
        1 / (((k : Real) + 1) ^ (2 : Nat)) :=
    one_div_le_one_div_of_le hLeftPos hDen
  have hkOne : Not ((k : Real) + 1 = 0) := by positivity
  have hTwoKOne : Not (2 * (k : Real) + 1 = 0) := by positivity
  have hOddDen : Not (1 + (k : Real) * 2 = 0) := by positivity
  have hOddDenC : Not ((1 : Complex) + (k : Complex) * 2 = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    linarith
  have hEq :
      quadraticOddGammaConstantAtom k =
        ((-1 / ((2 * ((k : Real) + 1)) *
          (2 * (k : Real) + 1)) : Real) : Complex) := by
    unfold quadraticOddGammaConstantAtom
    push_cast
    field_simp [hkOne, hTwoKOne, hOddDen, hOddDenC]
    ring_nf
    field_simp [hOddDenC]
    ring
  rw [hEq, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_neg, abs_one, abs_of_pos hRightPos]
  simpa [Real.rpow_two, one_div, inv_pow] using hInv

theorem summable_quadraticOddGammaConstantAtom :
    Summable quadraticOddGammaConstantAtom := by
  have hBase : Summable (fun k : Nat =>
      (Inv.inv ((k : Real) + 1)) ^ (2 : Real)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (2 : Real)).mpr
      (by norm_num)
    apply h.congr
    intro k
    rw [abs_of_pos (by positivity : (0 : Real) < k + 1),
      one_div, Real.inv_rpow (by positivity)]
  exact hBase.of_norm_bounded
    norm_quadraticOddGammaConstantAtom_le

def quadraticOddGammaRegularizedAtom
    (k : Nat) (s : Complex) : Complex :=
  1 / (2 * (k : Complex) + 1) -
    1 / (s + (2 * (k : Complex) + 1))

def quadraticOddGammaAtom
    (k : Nat) (s : Complex) : Complex :=
  1 / (2 * ((k : Complex) + 1)) -
    1 / (s + (2 * (k : Complex) + 1))

theorem quadraticOddGammaAtom_eq
    (k : Nat) (s : Complex) :
    quadraticOddGammaAtom k s =
      quadraticOddGammaConstantAtom k +
        quadraticOddGammaRegularizedAtom k s := by
  unfold quadraticOddGammaAtom quadraticOddGammaConstantAtom
  unfold quadraticOddGammaRegularizedAtom
  ring

theorem norm_quadraticOddGammaRegularizedAtom_mul_le
    {C : Real} (hC : 0 <= C) {z : Complex} {t : Real} (k : Nat)
    (hz : norm z <= C *
      (Inv.inv (norm ((3 / 2 : Complex) +
        (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    norm (z * quadraticOddGammaRegularizedAtom k
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)) <=
      4 * C * (Inv.inv ((k : Real) + 1)) ^ (3 / 2 : Real) *
        (Inv.inv (norm ((3 / 2 : Complex) +
          (t : Complex) * Complex.I))) ^ (3 / 2 : Real) := by
  let s : Complex := (3 / 2 : Complex) +
    (t : Complex) * Complex.I
  let u : Real := 2 * (k : Real) + 1
  let rho : Complex := -(u : Complex)
  have hk : 0 < (k : Real) + 1 := by positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have huCast : (u : Complex) =
      2 * (k : Complex) + 1 := by
    dsimp [u]
    push_cast
    ring
  have hsRe : s.re = (3 / 2 : Real) := by simp [s]
  have hRhoRe : rho.re = -u := by simp [rho]
  have hsZero : Not (s = 0) := by
    intro h
    rw [h] at hsRe
    norm_num at hsRe
  have hRhoZero : Not (rho = 0) := by
    intro h
    rw [h] at hRhoRe
    simp at hRhoRe
    linarith
  have hSubZero : Not (s - rho = 0) := by
    intro h
    have hReal := congrArg Complex.re h
    simp only [Complex.sub_re, hsRe, hRhoRe,
      Complex.zero_re] at hReal
    linarith
  have hsNorm : 0 < norm s := norm_pos_iff.mpr hsZero
  have hRhoNorm : norm rho = u := by
    simp [rho, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hu]
  have hNormLe : norm s <= norm (s - rho) := by
    have hSquare :
        norm s ^ (2 : Nat) <= norm (s - rho) ^ (2 : Nat) := by
      rw [Complex.sq_norm, Complex.sq_norm,
        Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, hsRe, hRhoRe]
      have hRhoIm : rho.im = 0 := by simp [rho]
      rw [hRhoIm]
      nlinarith
    nlinarith [norm_nonneg s, norm_nonneg (s - rho)]
  have hInvB :
      Inv.inv (norm (s - rho)) <= Inv.inv (norm s) := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hsNorm hNormLe
  have hWeightB :
      (Inv.inv (norm (s - rho))) ^ (3 / 2 : Real) <=
        (Inv.inv (norm s)) ^ (3 / 2 : Real) :=
    Real.rpow_le_rpow (by positivity) hInvB (by norm_num)
  have hInvU : Inv.inv u <= Inv.inv ((k : Real) + 1) := by
    have hku : (k : Real) + 1 <= u := by
      dsimp [u]
      linarith
    simpa only [one_div] using
      one_div_le_one_div_of_le hk hku
  have hWeightU :
      (Inv.inv u) ^ (3 / 2 : Real) <=
        (Inv.inv ((k : Real) + 1)) ^ (3 / 2 : Real) :=
    Real.rpow_le_rpow (by positivity) hInvU (by norm_num)
  have hAtom :
      z * (1 / (u : Complex) - 1 / (s + (u : Complex))) =
        -(z * (1 / (s - rho) + 1 / rho)) := by
    dsimp [rho]
    simp only [sub_neg_eq_add, div_neg]
    ring
  unfold quadraticOddGammaRegularizedAtom
  rw [<- huCast]
  change norm (z *
    (1 / (u : Complex) - 1 / (s + (u : Complex)))) <= _
  rw [hAtom, norm_neg]
  have hGeneric :=
    Robin1984.norm_regularized_resolvent_mul_le
      hsZero hRhoZero hSubZero hC hz
  rw [hRhoNorm] at hGeneric
  apply hGeneric.trans
  calc
    2 * C * (Inv.inv u) ^ (3 / 2 : Real) *
        ((Inv.inv (norm s)) ^ (3 / 2 : Real) +
          (Inv.inv (norm (s - rho))) ^ (3 / 2 : Real)) <=
      2 * C * (Inv.inv ((k : Real) + 1)) ^ (3 / 2 : Real) *
        ((Inv.inv (norm s)) ^ (3 / 2 : Real) +
          (Inv.inv (norm s)) ^ (3 / 2 : Real)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hWeightU (by positivity))
        (add_le_add le_rfl hWeightB)
        (by positivity) (by positivity)
    _ = _ := by ring

theorem integrable_quadraticOddGammaRegularizedAtom
    {H : Real -> Complex} (hH : Integrable H) (k : Nat) :
    Integrable (fun t : Real => H t *
      quadraticOddGammaRegularizedAtom k
        ((3 / 2 : Complex) + (t : Complex) * Complex.I)) := by
  have hRho :
      (-(2 * (k : Complex) + 1)).re < (3 / 2 : Real) := by
    simp
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have hR : Integrable (fun t : Real =>
      H t / ((3 / 2 : Complex) + (t : Complex) * Complex.I +
        (2 * (k : Complex) + 1))) := by
    have hRaw := Robin1984.integrable_vertical_resolvent hH
      (c := (3 / 2 : Real))
      (rho := -(2 * (k : Complex) + 1)) hRho
    apply hRaw.congr
    filter_upwards with t
    congr 1
    norm_num
    ring
  apply ((hH.div_const (2 * (k : Complex) + 1)).sub hR).congr
  filter_upwards with t
  unfold quadraticOddGammaRegularizedAtom
  simp only [Pi.sub_apply]
  ring

theorem summable_integral_norm_quadraticOddGammaRegularizedAtoms
    {H : Real -> Complex} (hH : Integrable H)
    {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) +
        (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    Summable (fun k : Nat =>
      integral volume (fun t : Real => norm (H t *
        quadraticOddGammaRegularizedAtom k
          ((3 / 2 : Complex) + (t : Complex) * Complex.I)))) := by
  let K : Real -> Real := fun t =>
    (Inv.inv (norm ((3 / 2 : Complex) +
      (t : Complex) * Complex.I))) ^ (3 / 2 : Real)
  let W : Nat -> Real := fun k =>
    (Inv.inv ((k : Real) + 1)) ^ (3 / 2 : Real)
  let F : Nat -> Real -> Complex := fun k t =>
    H t * quadraticOddGammaRegularizedAtom k
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  have hK : Integrable K := by
    simpa [K] using!
      Robin1984.integrable_three_halves_verticalLine
        (by norm_num : (1 : Real) <= 3 / 2)
  have hW : Summable W := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).mpr
      (by norm_num)
    apply h.congr
    intro k
    dsimp [W]
    rw [abs_of_pos (by positivity : (0 : Real) < k + 1),
      one_div, Real.inv_rpow (by positivity)]
  have hMajor : forall k : Nat,
      integral volume (fun t : Real => norm (F k t)) <=
        (4 * C * integral volume K) * W k := by
    intro k
    have hF : Integrable (F k) :=
      integrable_quadraticOddGammaRegularizedAtom hH k
    have hM : Integrable (fun t : Real =>
        4 * C * W k * K t) := hK.const_mul _
    calc
      integral volume (fun t : Real => norm (F k t)) <=
          integral volume (fun t : Real =>
            4 * C * W k * K t) := by
        apply integral_mono_ae hF.norm hM
        filter_upwards with t
        exact
          norm_quadraticOddGammaRegularizedAtom_mul_le
            hC k (hBound t)
      _ = _ := by
        rw [integral_const_mul]
        ring
  exact Summable.of_nonneg_of_le
    (fun k => integral_nonneg
      (fun t => norm_nonneg (F k t)))
    hMajor (hW.mul_left _)

theorem half_digamma_odd_eq_gammaAtoms
    {s : Complex} (hs : 1 < s.re) :
    (1 / 2 : Complex) * Complex.digamma ((s + 1) / 2) =
      -(Real.eulerMascheroniConstant : Complex) / 2 +
        tsum (fun k : Nat => quadraticOddGammaAtom k s) := by
  have hPole : forall k : Nat,
      Not ((s + 1) / 2 = -(k : Complex)) := by
    intro k h
    have hRe := congrArg Complex.re h
    simp at hRe
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  rw [Complex.digamma_eq_tsum hPole, mul_add]
  have hConstant :
      (1 / 2 : Complex) *
          -(Real.eulerMascheroniConstant : Complex) =
        -(Real.eulerMascheroniConstant : Complex) / 2 := by
    ring
  rw [hConstant, <- tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  unfold quadraticOddGammaAtom
  have hkOne : Not ((k : Complex) + 1 = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have hDen :
      Not (s + (2 * (k : Complex) + 1) = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  rw [show (k : Complex) + (s + 1) / 2 =
    (s + (2 * (k : Complex) + 1)) / 2 by ring]
  field_simp [hkOne, hDen]

theorem integrable_quadraticOddGammaAtom
    {H : Real -> Complex} (hH : Integrable H) (k : Nat) :
    Integrable (fun t : Real => H t *
      quadraticOddGammaAtom k
        ((3 / 2 : Complex) + (t : Complex) * Complex.I)) := by
  have hConst : Integrable (fun t : Real =>
      quadraticOddGammaConstantAtom k * H t) :=
    hH.const_mul _
  have hRegular :
      Integrable (fun t : Real => H t *
        quadraticOddGammaRegularizedAtom k
          ((3 / 2 : Complex) + (t : Complex) * Complex.I)) :=
    integrable_quadraticOddGammaRegularizedAtom hH k
  apply (hConst.add hRegular).congr
  filter_upwards with t
  simp only [Pi.add_apply]
  rw [quadraticOddGammaAtom_eq]
  ring

theorem summable_integral_norm_quadraticOddGammaAtoms
    {H : Real -> Complex} (hH : Integrable H)
    {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) +
        (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    Summable (fun k : Nat =>
      integral volume (fun t : Real => norm (H t *
        quadraticOddGammaAtom k
          ((3 / 2 : Complex) + (t : Complex) * Complex.I)))) := by
  let FC : Nat -> Real -> Complex := fun k t =>
    quadraticOddGammaConstantAtom k * H t
  let FR : Nat -> Real -> Complex := fun k t =>
    H t * quadraticOddGammaRegularizedAtom k
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let F : Nat -> Real -> Complex := fun k t =>
    H t * quadraticOddGammaAtom k
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  have hFC (k : Nat) : Integrable (FC k) := hH.const_mul _
  have hFR (k : Nat) : Integrable (FR k) :=
    integrable_quadraticOddGammaRegularizedAtom hH k
  have hF (k : Nat) : Integrable (F k) :=
    integrable_quadraticOddGammaAtom hH k
  have hConstNorm : Summable (fun k : Nat =>
      integral volume (fun t : Real => norm (FC k t))) := by
    have hWeights :=
      summable_quadraticOddGammaConstantAtom.norm
    have hScaled := hWeights.mul_right
      (integral volume (fun t : Real => norm (H t)))
    apply hScaled.congr
    intro k
    dsimp [FC]
    rw [show (fun t : Real =>
        norm (quadraticOddGammaConstantAtom k * H t)) =
      (fun t : Real =>
        norm (quadraticOddGammaConstantAtom k) * norm (H t)) by
          funext t
          rw [norm_mul],
      integral_const_mul]
  have hRegularNorm : Summable (fun k : Nat =>
      integral volume (fun t : Real => norm (FR k t))) := by
    simpa [FR] using!
      summable_integral_norm_quadraticOddGammaRegularizedAtoms
        hH hC hBound
  have hMajor (k : Nat) :
      integral volume (fun t : Real => norm (F k t)) <=
        integral volume (fun t : Real => norm (FC k t)) +
          integral volume (fun t : Real => norm (FR k t)) := by
    calc
      integral volume (fun t : Real => norm (F k t)) <=
          integral volume (fun t : Real =>
            norm (FC k t) + norm (FR k t)) := by
        apply integral_mono_ae (hF k).norm
          ((hFC k).norm.add (hFR k).norm)
        filter_upwards with t
        have hEq : F k t = FC k t + FR k t := by
          dsimp [F, FC, FR]
          rw [quadraticOddGammaAtom_eq]
          ring
        rw [hEq]
        exact norm_add_le _ _
      _ = _ := by
        rw [integral_add (hFC k).norm (hFR k).norm]
  exact Summable.of_nonneg_of_le
    (fun k => integral_nonneg
      (fun t => norm_nonneg (F k t)))
    hMajor (hConstNorm.add hRegularNorm)

theorem integral_tsum_quadraticOddGammaAtoms
    {H : Real -> Complex} (hH : Integrable H)
    {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) +
        (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    tsum (fun k : Nat =>
      integral volume (fun t : Real => H t *
        quadraticOddGammaAtom k
          ((3 / 2 : Complex) + (t : Complex) * Complex.I))) =
      integral volume (fun t : Real =>
        tsum (fun k : Nat => H t *
          quadraticOddGammaAtom k
            ((3 / 2 : Complex) + (t : Complex) * Complex.I))) :=
  integral_tsum_of_summable_integral_norm
    (integrable_quadraticOddGammaAtom hH)
    (summable_integral_norm_quadraticOddGammaAtoms
      hH hC hBound)

theorem robinCutoffMellin_oddGammaRegularizedAtom_pairing
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    {c : Real} (hcPos : 0 < c) (hcLt : c < n)
    (k : Nat) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (Robin1984.robinCutoffMellinTest n x)
              ((c : Complex) + (t : Complex) * Complex.I) *
            quadraticOddGammaRegularizedAtom k
              ((c : Complex) + (t : Complex) * Complex.I)) =
      Robin1984.robinZeroKernel n
          (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1) := by
  let rho : Complex := -(2 * (k : Complex) + 1)
  have hRhoZero : Not (rho = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp [rho] at hRe
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have hRho : rho.re < c := by
    simp [rho]
    have hk : 0 <= (k : Real) := Nat.cast_nonneg k
    linarith
  have hPair :=
    Robin1984.robinCutoffMellin_paired_zero_atom
      hn hx hcPos hcLt hRhoZero hRho
  have hFunction : (fun t : Real =>
      mellin (Robin1984.robinCutoffMellinTest n x)
          ((c : Complex) + (t : Complex) * Complex.I) *
        quadraticOddGammaRegularizedAtom k
          ((c : Complex) + (t : Complex) * Complex.I)) =
      (fun t : Real =>
        -(mellin (Robin1984.robinCutoffMellinTest n x)
          ((c : Complex) + (t : Complex) * Complex.I) *
          (1 / ((c : Complex) + (t : Complex) * Complex.I - rho) +
            1 / rho))) := by
    funext t
    unfold quadraticOddGammaRegularizedAtom
    dsimp [rho]
    simp only [sub_neg_eq_add, div_neg]
    ring
  rw [hFunction, integral_neg, mul_neg, hPair]
  simp only [rho, div_neg, neg_neg]

theorem robinCutoffMellin_oddGammaAtom_pairing
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x)
    (k : Nat) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (Robin1984.robinCutoffMellinTest n x)
              ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
            quadraticOddGammaAtom k
              ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
      quadraticOddGammaConstantAtom k *
        Robin1984.robinCutoffMellinTest n x 1 +
      Robin1984.robinZeroKernel n
          (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1) := by
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcPos : (0 : Real) < 3 / 2 := by norm_num
  have hcLt : (3 / 2 : Real) < n := by linarith
  let K : Complex := (((1 / (2 * Real.pi) : Real) : Complex))
  let H : Real -> Complex := fun t =>
    mellin (Robin1984.robinCutoffMellinTest n x)
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let R : Real -> Complex := fun t =>
    H t * quadraticOddGammaRegularizedAtom k
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using!
      Robin1984.verticalIntegrable_mellin_robinCutoffMellinTest
        hnOne hx hcPos hcLt
  have hR : Integrable R := by
    simpa [R] using!
      integrable_quadraticOddGammaRegularizedAtom hH k
  have hConst : Integrable (fun t : Real =>
      quadraticOddGammaConstantAtom k * H t) :=
    hH.const_mul _
  have hIntegral :
      integral volume (fun t : Real =>
        H t * quadraticOddGammaAtom k
          ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
      quadraticOddGammaConstantAtom k * integral volume H +
        integral volume R := by
    calc
      _ = integral volume (fun t : Real =>
          quadraticOddGammaConstantAtom k * H t + R t) := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [R]
        rw [quadraticOddGammaAtom_eq]
        ring
      _ = _ := by
        have hAdd := integral_add hConst hR
        rw [hAdd, integral_const_mul]
  have hAtOne :
      K * integral volume H =
        Robin1984.robinCutoffMellinTest n x 1 := by
    have h := Robin1984.mellinInv_mellin_robinCutoffMellinTest
      hnOne hx hcPos hcLt Real.zero_lt_one
    simpa [mellinInv, RCLike.real_smul_eq_coe_mul,
      smul_eq_mul, H, K] using! h
  have hRegular :
      K * integral volume R =
        Robin1984.robinZeroKernel n
            (-(2 * (k : Complex) + 1)) x /
          (2 * (k : Complex) + 1) := by
    simpa [K, R, H] using!
      robinCutoffMellin_oddGammaRegularizedAtom_pairing
        hnOne hx hcPos hcLt k
  change K * integral volume (fun t : Real =>
    H t * quadraticOddGammaAtom k
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)) = _
  rw [hIntegral]
  rw [show K * (quadraticOddGammaConstantAtom k *
      integral volume H + integral volume R) =
    quadraticOddGammaConstantAtom k * (K * integral volume H) +
      K * integral volume R by ring]
  rw [hAtOne, hRegular]

theorem quadraticCharacter_odd_shifted_gamma_pairing
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (Robin1984.robinCutoffMellinTest n x)
              ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
            ((1 / 2 : Complex) * Complex.digamma
              (((3 / 2 : Complex) + (t : Complex) * Complex.I + 1) / 2) +
              (Real.eulerMascheroniConstant : Complex) / 2)) =
      quadraticOddGammaConstant *
        Robin1984.robinCutoffMellinTest n x 1 +
      tsum (fun k : Nat =>
        Robin1984.robinZeroKernel n
            (-(2 * (k : Complex) + 1)) x /
          (2 * (k : Complex) + 1)) := by
  choose C hC hBound using
    Robin1984.exists_robinCutoffMellin_safeLine_majorant hn hx
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcLt : (3 / 2 : Real) < n := by linarith
  let K : Complex := (((1 / (2 * Real.pi) : Real) : Complex))
  let H : Real -> Complex := fun t =>
    mellin (Robin1984.robinCutoffMellinTest n x)
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using!
      Robin1984.verticalIntegrable_mellin_robinCutoffMellinTest
        hnOne hx (by norm_num : (0 : Real) < 3 / 2) hcLt
  have hSwap :=
    integral_tsum_quadraticOddGammaAtoms hH hC hBound
  have hIntegral :
      integral volume (fun t : Real => H t *
        ((1 / 2 : Complex) * Complex.digamma
          (((3 / 2 : Complex) + (t : Complex) * Complex.I + 1) / 2) +
          (Real.eulerMascheroniConstant : Complex) / 2)) =
      tsum (fun k : Nat =>
        integral volume (fun t : Real => H t *
          quadraticOddGammaAtom k
            ((3 / 2 : Complex) + (t : Complex) * Complex.I))) := by
    rw [hSwap]
    apply integral_congr_ae
    filter_upwards with t
    rw [tsum_mul_left,
      half_digamma_odd_eq_gammaAtoms
        (by simp; norm_num)]
    ring
  have hRegularNorm :=
    summable_integral_norm_quadraticOddGammaRegularizedAtoms
      hH hC hBound
  have hRegularValues : Summable (fun k : Nat =>
      integral volume (fun t : Real => H t *
        quadraticOddGammaRegularizedAtom k
          ((3 / 2 : Complex) + (t : Complex) * Complex.I))) :=
    hRegularNorm.of_norm_bounded
      (fun k => norm_integral_le_integral_norm _)
  have hKernels : Summable (fun k : Nat =>
      Robin1984.robinZeroKernel n
          (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1)) := by
    apply (hRegularValues.mul_left K).congr
    intro k
    simpa [K, H] using!
      robinCutoffMellin_oddGammaRegularizedAtom_pairing
        hnOne hx (by norm_num : (0 : Real) < 3 / 2)
        hcLt k
  have hConstants : Summable (fun k : Nat =>
      quadraticOddGammaConstantAtom k *
        Robin1984.robinCutoffMellinTest n x 1) :=
    summable_quadraticOddGammaConstantAtom.mul_right _
  change K * integral volume (fun t : Real => H t *
    ((1 / 2 : Complex) * Complex.digamma
      (((3 / 2 : Complex) + (t : Complex) * Complex.I + 1) / 2) +
      (Real.eulerMascheroniConstant : Complex) / 2)) = _
  rw [hIntegral, <- tsum_mul_left]
  calc
    tsum (fun k : Nat => K * integral volume (fun t : Real =>
        H t * quadraticOddGammaAtom k
          ((3 / 2 : Complex) + (t : Complex) * Complex.I))) =
      tsum (fun k : Nat =>
        quadraticOddGammaConstantAtom k *
          Robin1984.robinCutoffMellinTest n x 1 +
        Robin1984.robinZeroKernel n
            (-(2 * (k : Complex) + 1)) x /
          (2 * (k : Complex) + 1)) := by
        apply tsum_congr
        intro k
        simpa [K, H] using!
          robinCutoffMellin_oddGammaAtom_pairing
            hn hx k
    _ = tsum (fun k : Nat =>
          quadraticOddGammaConstantAtom k *
            Robin1984.robinCutoffMellinTest n x 1) +
        tsum (fun k : Nat =>
          Robin1984.robinZeroKernel n
              (-(2 * (k : Complex) + 1)) x /
            (2 * (k : Complex) + 1)) :=
      hConstants.tsum_add hKernels
    _ = _ := by
      rw [tsum_mul_right]
      rfl

theorem quadraticCharacter_odd_gamma_pairing
    {chi : DirichletCharacter Complex N}
    (hOdd : DirichletCharacter.Odd chi)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (Robin1984.robinCutoffMellinTest n x)
              ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
            logDeriv chi.gammaFactor
              ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
      (-(Real.log Real.pi : Complex) / 2 -
          (Real.eulerMascheroniConstant : Complex) / 2 +
          quadraticOddGammaConstant) *
        Robin1984.robinCutoffMellinTest n x 1 +
      tsum (fun k : Nat =>
        Robin1984.robinZeroKernel n
            (-(2 * (k : Complex) + 1)) x /
          (2 * (k : Complex) + 1)) := by
  have hShift :=
    quadraticCharacter_odd_shifted_gamma_pairing hn hx
  have hPoint : forall t : Real,
      logDeriv chi.gammaFactor
          ((3 / 2 : Complex) + (t : Complex) * Complex.I) =
        -(Real.log Real.pi : Complex) / 2 -
          (Real.eulerMascheroniConstant : Complex) / 2 +
          ((1 / 2 : Complex) * Complex.digamma
            (((3 / 2 : Complex) + (t : Complex) * Complex.I + 1) / 2) +
            (Real.eulerMascheroniConstant : Complex) / 2) := by
    intro t
    rw [logDeriv_gammaFactor_of_odd hOdd (by norm_num)]
    ring
  rw [show (fun t : Real =>
      mellin (Robin1984.robinCutoffMellinTest n x)
          ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
        logDeriv chi.gammaFactor
          ((3 / 2 : Complex) + (t : Complex) * Complex.I)) =
    (fun t : Real =>
      mellin (Robin1984.robinCutoffMellinTest n x)
          ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
        (-(Real.log Real.pi : Complex) / 2 -
          (Real.eulerMascheroniConstant : Complex) / 2 +
          ((1 / 2 : Complex) * Complex.digamma
            (((3 / 2 : Complex) + (t : Complex) * Complex.I + 1) / 2) +
            (Real.eulerMascheroniConstant : Complex) / 2))) by
      funext t
      rw [hPoint t]]
  let K : Complex := (((1 / (2 * Real.pi) : Real) : Complex))
  let H : Real -> Complex := fun t =>
    mellin (Robin1984.robinCutoffMellinTest n x)
      ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let C0 : Complex :=
    -(Real.log Real.pi : Complex) / 2 -
      (Real.eulerMascheroniConstant : Complex) / 2
  let G : Real -> Complex := fun t =>
    H t * ((1 / 2 : Complex) * Complex.digamma
      (((3 / 2 : Complex) + (t : Complex) * Complex.I + 1) / 2) +
      (Real.eulerMascheroniConstant : Complex) / 2)
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcLt : (3 / 2 : Real) < n := by linarith
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using!
      Robin1984.verticalIntegrable_mellin_robinCutoffMellinTest
        hnOne hx (by norm_num : (0 : Real) < 3 / 2) hcLt
  have hG : Integrable G := by
    choose C hC hBound using
      Robin1984.exists_robinCutoffMellin_safeLine_majorant hn hx
    have hNorm :=
      summable_integral_norm_quadraticOddGammaAtoms
        hH hC hBound
    have hSeries := Robin1984.integrable_complex_series_of_integral_norm
      (integrable_quadraticOddGammaAtom hH) hNorm
    apply hSeries.congr
    filter_upwards with t
    dsimp only [G]
    rw [tsum_mul_left,
      half_digamma_odd_eq_gammaAtoms
        (by simp; norm_num)]
    ring
  have hConst : Integrable (fun t : Real => C0 * H t) :=
    hH.const_mul C0
  have hIntegral :
      integral volume (fun t : Real =>
        H t * (C0 +
          ((1 / 2 : Complex) * Complex.digamma
            (((3 / 2 : Complex) + (t : Complex) * Complex.I + 1) / 2) +
            (Real.eulerMascheroniConstant : Complex) / 2))) =
      C0 * integral volume H + integral volume G := by
    calc
      _ = integral volume (fun t : Real =>
          C0 * H t + G t) := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [G]
        ring
      _ = _ := by
        have hAdd := integral_add hConst hG
        rw [hAdd, integral_const_mul]
  have hAtOne :
      K * integral volume H =
        Robin1984.robinCutoffMellinTest n x 1 := by
    have h := Robin1984.mellinInv_mellin_robinCutoffMellinTest
      hnOne hx (by norm_num : (0 : Real) < 3 / 2)
      hcLt Real.zero_lt_one
    simpa [mellinInv, RCLike.real_smul_eq_coe_mul,
      smul_eq_mul, H, K] using! h
  change K * integral volume (fun t : Real =>
    H t * (C0 +
      ((1 / 2 : Complex) * Complex.digamma
        (((3 / 2 : Complex) + (t : Complex) * Complex.I + 1) / 2) +
        (Real.eulerMascheroniConstant : Complex) / 2))) = _
  rw [hIntegral]
  rw [show K * (C0 * integral volume H + integral volume G) =
    C0 * (K * integral volume H) + K * integral volume G by ring]
  rw [hAtOne]
  rw [show K * integral volume G =
    quadraticOddGammaConstant *
      Robin1984.robinCutoffMellinTest n x 1 +
    tsum (fun k : Nat =>
      Robin1984.robinZeroKernel n
          (-(2 * (k : Complex) + 1)) x /
        (2 * (k : Complex) + 1)) by
      simpa [K, G, H] using! hShift]
  ring

end

end RobinBV.NumberField
