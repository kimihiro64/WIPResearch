import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Expansion
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Linearity
import RobinBV.NumberField.Definitions.QuadraticDedekindZeta

/-!
# Prime-side decomposition of quadratic Dedekind zeta

The quadratic Dedekind von Mangoldt coefficient is the sum of the rational
von Mangoldt coefficient and its quadratic-character twist. Its finite
Chebyshev sum therefore splits exactly into the ordinary Chebyshev function
and the character sum used by the Bombieri-Vinogradov explicit-formula
development. On the half-plane of absolute convergence, its L-series is the
negative logarithmic derivative of the canonical quadratic Dedekind-zeta
continuation.
-/

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Finset

noncomputable section

def quadraticDedekindMangoldtSequence
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) : Complex :=
  (ArithmeticFunction.vonMangoldt n : Complex) +
    twistedMangoldtSequence D.character n

def rationalChebyshevSum (x : Nat) : Complex :=
  (Finset.Icc 1 x).sum fun n =>
    (ArithmeticFunction.vonMangoldt n : Complex)

def quadraticDedekindChebyshevSum
    (D : NumberField.OddFundamentalDiscriminant) (x : Nat) : Complex :=
  (Finset.Icc 1 x).sum fun n =>
    quadraticDedekindMangoldtSequence D n

theorem quadraticDedekindMangoldtSequence_im
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) :
    (quadraticDedekindMangoldtSequence D n).im = 0 := by
  unfold quadraticDedekindMangoldtSequence twistedMangoldtSequence
  rcases D.character_isQuadratic n with hZero | hOne | hNeg
  next => rw [hZero]; simp
  next => rw [hOne]; simp
  next => rw [hNeg]; simp

theorem quadraticDedekindMangoldtSequence_re_nonneg
    (D : NumberField.OddFundamentalDiscriminant) (n : Nat) :
    0 <= (quadraticDedekindMangoldtSequence D n).re := by
  unfold quadraticDedekindMangoldtSequence twistedMangoldtSequence
  rcases D.character_isQuadratic n with hZero | hOne | hNeg
  next => rw [hZero]; simp [ArithmeticFunction.vonMangoldt_nonneg]
  next => rw [hOne]; simp [ArithmeticFunction.vonMangoldt_nonneg]
  next => rw [hNeg]; simp

theorem quadraticDedekindChebyshevSum_im
    (D : NumberField.OddFundamentalDiscriminant) (x : Nat) :
    (quadraticDedekindChebyshevSum D x).im = 0 := by
  have hAll : forall S : Finset Nat,
      (S.sum fun n => quadraticDedekindMangoldtSequence D n).im = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert n S hn ih =>
      rw [Finset.sum_insert hn, Complex.add_im,
        quadraticDedekindMangoldtSequence_im, ih, add_zero]
  exact hAll (Finset.Icc 1 x)

theorem quadraticDedekindChebyshevSum_re_nonneg
    (D : NumberField.OddFundamentalDiscriminant) (x : Nat) :
    0 <= (quadraticDedekindChebyshevSum D x).re := by
  have hAll : forall S : Finset Nat,
      0 <= (S.sum fun n => quadraticDedekindMangoldtSequence D n).re := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert n S hn ih =>
      rw [Finset.sum_insert hn, Complex.add_re]
      exact add_nonneg
        (quadraticDedekindMangoldtSequence_re_nonneg D n) ih
  exact hAll (Finset.Icc 1 x)

theorem rationalChebyshevSum_eq_psi (x : Nat) :
    rationalChebyshevSum x = Chebyshev.psi x := by
  unfold rationalChebyshevSum Chebyshev.psi
  simp only [Nat.floor_natCast]
  norm_cast

theorem quadraticDedekindChebyshevSum_eq_add
    (D : NumberField.OddFundamentalDiscriminant) (x : Nat) :
    quadraticDedekindChebyshevSum D x =
      rationalChebyshevSum x + characterChebyshevSum x D.character := by
  unfold quadraticDedekindChebyshevSum
  unfold quadraticDedekindMangoldtSequence
  unfold rationalChebyshevSum characterChebyshevSum
  unfold BombieriVinogradov.VaughanMeanValue.psiCharacterSum
  rw [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  unfold twistedMangoldtSequence
  rw [mul_comm]

theorem quadraticDedekindChebyshevSum_eq_psi_add_character
    (D : NumberField.OddFundamentalDiscriminant) (x : Nat) :
    quadraticDedekindChebyshevSum D x =
      Chebyshev.psi x + characterChebyshevSum x D.character := by
  rw [quadraticDedekindChebyshevSum_eq_add,
    rationalChebyshevSum_eq_psi]

theorem quadraticCharacterChebyshevSum_im
    (D : NumberField.OddFundamentalDiscriminant) (x : Nat) :
    (characterChebyshevSum x D.character).im = 0 := by
  have hSplit := congrArg Complex.im
    (quadraticDedekindChebyshevSum_eq_psi_add_character D x)
  rw [quadraticDedekindChebyshevSum_im] at hSplit
  simpa using hSplit.symm

theorem quadraticDedekindChebyshevSum_re_eq
    (D : NumberField.OddFundamentalDiscriminant) (x : Nat) :
    (quadraticDedekindChebyshevSum D x).re =
      Chebyshev.psi x + (characterChebyshevSum x D.character).re := by
  have hSplit := congrArg Complex.re
    (quadraticDedekindChebyshevSum_eq_psi_add_character D x)
  simpa using hSplit

theorem neg_logDeriv_quadraticDedekindZetaContinuation_eq_add_LSeries
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 < s.re) :
    -logDeriv (quadraticDedekindZetaContinuation D) s =
      LSeries (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex)) s +
        LSeries (twistedMangoldtSequence D.character) s := by
  have hsOne : Not (s = 1) := by
    intro hOne
    rw [hOne] at hs
    norm_num at hs
  have hZetaNe : Not (riemannZeta s = 0) :=
    riemannZeta_ne_zero_of_one_le_re hs.le
  have hLNe : Not (D.character.LFunction s = 0) :=
    D.character.LFunction_ne_zero_of_one_le_re
      (Or.inl (quadraticCharacter_ne_one D)) hs.le
  have hProduct := logDeriv_mul s hZetaNe hLNe
    (differentiableAt_riemannZeta hsOne)
    (D.character.differentiableAt_LFunction s
      (Or.inr (quadraticCharacter_ne_one D)))
  have hZetaSeries :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hLSeries := neg_logDeriv_LFunction_eq_LSeries D.character hs
  have hZetaLog :
      -logDeriv riemannZeta s =
        LSeries (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex)) s := by
    rw [logDeriv_apply]
    calc
      -(deriv riemannZeta s / riemannZeta s) =
          -deriv riemannZeta s / riemannZeta s := by ring
      _ = LSeries (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex)) s :=
        hZetaSeries.symm
  unfold quadraticDedekindZetaContinuation
  rw [hProduct]
  calc
    -(logDeriv riemannZeta s + logDeriv D.character.LFunction s) =
        -logDeriv riemannZeta s +
          -logDeriv D.character.LFunction s := by ring
    _ = LSeries (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex)) s +
        LSeries (twistedMangoldtSequence D.character) s := by
      rw [hZetaLog, hLSeries]

theorem neg_logDeriv_quadraticDedekindZetaContinuation_eq_LSeries
    (D : NumberField.OddFundamentalDiscriminant)
    {s : Complex} (hs : 1 < s.re) :
    -logDeriv (quadraticDedekindZetaContinuation D) s =
      LSeries (quadraticDedekindMangoldtSequence D) s := by
  rw [neg_logDeriv_quadraticDedekindZetaContinuation_eq_add_LSeries D hs]
  have hZeta : LSeriesSummable
      (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hL : LSeriesSummable
      (twistedMangoldtSequence D.character) s := by
    change LSeriesSummable
      ((fun n : Nat => D.character n) *
        (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex))) s
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt D.character hs
  have hAdd := LSeries_add hZeta hL
  rw [show quadraticDedekindMangoldtSequence D =
      (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) +
        twistedMangoldtSequence D.character by
    funext n
    rfl]
  exact hAdd.symm

end

end RobinBV.NumberField
