import Mathlib.Logic.Equiv.Sum
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannXiDivisorZeros
import Robin1984.NicolasLandau.XiZeroConstant
import RobinBV.NumberField.Proof.QuadraticDedekindERH
import RobinBV.NumberField.Proof.QuadraticDedekindZetaZeros
import RobinBV.NumberField.Proof.QuadraticLZeroMass
import RobinBV.NumberField.Proof.QuadraticLZeroMassEvaluation

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex

noncomputable section

abbrev QuadraticDedekindZeroIndex
    (D : NumberField.OddFundamentalDiscriminant) :=
  {p : Complex.Hadamard.divisorZeroIndex
      (quadraticDedekindZeroCarrier D) (Set.univ : Set Complex) //
    Not (p.1 = 0)}

abbrev quadraticDedekindZeroValue
    {D : NumberField.OddFundamentalDiscriminant}
    (p : QuadraticDedekindZeroIndex D) : Complex :=
  p.1.1

theorem quadraticDedekind_divisorMultiplicity_eq_add
    (D : NumberField.OddFundamentalDiscriminant) (z : Complex) :
    Int.toNat
        (MeromorphicOn.divisor (quadraticDedekindZeroCarrier D)
          (Set.univ : Set Complex) z) =
      Int.toNat
          (MeromorphicOn.divisor riemannXi
            (Set.univ : Set Complex) z) +
        Int.toNat
          (MeromorphicOn.divisor
            (symmetricCompletedLFunction D.character)
            (Set.univ : Set Complex) z) := by
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
    (differentiable_quadraticDedekindZeroCarrier D) z]
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
    differentiable_riemannXi z]
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
    (differentiable_symmetricCompletedLFunction
      (quadraticCharacter_ne_one D)) z]
  simp only [Int.toNat_natCast]
  exact analyticOrderNatAt_quadraticDedekindZeroCarrier D z

noncomputable def quadraticDedekindMultiplicityEquiv
    (D : NumberField.OddFundamentalDiscriminant) (z : Complex) :
    Equiv (Fin (Int.toNat
        (MeromorphicOn.divisor (quadraticDedekindZeroCarrier D)
          (Set.univ : Set Complex) z)))
      (Sum (Fin (Int.toNat
          (MeromorphicOn.divisor riemannXi
            (Set.univ : Set Complex) z)))
        (Fin (Int.toNat
          (MeromorphicOn.divisor
            (symmetricCompletedLFunction D.character)
            (Set.univ : Set Complex) z)))) :=
  (finCongr (quadraticDedekind_divisorMultiplicity_eq_add D z)).trans
    finSumFinEquiv.symm

noncomputable def quadraticDedekindZeroIndexBaseEquiv
    (D : NumberField.OddFundamentalDiscriminant) :
    Equiv
      (Complex.Hadamard.divisorZeroIndex
        (quadraticDedekindZeroCarrier D) (Set.univ : Set Complex))
      (Sum (Complex.Hadamard.divisorZeroIndex riemannXi
          (Set.univ : Set Complex))
        (Complex.Hadamard.divisorZeroIndex
          (symmetricCompletedLFunction D.character)
          (Set.univ : Set Complex))) :=
  (Equiv.sigmaCongrRight
      (fun z => quadraticDedekindMultiplicityEquiv D z)).trans
    (Equiv.sigmaSumDistrib _ _)

noncomputable def quadraticDedekindZeroIndexEquiv
    (D : NumberField.OddFundamentalDiscriminant) :
    Equiv (QuadraticDedekindZeroIndex D)
      (Sum RiemannXiDivisorZeroIndex
        (QuadraticLZeroIndex D.character)) where
  toFun p :=
    match quadraticDedekindMultiplicityEquiv D p.1.1 p.1.2 with
    | Sum.inl i =>
        Sum.inl (Subtype.mk (Sigma.mk p.1.1 i) p.2)
    | Sum.inr i =>
        Sum.inr (Subtype.mk (Sigma.mk p.1.1 i) p.2)
  invFun q :=
    match q with
    | Sum.inl p =>
        Subtype.mk
          (Sigma.mk p.1.1
            ((quadraticDedekindMultiplicityEquiv D p.1.1).symm
              (Sum.inl p.1.2))) p.2
    | Sum.inr p =>
        Subtype.mk
          (Sigma.mk p.1.1
            ((quadraticDedekindMultiplicityEquiv D p.1.1).symm
              (Sum.inr p.1.2))) p.2
  left_inv p := by
    cases p with
    | mk p hp =>
      cases p with
      | mk z k =>
        dsimp
        cases hSplit : quadraticDedekindMultiplicityEquiv D z k with
        | inl i =>
          have hk :=
            (quadraticDedekindMultiplicityEquiv D z).symm_apply_apply k
          rw [hSplit] at hk
          cases hk
          rfl
        | inr i =>
          have hk :=
            (quadraticDedekindMultiplicityEquiv D z).symm_apply_apply k
          rw [hSplit] at hk
          cases hk
          rfl
  right_inv q := by
    cases q with
    | inl p =>
      cases p with
      | mk p hp =>
        cases p with
        | mk z k =>
          dsimp
          rw [(quadraticDedekindMultiplicityEquiv D z).apply_symm_apply]
    | inr p =>
      cases p with
      | mk p hp =>
        cases p with
        | mk z k =>
          dsimp
          rw [(quadraticDedekindMultiplicityEquiv D z).apply_symm_apply]

def riemannXiZeroMass : Real :=
  tsum fun p : RiemannXiDivisorZeroIndex =>
    (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)

def quadraticDedekindZeroMass
    (D : NumberField.OddFundamentalDiscriminant) : Real :=
  tsum fun p : QuadraticDedekindZeroIndex D =>
    (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat)

theorem quadraticDedekindZeroIndexEquiv_weight
    (D : NumberField.OddFundamentalDiscriminant)
    (p : QuadraticDedekindZeroIndex D) :
    Sum.elim
        (fun q : RiemannXiDivisorZeroIndex =>
          (Inv.inv (norm (riemannXiDivisorZeroValue q))) ^ (2 : Nat))
        (fun q : QuadraticLZeroIndex D.character =>
          (Inv.inv (norm (quadraticLZeroValue q))) ^ (2 : Nat))
        (quadraticDedekindZeroIndexEquiv D p) =
      (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat) := by
  cases p with
  | mk p hp =>
    cases p with
    | mk z k =>
      dsimp [quadraticDedekindZeroIndexEquiv]
      cases hSplit : quadraticDedekindMultiplicityEquiv D z k <;> rfl

theorem summable_quadraticDedekindZeroWeight
    (D : NumberField.OddFundamentalDiscriminant) :
    Summable (fun p : QuadraticDedekindZeroIndex D =>
      (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat)) := by
  let e := quadraticDedekindZeroIndexEquiv D
  let g : Sum RiemannXiDivisorZeroIndex
      (QuadraticLZeroIndex D.character) -> Real :=
    Sum.elim
      (fun q =>
        (Inv.inv (norm (riemannXiDivisorZeroValue q))) ^ (2 : Nat))
      (fun q =>
        (Inv.inv (norm (quadraticLZeroValue q))) ^ (2 : Nat))
  have hXi : Summable (Function.comp g Sum.inl) := by
    simpa [g, Function.comp_def] using
      Robin1984.summable_robinXiZeroWeight
  have hL : Summable (Function.comp g Sum.inr) := by
    simpa [g, Function.comp_def] using
      summable_quadraticLZeroWeight
        (quadraticCharacter_ne_one D) D.character_isPrimitive
  have hTarget : Summable g := Summable.sum g hXi hL
  have hComposed : Summable (Function.comp g e) :=
    e.summable_iff.mpr hTarget
  have hPointwise :
      Function.comp g e = fun p : QuadraticDedekindZeroIndex D =>
        (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat) := by
    funext p
    exact quadraticDedekindZeroIndexEquiv_weight D p
  rw [hPointwise] at hComposed
  exact hComposed

theorem quadraticDedekindZeroMass_eq_riemannXi_add_quadraticL
    (D : NumberField.OddFundamentalDiscriminant) :
    quadraticDedekindZeroMass D =
      riemannXiZeroMass + quadraticLZeroMass D.character := by
  let e := quadraticDedekindZeroIndexEquiv D
  let g : Sum RiemannXiDivisorZeroIndex
      (QuadraticLZeroIndex D.character) -> Real :=
    Sum.elim
      (fun q =>
        (Inv.inv (norm (riemannXiDivisorZeroValue q))) ^ (2 : Nat))
      (fun q =>
        (Inv.inv (norm (quadraticLZeroValue q))) ^ (2 : Nat))
  have hXi : Summable (Function.comp g Sum.inl) := by
    simpa [g, Function.comp_def] using
      Robin1984.summable_robinXiZeroWeight
  have hL : Summable (Function.comp g Sum.inr) := by
    simpa [g, Function.comp_def] using
      summable_quadraticLZeroWeight
        (quadraticCharacter_ne_one D) D.character_isPrimitive
  have hReindexed :
      tsum (fun p : QuadraticDedekindZeroIndex D =>
          (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat)) =
        tsum g := by
    calc
      tsum (fun p : QuadraticDedekindZeroIndex D =>
          (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat)) =
          tsum (fun p : QuadraticDedekindZeroIndex D => g (e p)) := by
        apply tsum_congr
        intro p
        exact (quadraticDedekindZeroIndexEquiv_weight D p).symm
      _ = tsum g := e.tsum_eq g
  calc
    quadraticDedekindZeroMass D = tsum g := hReindexed
    _ = tsum (Function.comp g Sum.inl) +
        tsum (Function.comp g Sum.inr) :=
      Summable.tsum_sum hXi hL
    _ = riemannXiZeroMass + quadraticLZeroMass D.character := by
      rfl

theorem riemannXiZeroMass_eq_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    riemannXiZeroMass = Real.eulerMascheroniConstant + 2 -
      Real.log (4 * Real.pi) := by
  exact Robin1984.robinXiZeroConstant_eq_of_riemannHypothesis hRH

theorem quadraticDedekindZeroMass_eq_robinConstant_add_quadraticL
    (D : NumberField.OddFundamentalDiscriminant)
    (hRH : RiemannHypothesis) :
    quadraticDedekindZeroMass D =
      Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) +
        quadraticLZeroMass D.character := by
  rw [quadraticDedekindZeroMass_eq_riemannXi_add_quadraticL,
    riemannXiZeroMass_eq_of_riemannHypothesis hRH]

theorem quadraticDedekindZeroMass_eq_real_explicit
    (D : NumberField.OddFundamentalDiscriminant)
    (hPos : 0 < D.value) (hFieldERH : QuadraticDedekindERH D) :
    quadraticDedekindZeroMass D =
      Real.log D.modulus +
        2 * (logDeriv D.character.LFunction 1).re + 2 -
          2 * Real.log (4 * Real.pi) := by
  have hFactors := (quadraticDedekindERH_iff D).1 hFieldERH
  have hSplit :=
    quadraticDedekindZeroMass_eq_riemannXi_add_quadraticL D
  have hXi := riemannXiZeroMass_eq_of_riemannHypothesis hFactors.1
  have hL := quadraticLZeroMass_eq_even_explicit
    (quadraticCharacter_ne_one D) D.character_isPrimitive
    D.character_inv (D.character_even_of_pos hPos) hFactors.2
  rw [hXi, hL] at hSplit
  linarith

theorem quadraticDedekindZeroMass_eq_imaginary_explicit
    (D : NumberField.OddFundamentalDiscriminant)
    (hNeg : D.value < 0) (hFieldERH : QuadraticDedekindERH D) :
    quadraticDedekindZeroMass D =
      Real.log D.modulus +
        2 * (logDeriv D.character.LFunction 1).re + 2 -
          Real.log (4 * Real.pi) - Real.log Real.pi := by
  have hFactors := (quadraticDedekindERH_iff D).1 hFieldERH
  have hSplit :=
    quadraticDedekindZeroMass_eq_riemannXi_add_quadraticL D
  have hXi := riemannXiZeroMass_eq_of_riemannHypothesis hFactors.1
  have hL := quadraticLZeroMass_eq_odd_explicit
    (quadraticCharacter_ne_one D) D.character_isPrimitive
    D.character_inv (D.character_odd_of_neg hNeg) hFactors.2
  rw [hXi, hL] at hSplit
  linarith

end

end RobinBV.NumberField
