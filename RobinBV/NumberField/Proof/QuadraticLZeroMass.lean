import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroRealSumReflection
import RobinBV.NumberField.Definitions.QuadraticLZeros
import RobinBV.NumberField.Proof.QuadraticLFiniteOrderInput

/-!
# The primitive Dirichlet L zero mass under ERH

The committed Bombieri--Vinogradov dependency supplies the order-one
Hadamard divisor, its multiplicities, critical-strip localization, reflection,
and inverse-square summability.  This module connects that divisor to the
project's `DirichletERH` predicate and proves that the symmetric Stark summand
is exactly the positive inverse-square weight under ERH.
-/

open Lean Elab Tactic

elab "exact_decl_by_ascii_name " s:str " for " n:ident chiId:ident
    hchiId:ident hPrimitiveId:ident : tactic => do
  let parts := s.getString.splitOn "."
  let name := List.foldl (fun acc part => Name.str acc part)
    Name.anonymous parts
  let id := mkIdent name
  let tacStx <- `(tactic|
    exact $id (N := $n) (chi := $chiId) $hchiId $hPrimitiveId)
  evalTactic tacStx

namespace RobinBV.NumberField

open DirichletCharacter
open BombieriVinogradov.SiegelWalfisz
open scoped BigOperators

noncomputable section

variable {N : Nat} [NeZero N]

abbrev QuadraticLZeroIndex (chi : DirichletCharacter Complex N) :=
  BombieriVinogradov.SiegelWalfisz.SymmetricCompletedZeroIndex chi

abbrev quadraticLZeroValue {chi : DirichletCharacter Complex N}
    (p : QuadraticLZeroIndex chi) : Complex :=
  p.1.1

/-- The positive multiplicity-counted inverse-square zero mass. -/
def quadraticLZeroMass (chi : DirichletCharacter Complex N) : Real :=
  tsum fun p : QuadraticLZeroIndex chi =>
    (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat)

/-- The symmetric zero sum occurring in the endpoint logarithmic-derivative
formula.  Under ERH it is the complex embedding of `quadraticLZeroMass`. -/
def quadraticLStarkMass (chi : DirichletCharacter Complex N) : Complex :=
  tsum fun p : QuadraticLZeroIndex chi =>
    1 / (quadraticLZeroValue p * (1 - quadraticLZeroValue p))

theorem summable_quadraticLZeroWeight
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    Summable (fun p : QuadraticLZeroIndex chi =>
      (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat)) := by
  exact_decl_by_ascii_name "BombieriVinogradov.SiegelWalfisz.summable_symmetricCompletedLFunction_divisorZeroIndex\u2080_norm_inv_sq" for N chi hchi hPrimitive

theorem quadraticLZeroValue_isNontrivialCompletedLZero
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : QuadraticLZeroIndex chi) :
    IsNontrivialCompletedLZero chi (quadraticLZeroValue p) := by
  let rho : Complex := quadraticLZeroValue p
  have hMultiplicity :
      Not (Int.toNat
        (MeromorphicOn.divisor
          (BombieriVinogradov.SiegelWalfisz.symmetricCompletedLFunction chi)
          (Set.univ : Set Complex) rho) = 0) := by
    intro hZero
    have q0 : Fin 0 := by
      simpa [rho, hZero] using p.1.2
    exact Fin.elim0 q0
  have hOrder :
      Not (analyticOrderNatAt
        (BombieriVinogradov.SiegelWalfisz.symmetricCompletedLFunction chi)
        rho = 0) := by
    intro hZero
    apply hMultiplicity
    rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (differentiable_symmetricCompletedLFunction hchi), hZero]
    simp
  have hSymmetricZero :
      BombieriVinogradov.SiegelWalfisz.symmetricCompletedLFunction chi rho = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero hOrder
  have hN : Not ((N : Complex) = 0) := by
    exact_mod_cast NeZero.ne N
  have hPower : Not ((N : Complex) ^ (rho / 2) = 0) :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hN)
  have hCompletedZero : completedLFunction chi rho = 0 := by
    rw [BombieriVinogradov.SiegelWalfisz.symmetricCompletedLFunction]
      at hSymmetricZero
    exact (mul_eq_zero.mp hSymmetricZero).resolve_left hPower
  have hUpper : rho.re < 1 := by
    by_contra hNot
    exact symmetricCompletedLFunction_ne_zero_of_one_le_re
      hchi (le_of_not_gt hNot) hSymmetricZero
  have hLower : 0 < rho.re := by
    by_contra hNot
    have hReflectedRe :
        1 <= (1 - (starRingEnd Complex) rho).re := by
      have hConjRe : ((starRingEnd Complex) rho).re = rho.re := by simp
      rw [Complex.sub_re, hConjRe]
      norm_num
      linarith
    have hReflectedZero :
        BombieriVinogradov.SiegelWalfisz.symmetricCompletedLFunction chi
          (1 - (starRingEnd Complex) rho) = 0 := by
      rw [symmetricCompletedLFunction_one_sub_conj hchi hPrimitive,
        hSymmetricZero, map_zero, mul_zero]
    exact symmetricCompletedLFunction_ne_zero_of_one_le_re
      hchi hReflectedRe hReflectedZero
  have hStrip : And (0 < rho.re) (rho.re < 1) :=
    And.intro hLower hUpper
  exact And.intro hCompletedZero hStrip

theorem quadraticLZeroValue_re_eq_half_of_dirichletERH
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) (p : QuadraticLZeroIndex chi) :
    (quadraticLZeroValue p).re = 1 / 2 := by
  exact hERH (quadraticLZeroValue p)
    (quadraticLZeroValue_isNontrivialCompletedLZero hchi hPrimitive p)

theorem quadraticLZero_starkTerm_eq_norm_inv_sq
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) (p : QuadraticLZeroIndex chi) :
    1 / (quadraticLZeroValue p * (1 - quadraticLZeroValue p)) =
      (((Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat) : Real) :
        Complex) := by
  let rho : Complex := quadraticLZeroValue p
  have hRhoZero : Not (rho = 0) := p.property
  have hRe : rho.re = (1 / 2 : Real) :=
    quadraticLZeroValue_re_eq_half_of_dirichletERH
      hchi hPrimitive hERH p
  have hConj : 1 - rho = starRingEnd Complex rho := by
    apply Complex.ext
    next =>
      rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hRe]
      norm_num
    next => simp
  have hNormZero : Not (norm rho = 0) :=
    norm_ne_zero_iff.mpr hRhoZero
  change
    1 / (rho * (1 - rho)) =
      (((Inv.inv (norm rho)) ^ (2 : Nat) : Real) : Complex)
  rw [hConj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp [hNormZero]

/-- Under ERH, Stark's symmetric completed-L zero sum is the complex
embedding of the positive inverse-square zero mass. -/
theorem ofReal_quadraticLZeroMass_eq_quadraticLStarkMass_of_dirichletERH
    {chi : DirichletCharacter Complex N} (hchi : Not (chi = 1))
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) :
    (quadraticLZeroMass chi : Complex) = quadraticLStarkMass chi := by
  rw [quadraticLZeroMass, quadraticLStarkMass, Complex.ofReal_tsum]
  apply tsum_congr
  intro p
  exact (quadraticLZero_starkTerm_eq_norm_inv_sq
    hchi hPrimitive hERH p).symm

theorem quadraticLZeroMass_nonneg
    (chi : DirichletCharacter Complex N) :
    0 <= quadraticLZeroMass chi := by
  exact tsum_nonneg fun _p => by positivity

end

end RobinBV.NumberField
