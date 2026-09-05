import RobinBV.Mathlib.MeasureTheory.Integral.TailSwap
import RobinBV.NumberField.Helpers.PairedMellinKernel
import RobinBV.NumberField.Proof.PairedDirichletEndpoint

/-!
# Exact paired Dirichlet Mellin reweighting

On Re(s)>1 the inverse Robin-weight kernel and unconditional endpoint
integrability give absolute triangular Fubini. No ERH hypothesis is needed
for this identity. The complete boundary term at the cutoff is retained.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open BombieriVinogradov.SiegelWalfisz
open Complex MeasureTheory Set

noncomputable section

def pairedDirichletChebyshevStep
    {N : Nat} (chi : DirichletCharacter Complex N) (t : Real) : Complex :=
  characterChebyshevSum (Nat.floor t) chi +
    characterChebyshevSum (Nat.floor t) (Inv.inv chi)

theorem integrableOn_pairedDirichletChebyshevStep_mul_weight_one
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) {x : Real} (hx : 3 <= x) :
    IntegrableOn (fun t : Real => pairedDirichletChebyshevStep chi t *
      (Robin1984.robinRealWeight 1 t : Complex)) (Ioi x) := by
  have hInv : Not (Inv.inv chi = 1) := by simpa only [inv_eq_one] using hchi
  have hFirst := (integrableOn_characterChebyshevStep_mul_weight_one chi hchi).mono_set
    (Ioi_subset_Ioi hx)
  have hSecond := (integrableOn_characterChebyshevStep_mul_weight_one (Inv.inv chi) hInv).mono_set
    (Ioi_subset_Ioi hx)
  simpa only [pairedDirichletChebyshevStep, add_mul, Pi.add_apply] using! hFirst.add hSecond

theorem pairedDirichletWeightedIntegral_one_eq_integral
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) {x : Real} (hx : 3 <= x) :
    pairedDirichletWeightedIntegral chi 1 x =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        pairedDirichletChebyshevStep chi t * (Robin1984.robinRealWeight 1 t : Complex)) := by
  have hInv : Not (Inv.inv chi = 1) := by simpa only [inv_eq_one] using hchi
  have hFirst := (integrableOn_characterChebyshevStep_mul_weight_one chi hchi).mono_set
    (Ioi_subset_Ioi hx)
  have hSecond := (integrableOn_characterChebyshevStep_mul_weight_one (Inv.inv chi) hInv).mono_set
    (Ioi_subset_Ioi hx)
  simp only [pairedDirichletWeightedIntegral, dirichletCharacterWeightedIntegral,
    pairedDirichletChebyshevStep, add_mul]
  exact (integral_add hFirst hSecond).symm

theorem continuousOn_pairedDirichletWeightedIntegral_one
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) :
    ContinuousOn (pairedDirichletWeightedIntegral chi 1) (Ici 3) := by
  have hF := integrableOn_pairedDirichletChebyshevStep_mul_weight_one hchi (le_refl (3 : Real))
  apply hF.continuousOn_Ici_primitive_Ioi.congr
  intro x hx
  exact pairedDirichletWeightedIntegral_one_eq_integral hchi hx

/-- The safe-half-plane Mellin identity, including absolute integrability of
the ordinary Mellin tail and the reweighted critical tail. -/
theorem pairedDirichlet_mellin_reweight
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) {s : Complex} (hs : 1 < s.re)
    {x : Real} (hx : 3 <= x) :
    And
      (IntegrableOn (fun t : Real =>
        pairedDirichletChebyshevStep chi t * (t : Complex) ^ (-s - 1)) (Ioi x))
      (And
        (IntegrableOn (fun t : Real =>
          pairedMellinKernelDerivative s t * pairedDirichletWeightedIntegral chi 1 t) (Ioi x))
        (integral (volume.restrict (Ioi x)) (fun t : Real =>
          pairedDirichletChebyshevStep chi t * (t : Complex) ^ (-s - 1)) =
          pairedMellinKernel s x * pairedDirichletWeightedIntegral chi 1 x +
            integral (volume.restrict (Ioi x)) (fun t : Real =>
              pairedMellinKernelDerivative s t * pairedDirichletWeightedIntegral chi 1 t))) := by
  have hxOne : 1 < x := by linarith
  have hF := integrableOn_pairedDirichletChebyshevStep_mul_weight_one hchi hx
  have hV := integrableOn_pairedMellinKernelDerivative hs hxOne
  have hPrimitive : forall t : Real, x < t ->
      integral (volume.restrict (Ioc x t)) (pairedMellinKernelDerivative s) =
        pairedMellinKernel s t - pairedMellinKernel s x :=
    fun t ht => integral_pairedMellinKernelDerivative_Ioc s hxOne ht.le
  have hSwap := complete_tail_reweight_of_integrable hV hF hPrimitive
  have hLeft : EqOn (fun t : Real =>
      pairedMellinKernel s t *
        (pairedDirichletChebyshevStep chi t * (Robin1984.robinRealWeight 1 t : Complex)))
      (fun t : Real => pairedDirichletChebyshevStep chi t * (t : Complex) ^ (-s - 1))
      (Ioi x) := by
    intro t ht
    calc
      _ = pairedDirichletChebyshevStep chi t *
          (pairedMellinKernel s t * (Robin1984.robinRealWeight 1 t : Complex)) := by ring
      _ = _ := by rw [pairedMellinKernel_mul_robinRealWeight s (lt_trans hxOne ht)]
  have hRight : EqOn (fun t : Real => pairedMellinKernelDerivative s t *
      integral (volume.restrict (Ioi t)) (fun u : Real =>
        pairedDirichletChebyshevStep chi u * (Robin1984.robinRealWeight 1 u : Complex)))
      (fun t : Real => pairedMellinKernelDerivative s t * pairedDirichletWeightedIntegral chi 1 t)
      (Ioi x) := by
    intro t ht
    dsimp only
    rw [pairedDirichletWeightedIntegral_one_eq_integral hchi (le_trans hx ht.le)]
  refine And.intro (hSwap.1.congr_fun hLeft measurableSet_Ioi)
    (And.intro (hSwap.2.1.congr_fun hRight measurableSet_Ioi) ?_)
  rw [<- setIntegral_congr_fun measurableSet_Ioi hLeft,
    <- setIntegral_congr_fun measurableSet_Ioi hRight,
    pairedDirichletWeightedIntegral_one_eq_integral hchi hx]
  exact hSwap.2.2

end

end RobinBV.NumberField
