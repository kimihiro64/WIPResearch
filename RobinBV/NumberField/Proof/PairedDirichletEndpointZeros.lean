import Robin1984.NicolasLandau.WeightedEndpointZeros
import RobinBV.NumberField.Proof.PairedDirichletWeightedFormula

/-!
# Complete endpoint transfer for complex Dirichlet zero sums

The inverse-square mass justifies the integral/sum exchange over every
multiplicity-counted zero of a primitive character. The character need not
be self-dual. These are the two constituent zero families of a dual pair.
-/

set_option autoImplicit false

namespace RobinBV.NumberField

open MeasureTheory Set

noncomputable section

theorem countable_primitiveLZeroIndex
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    Countable (QuadraticLZeroIndex chi) := by
  have hSupport : Function.support (fun p : QuadraticLZeroIndex chi =>
      (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat)) =
      Set.univ := by
    ext p
    simp only [Function.mem_support, mem_univ, iff_true]
    exact pow_ne_zero _
      (inv_ne_zero (norm_ne_zero_iff.mpr p.2))
  have hCount : Set.Countable (Function.support
      (fun p : QuadraticLZeroIndex chi =>
        (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat))) :=
    (summable_quadraticLZeroWeight hchi hPrimitive).countable_support
  rw [hSupport] at hCount
  exact Set.countable_univ_iff.mp hCount

theorem summable_integral_norm_primitiveLEndpointZeroAtoms
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi)
    {x : Real} (hx : 1 < x) :
    Summable (fun p : QuadraticLZeroIndex chi =>
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm ((Robin1984.robinEndpointReweightDerivative t : Complex) *
          (Robin1984.robinZeroKernel 2
            (quadraticLZeroValue p) t /
              quadraticLZeroValue p)))) := by
  have hM := Robin1984.integrableOn_robinEndpointZeroMajorant hx
  have hMajor (p : QuadraticLZeroIndex chi) :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm ((Robin1984.robinEndpointReweightDerivative t : Complex) *
          (Robin1984.robinZeroKernel 2
            (quadraticLZeroValue p) t /
              quadraticLZeroValue p))) <=
      (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat) *
        integral (volume.restrict (Ioi x))
          Robin1984.robinEndpointZeroMajorant := by
    have hRe : (quadraticLZeroValue p).re = (1 / 2 : Real) :=
      quadraticLZeroValue_re_eq_half_of_dirichletERH hchi hPrimitive hERH p
    have hInt := Robin1984.integrableOn_robinEndpointZeroAtom hx
      (show (quadraticLZeroValue p).re < 1 by linarith)
    calc
      _ <= integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Inv.inv (norm (quadraticLZeroValue p))) ^ (2 : Nat) *
            Robin1984.robinEndpointZeroMajorant t) := by
        apply integral_mono_ae hInt.norm (hM.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Robin1984.norm_robinEndpointZeroAtom_le p.2 hRe
          (lt_trans hx ht)
      _ = _ := integral_const_mul _ _
  exact Summable.of_nonneg_of_le
    (fun p => integral_nonneg (fun t => norm_nonneg _)) hMajor
    ((summable_quadraticLZeroWeight hchi hPrimitive).mul_right _)

theorem primitiveL_complete_zero_sum_one_reweight
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi)
    {x : Real} (hx : 1 < x) :
    And
      (IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          tsum (fun p : QuadraticLZeroIndex chi =>
            Robin1984.robinZeroKernel 2
              (quadraticLZeroValue p) t /
                quadraticLZeroValue p)) (Ioi x))
      (tsum (fun p : QuadraticLZeroIndex chi =>
          Robin1984.robinZeroKernel 1
            (quadraticLZeroValue p) x /
              quadraticLZeroValue p) =
        (Robin1984.robinEndpointReweight x : Complex) *
          tsum (fun p : QuadraticLZeroIndex chi =>
            Robin1984.robinZeroKernel 2
              (quadraticLZeroValue p) x /
                quadraticLZeroValue p) +
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            (Robin1984.robinEndpointReweightDerivative t : Complex) *
              tsum (fun p : QuadraticLZeroIndex chi =>
                Robin1984.robinZeroKernel 2
                  (quadraticLZeroValue p) t /
                    quadraticLZeroValue p))) := by
  let _ : Countable (QuadraticLZeroIndex chi) :=
    countable_primitiveLZeroIndex hchi hPrimitive
  let Z (p : QuadraticLZeroIndex chi) (t : Real) : Complex :=
    (Robin1984.robinEndpointReweightDerivative t : Complex) *
      (Robin1984.robinZeroKernel 2
        (quadraticLZeroValue p) t /
          quadraticLZeroValue p)
  have hInt (p : QuadraticLZeroIndex chi) :
      IntegrableOn (Z p) (Ioi x) := by
    have hRe : (quadraticLZeroValue p).re = (1 / 2 : Real) :=
      quadraticLZeroValue_re_eq_half_of_dirichletERH hchi hPrimitive hERH p
    exact Robin1984.integrableOn_robinEndpointZeroAtom hx (by linarith)
  have hNorm : Summable (fun p : QuadraticLZeroIndex chi =>
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm (Z p t))) :=
    summable_integral_norm_primitiveLEndpointZeroAtoms
      hchi hPrimitive hERH hx
  have hSumInt : Summable (fun p : QuadraticLZeroIndex chi =>
      integral (volume.restrict (Ioi x)) (Z p)) :=
    hNorm.of_norm_bounded (fun p => norm_integral_le_integral_norm _)
  have hSeries := Robin1984.integrable_complex_series_of_integral_norm
    hInt hNorm
  have hWholeInt : IntegrableOn (fun t : Real =>
      (Robin1984.robinEndpointReweightDerivative t : Complex) *
        tsum (fun p : QuadraticLZeroIndex chi =>
          Robin1984.robinZeroKernel 2
            (quadraticLZeroValue p) t /
              quadraticLZeroValue p)) (Ioi x) := by
    apply IntegrableOn.congr_fun hSeries _ measurableSet_Ioi
    intro t ht
    dsimp only [Z]
    rw [tsum_mul_left]
  have hAtom (p : QuadraticLZeroIndex chi) :
      Robin1984.robinZeroKernel 1
          (quadraticLZeroValue p) x /
            quadraticLZeroValue p =
        (Robin1984.robinEndpointReweight x : Complex) *
          (Robin1984.robinZeroKernel 2
            (quadraticLZeroValue p) x /
              quadraticLZeroValue p) +
          integral (volume.restrict (Ioi x)) (Z p) := by
    have hRe : (quadraticLZeroValue p).re = (1 / 2 : Real) :=
      quadraticLZeroValue_re_eq_half_of_dirichletERH hchi hPrimitive hERH p
    have hRaw := (Robin1984.robinZeroKernel_one_reweight hx
      (show (quadraticLZeroValue p).re < 1 by linarith)).2
    rw [hRaw, add_div, mul_div_assoc]
    congr 1
    rw [<- integral_div]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [Z]
    ring
  exact And.intro hWholeInt (by
    calc
      _ = tsum (fun p : QuadraticLZeroIndex chi =>
          (Robin1984.robinEndpointReweight x : Complex) *
            (Robin1984.robinZeroKernel 2
              (quadraticLZeroValue p) x /
                quadraticLZeroValue p) +
            integral (volume.restrict (Ioi x)) (Z p)) :=
        tsum_congr hAtom
      _ = (Robin1984.robinEndpointReweight x : Complex) *
            tsum (fun p : QuadraticLZeroIndex chi =>
              Robin1984.robinZeroKernel 2
                (quadraticLZeroValue p) x /
                  quadraticLZeroValue p) +
            tsum (fun p : QuadraticLZeroIndex chi =>
              integral (volume.restrict (Ioi x)) (Z p)) := by
        rw [((summable_primitiveCharacter_robinZeroKernel_div
          hchi hPrimitive hERH (n := 2) (by norm_num) hx).mul_left
            (Robin1984.robinEndpointReweight x : Complex)).tsum_add
              hSumInt, tsum_mul_left]
      _ = _ := by
        rw [integral_tsum_of_summable_integral_norm hInt hNorm]
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only [Z]
        rw [tsum_mul_left])

/-- Both constituent zero families reweight to the full paired-carrier sum,
with no loss or duplication of multiplicities. -/
theorem pairedDirichlet_complete_zero_sum_one_reweight
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Not (chi = 1)) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hERH : DirichletERH chi) {x : Real} (hx : 1 < x) :
    And
      (IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          tsum (fun p : PairedDirichletZeroIndex chi =>
            Robin1984.robinZeroKernel 2 (pairedDirichletZeroValue p) t /
              pairedDirichletZeroValue p)) (Ioi x))
      (tsum (fun p : PairedDirichletZeroIndex chi =>
        Robin1984.robinZeroKernel 1 (pairedDirichletZeroValue p) x /
          pairedDirichletZeroValue p) =
        (Robin1984.robinEndpointReweight x : Complex) *
          tsum (fun p : PairedDirichletZeroIndex chi =>
            Robin1984.robinZeroKernel 2 (pairedDirichletZeroValue p) x /
              pairedDirichletZeroValue p) +
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Robin1984.robinEndpointReweightDerivative t : Complex) *
            tsum (fun p : PairedDirichletZeroIndex chi =>
              Robin1984.robinZeroKernel 2 (pairedDirichletZeroValue p) t /
                pairedDirichletZeroValue p))) := by
  have hi := BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hp := BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive
  have he := (dirichletERH_inv_iff_of_isPrimitive hPrimitive).2 hERH
  have hLeft := primitiveL_complete_zero_sum_one_reweight hchi hPrimitive hERH hx
  have hRight := primitiveL_complete_zero_sum_one_reweight hi hp he hx
  have hSplit (n : Nat) (hn : 1 <= n) (t : Real) (ht : 1 < t) :
      tsum (fun p : PairedDirichletZeroIndex chi =>
        Robin1984.robinZeroKernel n (pairedDirichletZeroValue p) t /
          pairedDirichletZeroValue p) =
      tsum (fun p : QuadraticLZeroIndex chi =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) t / quadraticLZeroValue p) +
      tsum (fun p : QuadraticLZeroIndex (Inv.inv chi) =>
        Robin1984.robinZeroKernel n (quadraticLZeroValue p) t / quadraticLZeroValue p) :=
    tsum_pairedDirichletZeroKernel_eq_sum hchi
      (fun rho => Robin1984.robinZeroKernel n rho t / rho)
      (summable_primitiveCharacter_robinZeroKernel_div hchi hPrimitive hERH hn ht)
      (summable_primitiveCharacter_robinZeroKernel_div hi hp he hn ht)
  have hIntegral :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          tsum (fun p : PairedDirichletZeroIndex chi =>
            Robin1984.robinZeroKernel 2 (pairedDirichletZeroValue p) t /
              pairedDirichletZeroValue p)) =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          tsum (fun p : QuadraticLZeroIndex chi =>
            Robin1984.robinZeroKernel 2 (quadraticLZeroValue p) t / quadraticLZeroValue p)) +
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          tsum (fun p : QuadraticLZeroIndex (Inv.inv chi) =>
            Robin1984.robinZeroKernel 2 (quadraticLZeroValue p) t / quadraticLZeroValue p)) := by
    rw [<- integral_add hLeft.1 hRight.1]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [Pi.add_apply]
    rw [hSplit 2 (by norm_num) t (lt_trans hx ht), mul_add]
  refine And.intro ?_ ?_
  next =>
    apply (hLeft.1.add hRight.1).congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.add_apply]
    rw [hSplit 2 (by norm_num) t (lt_trans hx ht), mul_add]
  next =>
    rw [hSplit 1 (by norm_num) x hx, hLeft.2, hRight.2,
      hSplit 2 (by norm_num) x hx, hIntegral]
    ring

end

end RobinBV.NumberField
