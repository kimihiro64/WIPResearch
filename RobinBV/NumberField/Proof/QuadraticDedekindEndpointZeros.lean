import Robin1984.NicolasLandau.WeightedEndpointZeros
import RobinBV.NumberField.Proof.QuadraticDedekindWeightedError

/-!
# Endpoint reweighting for quadratic Dedekind zero sums

The inverse-square zero mass controls the complete multiplicity-counted
Dedekind zero family strongly enough to interchange the endpoint reweighting
integral with its zero sum.
-/

namespace RobinBV.NumberField

open MeasureTheory Set

noncomputable section

theorem countable_quadraticDedekindZeroIndex
    (D : NumberField.OddFundamentalDiscriminant) :
    Countable (QuadraticDedekindZeroIndex D) := by
  have hSupport : Function.support (fun p : QuadraticDedekindZeroIndex D =>
      (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat)) =
      Set.univ := by
    ext p
    simp only [Function.mem_support, mem_univ, iff_true]
    exact pow_ne_zero _
      (inv_ne_zero (norm_ne_zero_iff.mpr p.2))
  have hCount : Set.Countable (Function.support
      (fun p : QuadraticDedekindZeroIndex D =>
        (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat))) :=
    (summable_quadraticDedekindZeroWeight D).countable_support
  rw [hSupport] at hCount
  exact Set.countable_univ_iff.mp hCount

theorem summable_quadraticDedekind_robinZeroKernel_div
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    Summable (fun p : QuadraticDedekindZeroIndex D =>
      Robin1984.robinZeroKernel n (quadraticDedekindZeroValue p) x /
        quadraticDedekindZeroValue p) := by
  let C : Real := quadraticRobinZeroKernelScale n x
  have hMajor : Summable (fun p : QuadraticDedekindZeroIndex D =>
      (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat) * C) :=
    (summable_quadraticDedekindZeroWeight D).mul_right C
  apply hMajor.of_norm_bounded
  intro p
  dsimp [C, quadraticRobinZeroKernelScale]
  exact Robin1984.norm_robinZeroKernel_div_rho_le_robinXiZeroWeight hn
    p.2 (quadraticDedekindZeroValue_re_eq_half_of_ERH D hFieldERH p) hx

theorem summable_integral_norm_quadraticDedekindEndpointZeroAtoms
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {x : Real} (hx : 1 < x) :
    Summable (fun p : QuadraticDedekindZeroIndex D =>
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm ((Robin1984.robinEndpointReweightDerivative t : Complex) *
          (Robin1984.robinZeroKernel 2
            (quadraticDedekindZeroValue p) t /
              quadraticDedekindZeroValue p)))) := by
  have hM := Robin1984.integrableOn_robinEndpointZeroMajorant hx
  have hMajor (p : QuadraticDedekindZeroIndex D) :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm ((Robin1984.robinEndpointReweightDerivative t : Complex) *
          (Robin1984.robinZeroKernel 2
            (quadraticDedekindZeroValue p) t /
              quadraticDedekindZeroValue p))) <=
      (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat) *
        integral (volume.restrict (Ioi x))
          Robin1984.robinEndpointZeroMajorant := by
    have hRe : (quadraticDedekindZeroValue p).re = (1 / 2 : Real) :=
      quadraticDedekindZeroValue_re_eq_half_of_ERH D hFieldERH p
    have hInt := Robin1984.integrableOn_robinEndpointZeroAtom hx
      (show (quadraticDedekindZeroValue p).re < 1 by linarith)
    calc
      _ <= integral (volume.restrict (Ioi x)) (fun t : Real =>
          (Inv.inv (norm (quadraticDedekindZeroValue p))) ^ (2 : Nat) *
            Robin1984.robinEndpointZeroMajorant t) := by
        apply integral_mono_ae hInt.norm (hM.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Robin1984.norm_robinEndpointZeroAtom_le p.2 hRe
          (lt_trans hx ht)
      _ = _ := integral_const_mul _ _
  exact Summable.of_nonneg_of_le
    (fun p => integral_nonneg (fun t => norm_nonneg _)) hMajor
    ((summable_quadraticDedekindZeroWeight D).mul_right _)

theorem quadraticDedekind_complete_zero_sum_one_reweight
    (D : NumberField.OddFundamentalDiscriminant)
    (hFieldERH : QuadraticDedekindERH D)
    {x : Real} (hx : 1 < x) :
    And
      (IntegrableOn (fun t : Real =>
        (Robin1984.robinEndpointReweightDerivative t : Complex) *
          tsum (fun p : QuadraticDedekindZeroIndex D =>
            Robin1984.robinZeroKernel 2
              (quadraticDedekindZeroValue p) t /
                quadraticDedekindZeroValue p)) (Ioi x))
      (tsum (fun p : QuadraticDedekindZeroIndex D =>
          Robin1984.robinZeroKernel 1
            (quadraticDedekindZeroValue p) x /
              quadraticDedekindZeroValue p) =
        (Robin1984.robinEndpointReweight x : Complex) *
          tsum (fun p : QuadraticDedekindZeroIndex D =>
            Robin1984.robinZeroKernel 2
              (quadraticDedekindZeroValue p) x /
                quadraticDedekindZeroValue p) +
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            (Robin1984.robinEndpointReweightDerivative t : Complex) *
              tsum (fun p : QuadraticDedekindZeroIndex D =>
                Robin1984.robinZeroKernel 2
                  (quadraticDedekindZeroValue p) t /
                    quadraticDedekindZeroValue p))) := by
  let _ : Countable (QuadraticDedekindZeroIndex D) :=
    countable_quadraticDedekindZeroIndex D
  let Z (p : QuadraticDedekindZeroIndex D) (t : Real) : Complex :=
    (Robin1984.robinEndpointReweightDerivative t : Complex) *
      (Robin1984.robinZeroKernel 2
        (quadraticDedekindZeroValue p) t /
          quadraticDedekindZeroValue p)
  have hInt (p : QuadraticDedekindZeroIndex D) :
      IntegrableOn (Z p) (Ioi x) := by
    have hRe : (quadraticDedekindZeroValue p).re = (1 / 2 : Real) :=
      quadraticDedekindZeroValue_re_eq_half_of_ERH D hFieldERH p
    exact Robin1984.integrableOn_robinEndpointZeroAtom hx (by linarith)
  have hNorm : Summable (fun p : QuadraticDedekindZeroIndex D =>
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        norm (Z p t))) :=
    summable_integral_norm_quadraticDedekindEndpointZeroAtoms
      D hFieldERH hx
  have hSumInt : Summable (fun p : QuadraticDedekindZeroIndex D =>
      integral (volume.restrict (Ioi x)) (Z p)) :=
    hNorm.of_norm_bounded (fun p => norm_integral_le_integral_norm _)
  have hSeries := Robin1984.integrable_complex_series_of_integral_norm
    hInt hNorm
  have hWholeInt : IntegrableOn (fun t : Real =>
      (Robin1984.robinEndpointReweightDerivative t : Complex) *
        tsum (fun p : QuadraticDedekindZeroIndex D =>
          Robin1984.robinZeroKernel 2
            (quadraticDedekindZeroValue p) t /
              quadraticDedekindZeroValue p)) (Ioi x) := by
    apply IntegrableOn.congr_fun hSeries _ measurableSet_Ioi
    intro t ht
    dsimp only [Z]
    rw [tsum_mul_left]
  have hAtom (p : QuadraticDedekindZeroIndex D) :
      Robin1984.robinZeroKernel 1
          (quadraticDedekindZeroValue p) x /
            quadraticDedekindZeroValue p =
        (Robin1984.robinEndpointReweight x : Complex) *
          (Robin1984.robinZeroKernel 2
            (quadraticDedekindZeroValue p) x /
              quadraticDedekindZeroValue p) +
          integral (volume.restrict (Ioi x)) (Z p) := by
    have hRe : (quadraticDedekindZeroValue p).re = (1 / 2 : Real) :=
      quadraticDedekindZeroValue_re_eq_half_of_ERH D hFieldERH p
    have hRaw := (Robin1984.robinZeroKernel_one_reweight hx
      (show (quadraticDedekindZeroValue p).re < 1 by linarith)).2
    rw [hRaw, add_div, mul_div_assoc]
    congr 1
    rw [<- integral_div]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [Z]
    ring
  exact And.intro hWholeInt (by
    calc
      _ = tsum (fun p : QuadraticDedekindZeroIndex D =>
          (Robin1984.robinEndpointReweight x : Complex) *
            (Robin1984.robinZeroKernel 2
              (quadraticDedekindZeroValue p) x /
                quadraticDedekindZeroValue p) +
            integral (volume.restrict (Ioi x)) (Z p)) :=
        tsum_congr hAtom
      _ = (Robin1984.robinEndpointReweight x : Complex) *
            tsum (fun p : QuadraticDedekindZeroIndex D =>
              Robin1984.robinZeroKernel 2
                (quadraticDedekindZeroValue p) x /
                  quadraticDedekindZeroValue p) +
            tsum (fun p : QuadraticDedekindZeroIndex D =>
              integral (volume.restrict (Ioi x)) (Z p)) := by
        rw [((summable_quadraticDedekind_robinZeroKernel_div
          D hFieldERH (n := 2) (by norm_num) hx).mul_left
            (Robin1984.robinEndpointReweight x : Complex)).tsum_add
              hSumInt, tsum_mul_left]
      _ = _ := by
        rw [integral_tsum_of_summable_integral_norm hInt hNorm]
        congr 1
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only [Z]
        rw [tsum_mul_left])

end

end RobinBV.NumberField
