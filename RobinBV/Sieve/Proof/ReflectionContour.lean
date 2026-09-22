/- Reflection-contour identities feeding the square-corridor moment argument. -/
import RobinBV.Sieve.Assembly.SquareCorridorMomentCost

/-!
# Reflected zeta contour identities

The reflected amplitude is holomorphic away from the zeta pole, its residue
is explicit, and the rectangle integral is identified exactly. This is the
contour source consumed by the reflected moving-test energy argument.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

noncomputable def reflectionZetaAmplitude (k : Real -> Complex) (L g h : Real)
    (z : Complex) : Complex :=
  (L : Complex)^(z-1/2+Complex.I*(g : Complex)) *
    Zeta23.paperFT k ((z-1/2+Complex.I*(g : Complex))/Complex.I) *
    Complex.exp ((h : Complex)*(z-1/2+Complex.I*(g : Complex))^2)

noncomputable def reflectionZetaKernel (k : Real -> Complex) (L g h : Real)
    (z : Complex) : Complex :=
  reflectionZetaAmplitude k L g h z * riemannZeta z

theorem reflectionZetaAmplitude_differentiable {k : Real -> Complex}
    (hk : Continuous k) (hkc : HasCompactSupport k) {L : Real} (hL : 0 < L)
    (g h : Real) :
    Differentiable Complex (reflectionZetaAmplitude k L g h) := by
  have hp : Differentiable Complex (fun z : Complex =>
      (L : Complex)^(z-1/2+Complex.I*(g : Complex))) := by
    simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hL))]
    fun_prop
  have hf : Differentiable Complex (fun z : Complex =>
      Zeta23.paperFT k ((z-1/2+Complex.I*(g : Complex))/Complex.I)) :=
    (Zeta23.WeilEF.differentiable_paperFT hk hkc).comp (by fun_prop)
  exact (hp.mul hf).mul (by fun_prop)

theorem reflectionZetaKernel_holomorphic {k : Real -> Complex}
    (hk : Continuous k) (hkc : HasCompactSupport k) {L : Real} (hL : 0 < L)
    (g h : Real) :
    HolomorphicOn (reflectionZetaKernel k L g h)
      (Set.diff Set.univ ({1} : Set Complex)) := by
  intro z hz
  exact ((reflectionZetaAmplitude_differentiable hk hkc hL g h).differentiableAt.mul
    (differentiableAt_riemannZeta hz.2)).differentiableWithinAt

theorem reflectionZetaKernel_residue_limit {k : Real -> Complex}
    (hk : Continuous k) (hkc : HasCompactSupport k) {L : Real} (hL : 0 < L)
    (g h : Real) :
    Tendsto (fun z : Complex => (z-1)*reflectionZetaKernel k L g h z)
      (nhdsWithin 1 (Set.compl ({1} : Set Complex)))
      (nhds (reflectionZetaAmplitude k L g h 1)) := by
  have ha : ContinuousAt (reflectionZetaAmplitude k L g h) (1 : Complex) :=
    (reflectionZetaAmplitude_differentiable hk hkc hL g h).continuous.continuousAt
  have hh := riemannZeta_residue_one.mul (ha.tendsto.mono_left inf_le_left)
  simp only [one_mul] at hh
  have he : (fun z : Complex => ((z-1)*riemannZeta z)*reflectionZetaAmplitude k L g h z) =
      (fun z : Complex => (z-1)*reflectionZetaKernel k L g h z) := by
    funext z
    dsimp only [reflectionZetaKernel]
    ring
  rw [he] at hh
  exact hh

theorem reflectionZetaKernel_pole_remainder {k : Real -> Complex}
    (hk : Continuous k) (hkc : HasCompactSupport k) {L : Real} (hL : 0 < L)
    (g h : Real) :
    Asymptotics.IsBigO (nhdsWithin 1 (Set.compl ({1} : Set Complex)))
      (fun z : Complex => reflectionZetaKernel k L g h z -
        reflectionZetaAmplitude k L g h 1/(z-1))
      (fun _ : Complex => (1 : Complex)) := by
  cases ResidueOfTendsTo (U := Set.univ) univ_mem
      (reflectionZetaKernel_holomorphic hk hkc hL g h)
      (reflectionZetaKernel_residue_limit hk hkc hL g h) with
  | intro V hV =>
      cases hV with
      | intro hV hB =>
          cases hB with
          | intro C hC =>
              apply Asymptotics.IsBigO.of_bound C
              filter_upwards [sdiff_mem_nhdsWithin_compl hV ({1} : Set Complex)] with z hz
              have hb : norm (reflectionZetaKernel k L g h z -
                  reflectionZetaAmplitude k L g h 1*Inv.inv (z-1)) <= C :=
                hC (Set.mem_image_of_mem _ hz)
              simpa only [Pi.sub_apply, Pi.one_apply, norm_one, mul_one, div_eq_mul_inv] using hb

theorem reflection_zeta_rectangle {k : Real -> Complex}
    (hk : Continuous k) (hkc : HasCompactSupport k) {L : Real} (hL : 0 < L)
    (g h : Real) {a b R : Real} (ha : a < 1) (hb : 1 < b) (hR : 0 < R) :
    RectangleIntegral' (reflectionZetaKernel k L g h)
      (Complex.mk a (-R)) (Complex.mk b R) =
      reflectionZetaAmplitude k L g h 1 := by
  apply ResidueTheoremOnRectangleWithSimplePole'
    (p := (1 : Complex))
  next =>
    change a <= b
    linarith
  next =>
    change -R <= R
    linarith
  next =>
    rw [rectangle_mem_nhds_iff]
    change (Set.uIoo a b) (1 : Real) /\ (Set.uIoo (-R) R) (0 : Real)
    rw [Set.uIoo_of_le (show a <= b by linarith),
      Set.uIoo_of_le (show -R <= R by linarith)]
    exact And.intro (And.intro ha hb) (And.intro (by linarith) hR)
  next =>
    exact (reflectionZetaKernel_holomorphic hk hkc hL g h).mono
      (Set.sdiff_subset_sdiff_left (Set.subset_univ _))
  next =>
    exact reflectionZetaKernel_pole_remainder hk hkc hL g h

theorem reflectionZetaAmplitude_pole (k : Real -> Complex) (L g h : Real) :
    reflectionZetaAmplitude k L g h 1 =
      (L : Complex)^(1/2+Complex.I*(g : Complex)) *
        Zeta23.paperFT (Zeta23.WeilEF.tilt k (1/2)) g *
        Complex.exp ((h : Complex)*(1/2+Complex.I*(g : Complex))^2) := by
  have hf := Zeta23.WeilEF.Hfn_line k 1 g
  unfold Zeta23.WeilEF.Hfn at hf
  simp only [Complex.ofReal_one] at hf
  have he : (1 : Complex)+(g : Complex)*Complex.I-1/2 =
      1/2+Complex.I*(g : Complex) := by ring
  have hr : (1 : Real)-1/2 = 1/2 := by ring
  rw [he, hr] at hf
  unfold reflectionZetaAmplitude
  rw [show (1 : Complex)-1/2 = 1/2 by norm_num, hf]

theorem reflection_zeta_rectangle_explicit {k : Real -> Complex}
    (hk : Continuous k) (hkc : HasCompactSupport k) {L : Real} (hL : 0 < L)
    (g h : Real) {a b R : Real} (ha : a < 1) (hb : 1 < b) (hR : 0 < R) :
    RectangleIntegral' (reflectionZetaKernel k L g h)
      (Complex.mk a (-R)) (Complex.mk b R) =
      (L : Complex)^(1/2+Complex.I*(g : Complex)) *
        Zeta23.paperFT (Zeta23.WeilEF.tilt k (1/2)) g *
        Complex.exp ((h : Complex)*(1/2+Complex.I*(g : Complex))^2) := by
  rw [reflection_zeta_rectangle hk hkc hL g h ha hb hR, reflectionZetaAmplitude_pole]
