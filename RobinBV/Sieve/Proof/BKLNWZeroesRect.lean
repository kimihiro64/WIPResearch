/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import PrimeNumberTheoremAnd.IEANTN.KadiriEq12Helpers
import PrimeNumberTheoremAnd.IEANTN.PrimaryDefinitions
import PrimeNumberTheoremAnd.IEANTN.ZetaSummary
import RobinBV.Mathlib.Analysis.Complex.ZeroFreeBandBound

/-!
# Direct zero-rectangle consumers

This module promotes the finite, multiplicity-preserving zero-rectangle
bounds used by the height-band part of the almost-all argument.  The order
nonnegativity proof is supplied from the zeta definitions rather than from
the application theorem.
-/

set_option autoImplicit false
noncomputable section

theorem rob_bv_zeroes_rect_Icc_finite
    (a b c d : Real) :
    (riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d)).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  refine (riemannZeta.zeroes_on_Compact_finite' ?_).subset
    (Set.inter_subset_inter (Set.inter_subset_inter_right _
      (Set.preimage_mono Set.Ioo_subset_Icc_self)) le_rfl)
  exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
    (isCompact_Icc.prod isCompact_Icc)

theorem rob_bv_order_nonneg {rho : Complex} (hrho : Not (rho = 1)) :
    0 <= riemannZeta.order rho := by
  have han : AnalyticAt Complex riemannZeta rho :=
    riemannZeta_analyticOn_compl_one rho (by
      simpa [Set.mem_compl_iff] using hrho)
  unfold riemannZeta.order
  rw [han.meromorphicOrderAt_eq]
  cases h : analyticOrderAt riemannZeta rho with
  | top => simp
  | coe n =>
      simp only [ENat.map_coe, WithTop.untopD_coe]
      exact_mod_cast Nat.zero_le n

theorem rob_bv_zeroes_rect_multiplicity_bound
    (a b c d : Real) (f : Complex -> Complex) (w : Real)
    (hpoint : forall z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d),
      norm (f z) <= w) :
    let S := riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d)
    letI : Fintype S := (rob_bv_zeroes_rect_Icc_finite a b c d).fintype
    norm (tsum (fun z : S => f z * (riemannZeta.order z : Complex))) <=
      w * Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) := by
  let S := riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d)
  have hfin : S.Finite := rob_bv_zeroes_rect_Icc_finite a b c d
  letI : Fintype S := hfin.fintype
  dsimp
  rw [tsum_fintype]
  have horder : forall z : S, 0 <= ((riemannZeta.order z : Int) : Real) := by
    intro z
    have horderZ : 0 <= riemannZeta.order (z : Complex) := by
      apply rob_bv_order_nonneg
      intro hEq
      have hz : riemannZeta (z : Complex) = 0 := z.property.2.2
      rw [hEq] at hz
      exact (riemannZeta_ne_zero_of_one_le_re (by norm_num)) hz
    exact_mod_cast horderZ
  calc
    norm (Finset.univ.sum (fun z : S => f z * (riemannZeta.order z : Complex))) <=
        Finset.univ.sum (fun z : S => norm (f z * (riemannZeta.order z : Complex))) := by
      exact norm_sum_le Finset.univ (fun z : S => f z * (riemannZeta.order z : Complex))
    _ = Finset.univ.sum (fun z : S =>
          norm (f z) * ((riemannZeta.order z : Int) : Real)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [norm_mul]
      simp [abs_of_nonneg (horder z)]
    _ <= Finset.univ.sum (fun z : S =>
          w * ((riemannZeta.order z : Int) : Real)) := by
      exact Finset.sum_le_sum (fun z hz =>
        mul_le_mul_of_nonneg_right (hpoint z) (horder z))
    _ = w * Finset.univ.sum (fun z : S =>
          ((riemannZeta.order (z : Complex) : Int) : Real)) := by
      rw [Finset.mul_sum]

theorem rob_bv_finite_multiplicity_bound
    (S : Set Complex) (hfin : S.Finite) (f : Complex -> Complex)
    (w : Real) (hzero : forall z : S, riemannZeta (z : Complex) = 0)
    (hpoint : forall z : S, norm (f z) <= w) :
    letI : Fintype S := hfin.fintype
    norm (tsum (fun z : S => f z * (riemannZeta.order z : Complex))) <=
      w * Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) := by
  letI : Fintype S := hfin.fintype
  rw [tsum_fintype]
  have horder : forall z : S, 0 <= ((riemannZeta.order z : Int) : Real) := by
    intro z
    have horderZ : 0 <= riemannZeta.order (z : Complex) := by
      apply rob_bv_order_nonneg
      intro hEq
      have hz := hzero z
      rw [hEq] at hz
      exact (riemannZeta_ne_zero_of_one_le_re (by norm_num)) hz
    exact_mod_cast horderZ
  calc
    norm (Finset.univ.sum (fun z : S => f z * (riemannZeta.order z : Complex))) <=
        Finset.univ.sum (fun z : S => norm (f z * (riemannZeta.order z : Complex))) := by
      exact norm_sum_le Finset.univ (fun z : S => f z * (riemannZeta.order z : Complex))
    _ = Finset.univ.sum (fun z : S =>
          norm (f z) * ((riemannZeta.order z : Int) : Real)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [norm_mul]
      simp [abs_of_nonneg (horder z)]
    _ <= Finset.univ.sum (fun z : S =>
          w * ((riemannZeta.order z : Int) : Real)) := by
      exact Finset.sum_le_sum (fun z hz =>
        mul_le_mul_of_nonneg_right (hpoint z) (horder z))
    _ = w * Finset.univ.sum (fun z : S =>
          ((riemannZeta.order (z : Complex) : Int) : Real)) := by
      rw [Finset.mul_sum]

theorem rob_bv_zeroes_rect_singleton_multiplicity_bound
    (a b d : Real) (f : Complex -> Complex) (w M : Real)
    (hw : 0 <= w)
    (hpoint : forall z : riemannZeta.zeroes_rect (Set.Icc a b) ({d} : Set Real),
      norm (f z) <= w)
    (hmass :
      let S := riemannZeta.zeroes_rect (Set.Icc a b) ({d} : Set Real)
      let hfin : S.Finite :=
        (rob_bv_zeroes_rect_Icc_finite a b (d - 1) (d + 1)).subset (by
          intro z hz
          have hlow : d - 1 < (z : Complex).im := by
            have h := Set.mem_singleton_iff.mp hz.2.1
            linarith
          have hhigh : (z : Complex).im < d + 1 := by
            have h := Set.mem_singleton_iff.mp hz.2.1
            linarith
          exact And.intro hz.1 (And.intro (And.intro hlow hhigh) hz.2.2))
      letI : Fintype S := hfin.fintype
      Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) <= M) :
    norm (riemannZeta.zeroes_sum (Set.Icc a b) ({d} : Set Real)
      (fun z => f z)) <= w * M := by
  let S := riemannZeta.zeroes_rect (Set.Icc a b) ({d} : Set Real)
  let hfin : S.Finite :=
    (rob_bv_zeroes_rect_Icc_finite a b (d - 1) (d + 1)).subset (by
      intro z hz
      have hlow : d - 1 < (z : Complex).im := by
        have h := Set.mem_singleton_iff.mp hz.2.1
        linarith
      have hhigh : (z : Complex).im < d + 1 := by
        have h := Set.mem_singleton_iff.mp hz.2.1
        linarith
      exact And.intro hz.1 (And.intro (And.intro hlow hhigh) hz.2.2))
  letI : Fintype S := hfin.fintype
  have hmass' : Finset.univ.sum (fun z : S =>
      ((riemannZeta.order (z : Complex) : Int) : Real)) <= M := by
    exact hmass
  have hbound := rob_bv_finite_multiplicity_bound S hfin f w
    (fun z => z.property.2.2) (fun z => hpoint z)
  change norm (tsum (fun z : S =>
    f z * (riemannZeta.order z : Complex))) <= w * M
  exact hbound.trans (mul_le_mul_of_nonneg_left hmass'
    hw)

theorem rob_bv_zeroes_rect_zero_free_band
    (a b c d x y R : Real)
    (hx : 1 < x) (hy : 1 < y) (hR : 0 < R)
    (hheight : forall z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d),
      y <= norm (z : Complex))
    (hre : forall z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d),
      (z : Complex).re <= 1 - 1 / (R * Real.log y)) :
    let S := riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d)
    letI : Fintype S := (rob_bv_zeroes_rect_Icc_finite a b c d).fintype
    norm (tsum (fun z : S =>
      ((x : Complex) ^ ((z : Complex) - 1) / (z : Complex)) *
        (riemannZeta.order (z : Complex) : Complex))) <=
      (x ^ (-(1 / (R * Real.log y))) / y) *
        Finset.univ.sum (fun z : S =>
          ((riemannZeta.order (z : Complex) : Int) : Real)) := by
  have hpoint : forall z : riemannZeta.zeroes_rect (Set.Icc a b) (Set.Ioo c d),
      norm ((x : Complex) ^ ((z : Complex) - 1) / (z : Complex)) <=
        x ^ (-(1 / (R * Real.log y))) / y := by
    intro z
    exact Complex.norm_cpow_div_zero_free_bound hx hy (hheight z) hR (hre z)
  exact rob_bv_zeroes_rect_multiplicity_bound
    a b c d (fun rho => (x : Complex) ^ (rho - 1) / rho)
    (x ^ (-(1 / (R * Real.log y))) / y) hpoint

theorem rob_bv_zeroes_rect_zero_free_height_band
    (a b T lambda x R : Real) (k : Nat)
    (hT : 1 < T) (hlambda : 1 < lambda)
    (hyband : 1 < T / lambda ^ (k + 1))
    (hx : 1 < x) (hR : 0 < R)
    (hre : forall z : riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k)),
      (z : Complex).re <=
        1 - 1 / (R * Real.log (T / lambda ^ (k + 1)))) :
    let S := riemannZeta.zeroes_rect (Set.Icc a b)
      (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
    letI : Fintype S :=
      (rob_bv_zeroes_rect_Icc_finite a b
        (T / lambda ^ (k + 1)) (T / lambda ^ k)).fintype
    norm (tsum (fun z : S =>
      ((x : Complex) ^ ((z : Complex) - 1) / (z : Complex)) *
        (riemannZeta.order (z : Complex) : Complex))) <=
      (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
        (T / lambda ^ (k + 1))) *
        Finset.univ.sum (fun z : S =>
          ((riemannZeta.order (z : Complex) : Int) : Real)) := by
  dsimp
  apply rob_bv_zeroes_rect_zero_free_band
  next => exact hx
  next => exact hyband
  next => exact hR
  next =>
    intro z
    exact Complex.norm_ge_of_height_band hT hlambda
      (Set.mem_Ioo.mp z.property.2.1).1
  next =>
    intro z
    exact hre z

theorem rob_bv_zeroes_rect_zero_free_height_band_count
    (a b T lambda x R M : Real) (k : Nat)
    (hT : 1 < T) (hlambda : 1 < lambda)
    (hyband : 1 < T / lambda ^ (k + 1))
    (hx : 1 < x) (hR : 0 < R)
    (hre : forall z : riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k)),
      (z : Complex).re <=
        1 - 1 / (R * Real.log (T / lambda ^ (k + 1))))
    (hmass :
      let S := riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
      letI : Fintype S :=
        (rob_bv_zeroes_rect_Icc_finite a b
          (T / lambda ^ (k + 1)) (T / lambda ^ k)).fintype
      Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) <= M) :
    let S := riemannZeta.zeroes_rect (Set.Icc a b)
      (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
    letI : Fintype S :=
      (rob_bv_zeroes_rect_Icc_finite a b
        (T / lambda ^ (k + 1)) (T / lambda ^ k)).fintype
    norm (tsum (fun z : S =>
      ((x : Complex) ^ ((z : Complex) - 1) / (z : Complex)) *
        (riemannZeta.order (z : Complex) : Complex))) <=
      (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
        (T / lambda ^ (k + 1))) * M := by
  dsimp at hmass
  dsimp
  have hband := rob_bv_zeroes_rect_zero_free_height_band
    a b T lambda x R k hT hlambda hyband hx hR hre
  have hnonneg : 0 <=
      x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
        (T / lambda ^ (k + 1)) := by
    positivity
  exact hband.trans (mul_le_mul_of_nonneg_left hmass hnonneg)

theorem rob_bv_zeroes_rect_zero_free_height_band_sum
    (a b T lambda x R M : Real) (k : Nat)
    (hT : 1 < T) (hlambda : 1 < lambda)
    (hyband : 1 < T / lambda ^ (k + 1))
    (hx : 1 < x) (hR : 0 < R)
    (hre : forall z : riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k)),
      (z : Complex).re <=
        1 - 1 / (R * Real.log (T / lambda ^ (k + 1))))
    (hmass :
      let S := riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
      letI : Fintype S :=
        (rob_bv_zeroes_rect_Icc_finite a b
          (T / lambda ^ (k + 1)) (T / lambda ^ k)).fintype
      Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) <= M) :
    norm (riemannZeta.zeroes_sum (Set.Icc a b)
      (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
      (fun z => (x : Complex) ^ (z - 1) / z)) <=
      (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
        (T / lambda ^ (k + 1))) * M := by
  let S := riemannZeta.zeroes_rect (Set.Icc a b)
    (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
  have hfin : S.Finite := rob_bv_zeroes_rect_Icc_finite a b
    (T / lambda ^ (k + 1)) (T / lambda ^ k)
  letI : Fintype S := hfin.fintype
  have hband := rob_bv_zeroes_rect_zero_free_height_band_count
    a b T lambda x R M k hT hlambda hyband hx hR hre hmass
  dsimp at hband
  change norm (tsum (fun z : S =>
    (x : Complex) ^ ((z : Complex) - 1) / (z : Complex) *
      (riemannZeta.order (z : Complex) : Complex))) <= _ at hband
  rw [zeroes_sum_eq_toFinset_sum _ hfin]
  rw [(Finset.tsum_subtype' hfin.toFinset
    (fun z => (x : Complex) ^ (z - 1) / z *
      (riemannZeta.order z : Complex))).symm]
  rw [hfin.coe_toFinset]
  simpa using hband

theorem rob_bv_height_Ioc_split (c d : Real) (hcd : c < d) :
    Set.Ioc c d = Set.union (Set.Ioo c d) ({d} : Set Real) := by
  ext y
  constructor
  next =>
    intro hy
    have hycd := Set.mem_Ioc.mp hy
    by_cases hyd : y = d
    next => exact Or.inr (Set.mem_singleton_iff.mpr hyd)
    next =>
      exact Or.inl (Set.mem_Ioo.mpr
        (And.intro hycd.1 (lt_of_le_of_ne hycd.2 hyd)))
  next =>
    intro hy
    rcases hy with hy | hy
    next =>
      have hy' := Set.mem_Ioo.mp hy
      exact Set.mem_Ioc.mpr (And.intro hy'.1 hy'.2.le)
    next =>
      have hy' := Set.mem_singleton_iff.mp hy
      subst y
      exact Set.mem_Ioc.mpr (And.intro hcd (le_refl d))

theorem rob_bv_zeroes_sum_Ioc_split
    (a b c d : Real) (hcd : c < d) (g : Complex -> Complex) :
    riemannZeta.zeroes_sum (Set.Icc a b) (Set.Ioc c d) g =
      riemannZeta.zeroes_sum (Set.Icc a b) (Set.Ioo c d) g +
        riemannZeta.zeroes_sum (Set.Icc a b) ({d} : Set Real) g := by
  let I : Set Real := Set.Icc a b
  let J1 : Set Real := Set.Ioo c d
  let J2 : Set Real := ({d} : Set Real)
  let S1 := riemannZeta.zeroes_rect I J1
  let S2 := riemannZeta.zeroes_rect I J2
  let S := riemannZeta.zeroes_rect I (Set.Ioc c d)
  have hS1 : S1.Finite := by
    dsimp [S1, I, J1]
    exact rob_bv_zeroes_rect_Icc_finite a b c d
  have hS : S.Finite := by
    have hbig := rob_bv_zeroes_rect_Icc_finite a b (c - 1) (d + 1)
    apply hbig.subset
    intro z hz
    have hz1 := hz.2.1
    have hlow : c - 1 < (z : Complex).im := by
      have h := (Set.mem_Ioc.mp hz1).1
      linarith
    have hhigh : (z : Complex).im < d + 1 := by
      have h := (Set.mem_Ioc.mp hz1).2
      linarith
    exact And.intro hz.1 (And.intro (And.intro hlow hhigh) hz.2.2)
  have hS2 : S2.Finite := by
    apply hS.subset
    intro z hz
    have hdmem : (z : Complex).im = d :=
      Set.mem_singleton_iff.mp hz.2.1
    have hcdz : c < (z : Complex).im := by simpa [hdmem] using hcd
    exact And.intro hz.1
      (And.intro (Set.mem_Ioc.mpr (And.intro hcdz hdmem.le)) hz.2.2)
  have hunion : S = Set.union S1 S2 := by
    dsimp [S, S1, S2, I, J1, J2]
    rw [rob_bv_height_Ioc_split c d hcd]
    ext z
    simp [riemannZeta.zeroes_rect, Set.union]
    tauto
  have hdisj : Disjoint S1 S2 := by
    apply Set.disjoint_left.mpr
    intro z hz1 hz2
    have hlt := (Set.mem_Ioo.mp hz1.2.1).2
    have heq := Set.mem_singleton_iff.mp hz2.2.1
    linarith
  simp only [riemannZeta.zeroes_sum]
  change tsum (fun z : S => g z * (riemannZeta.order z : Complex)) = _
  rw [hunion]
  exact Summable.tsum_union_disjoint hdisj
    (hS1.summable (fun z => g z * (riemannZeta.order z : Complex)))
    (hS2.summable (fun z => g z * (riemannZeta.order z : Complex)))

theorem rob_bv_zeroes_sum_Ioc_bound
    (a b c d : Real) (f : Complex -> Complex)
    (wopen wend Mopen Mend : Real) (hcd : c < d)
    (hopen : norm (riemannZeta.zeroes_sum (Set.Icc a b)
      (Set.Ioo c d) f) <= wopen * Mopen)
    (hend : norm (riemannZeta.zeroes_sum (Set.Icc a b)
      ({d} : Set Real) f) <= wend * Mend) :
    norm (riemannZeta.zeroes_sum (Set.Icc a b)
      (Set.Ioc c d) f) <= wopen * Mopen + wend * Mend := by
  rw [rob_bv_zeroes_sum_Ioc_split a b c d hcd f]
  calc
    norm (riemannZeta.zeroes_sum (Set.Icc a b) (Set.Ioo c d) f +
      riemannZeta.zeroes_sum (Set.Icc a b) ({d} : Set Real) f) <=
        norm (riemannZeta.zeroes_sum (Set.Icc a b) (Set.Ioo c d) f) +
          norm (riemannZeta.zeroes_sum (Set.Icc a b) ({d} : Set Real) f) := by
      exact norm_add_le _ _
    _ <= wopen * Mopen + wend * Mend := by
      exact add_le_add hopen hend

theorem rob_bv_zeroes_rect_zero_free_height_band_Ioc_sum
    (a b T lambda x R M wend Mend : Real) (k : Nat)
    (hT : 1 < T) (hlambda : 1 < lambda)
    (hyband : 1 < T / lambda ^ (k + 1))
    (hx : 1 < x) (hR : 0 < R)
    (hcd : T / lambda ^ (k + 1) < T / lambda ^ k)
    (hre : forall z : riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k)),
      (z : Complex).re <=
        1 - 1 / (R * Real.log (T / lambda ^ (k + 1))))
    (hmass :
      let S := riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
      letI : Fintype S :=
        (rob_bv_zeroes_rect_Icc_finite a b
          (T / lambda ^ (k + 1)) (T / lambda ^ k)).fintype
      Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) <= M)
    (hwEnd : 0 <= wend)
    (hpointEnd : forall z : riemannZeta.zeroes_rect (Set.Icc a b)
        ({T / lambda ^ k} : Set Real),
      norm ((x : Complex) ^ ((z : Complex) - 1) / z) <= wend)
    (hmassEnd :
      let S := riemannZeta.zeroes_rect (Set.Icc a b)
        ({T / lambda ^ k} : Set Real)
      let hfin : S.Finite :=
        (rob_bv_zeroes_rect_Icc_finite a b
          (T / lambda ^ k - 1) (T / lambda ^ k + 1)).subset (by
            intro z hz
            have hlow : T / lambda ^ k - 1 < (z : Complex).im := by
              have h := Set.mem_singleton_iff.mp hz.2.1
              linarith
            have hhigh : (z : Complex).im < T / lambda ^ k + 1 := by
              have h := Set.mem_singleton_iff.mp hz.2.1
              linarith
            exact And.intro hz.1
              (And.intro (And.intro hlow hhigh) hz.2.2))
      letI : Fintype S := hfin.fintype
      Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) <= Mend) :
    norm (riemannZeta.zeroes_sum (Set.Icc a b)
      (Set.Ioc (T / lambda ^ (k + 1)) (T / lambda ^ k))
      (fun z => (x : Complex) ^ (z - 1) / z)) <=
      (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
        (T / lambda ^ (k + 1))) * M + wend * Mend := by
  have hopen := rob_bv_zeroes_rect_zero_free_height_band_sum
    a b T lambda x R M k hT hlambda hyband hx hR hre hmass
  have hend := rob_bv_zeroes_rect_singleton_multiplicity_bound
    a b (T / lambda ^ k)
      (fun z => (x : Complex) ^ (z - 1) / z) wend Mend hwEnd
      hpointEnd hmassEnd
  exact rob_bv_zeroes_sum_Ioc_bound a b
    (T / lambda ^ (k + 1)) (T / lambda ^ k)
    (fun z => (x : Complex) ^ (z - 1) / z)
    (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
      (T / lambda ^ (k + 1))) wend M Mend hcd hopen hend

/-!
# Finite zero-free height-band aggregation

This theorem applies the endpoint-safe multiplicity estimate to a finite
family of dyadic height bands.  The supplied band bounds remain explicit,
so no unproved density theorem is hidden in the consumer.
-/

theorem rob_bv_zeroes_rect_zero_free_height_band_finite_aggregation
    {K : Nat} (a b T lambda x R : Real)
    (bound : Nat -> Real)
    (hband : forall k, k < K ->
      norm (riemannZeta.zeroes_sum (Set.Icc a b)
        (Set.Ioc (T / lambda ^ (k + 1)) (T / lambda ^ k))
        (fun z => (x : Complex) ^ (z - 1) / z)) <= bound k) :
    norm (Finset.sum (Finset.range K) (fun k =>
      riemannZeta.zeroes_sum (Set.Icc a b)
        (Set.Ioc (T / lambda ^ (k + 1)) (T / lambda ^ k))
        (fun z => (x : Complex) ^ (z - 1) / z))) <=
      Finset.sum (Finset.range K) bound := by
  calc
    norm (Finset.sum (Finset.range K) (fun k =>
        riemannZeta.zeroes_sum (Set.Icc a b)
          (Set.Ioc (T / lambda ^ (k + 1)) (T / lambda ^ k))
          (fun z => (x : Complex) ^ (z - 1) / z))) <=
        Finset.sum (Finset.range K) (fun k =>
          norm (riemannZeta.zeroes_sum (Set.Icc a b)
            (Set.Ioc (T / lambda ^ (k + 1)) (T / lambda ^ k))
            (fun z => (x : Complex) ^ (z - 1) / z))) := by
      exact norm_sum_le (Finset.range K) (fun k =>
        riemannZeta.zeroes_sum (Set.Icc a b)
          (Set.Ioc (T / lambda ^ (k + 1)) (T / lambda ^ k))
          (fun z => (x : Complex) ^ (z - 1) / z))
    _ <= Finset.sum (Finset.range K) bound := by
      exact Finset.sum_le_sum (fun k hk =>
        hband k (Finset.mem_range.mp hk))

/-!
# Positive-height density substitution

A finite zero set inside the strict positive rectangle is bounded by the
weighted positive-height counting function N'.  The proof keeps the strict
real-part and height endpoints and carries the zeta order as multiplicity.
-/

theorem rob_bv_positive_zero_mass_le_NPrime
    (sigma d : Real) (A : Finset Complex)
    (hA : forall z, Membership.mem A z ->
      sigma < z.re /\ z.re < 1 /\ 0 < z.im /\ z.im < d /\
        riemannZeta z = 0) :
    A.sum (fun z => ((riemannZeta.order z : Int) : Real)) <=
      riemannZeta.N' sigma d := by
  let B := riemannZeta.zeroes_rect (Set.Ioo sigma 1) (Set.Ioo 0 d)
  have hfin : B.Finite := by
    apply (rob_bv_zeroes_rect_Icc_finite (sigma - 1) 1 0 d).subset
    intro z hz
    have hzre := hz.1
    have hzim := hz.2.1
    have hlow : sigma - 1 <= (z : Complex).re := by
      have hsig := (Set.mem_Ioo.mp hzre).1
      linarith
    have hhigh : (z : Complex).re <= 1 := (Set.mem_Ioo.mp hzre).2.le
    have hzero := And.intro hlow hhigh
    exact And.intro hzero (And.intro hzim hz.2.2)
  letI : Fintype B := hfin.fintype
  let w : Complex -> Real := fun z =>
    ((riemannZeta.order z : Int) : Real)
  have hBnonneg : forall z : B, 0 <= w (z : Complex) := by
    intro z
    change 0 <= ((riemannZeta.order (z : Complex) : Int) : Real)
    have horder : 0 <= riemannZeta.order (z : Complex) := by
      apply rob_bv_order_nonneg
      intro hEq
      have hzeta : riemannZeta (z : Complex) = 0 := z.property.2.2
      rw [hEq] at hzeta
      exact (riemannZeta_ne_zero_of_one_le_re (by norm_num)) hzeta
    exact_mod_cast horder
  have hsubset : forall z, Membership.mem A z ->
      Membership.mem (Finset.univ.image (fun z : B => (z : Complex))) z := by
    intro z hz
    have hzA := hA z hz
    have hzB : Membership.mem B z := by
      exact And.intro (Set.mem_Ioo.mpr (And.intro hzA.1 hzA.2.1))
        (And.intro (Set.mem_Ioo.mpr
          (And.intro hzA.2.2.1 hzA.2.2.2.1)) hzA.2.2.2.2)
    rw [Finset.mem_image]
    exact Exists.intro (Subtype.mk z hzB)
      (And.intro (Finset.mem_univ _) rfl)
  have himage : (Finset.univ.image (fun z : B => (z : Complex))).sum w =
      Finset.univ.sum (fun z : B => w (z : Complex)) := by
    rw [Finset.sum_image]
    intro z hz y hy hzy
    exact Subtype.ext hzy
  have hsum : A.sum w <=
      (Finset.univ.image (fun z : B => (z : Complex))).sum w := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro z hz hznot
    rw [Finset.mem_image] at hz
    cases hz with
    | intro y hy =>
        cases hy with
        | intro hy hzy =>
            cases hzy
            exact hBnonneg y
  have hN : riemannZeta.N' sigma d =
      Finset.univ.sum (fun z : B => w (z : Complex)) := by
    unfold riemannZeta.N' riemannZeta.zeroes_sum
    simp [B, w]
  rw [hN]
  exact hsum.trans_eq himage

/-!
# Density-bound consumer

This corollary substitutes a proved zero-density structure into the finite
positive-height mass estimate.  Its threshold and sigma-range hypotheses are
kept visible at the consumer boundary.
-/

def rob_bv_density_T0 : zero_density_bound -> Real
  | zero_density_bound.mk t s c1 c2 p q b => t

def rob_bv_density_range : zero_density_bound -> Set Real
  | zero_density_bound.mk t s c1 c2 p q b => s

theorem rob_bv_positive_zero_mass_le_density_bound
    (sigma d : Real) (A : Finset Complex) (ZDB : zero_density_bound)
    (hA : forall z, Membership.mem A z ->
      sigma < z.re /\ z.re < 1 /\ 0 < z.im /\ z.im < d /\
        riemannZeta z = 0)
    (hT0 : rob_bv_density_T0 ZDB <= d)
    (hsigma : Membership.mem (rob_bv_density_range ZDB) sigma) :
    A.sum (fun z => ((riemannZeta.order z : Int) : Real)) <=
      ZDB.N sigma d := by
  have hmass := rob_bv_positive_zero_mass_le_NPrime sigma d A hA
  cases ZDB with
  | mk t s c1 c2 p q hbound =>
      have hcount := hbound d hT0 sigma hsigma
      exact hmass.trans (by simpa [zero_density_bound.N] using hcount)

/-!
# Density substitution on zero-rectangle subtypes

This adapter changes the finite complex-set density consumer into the exact
subtype sum used by the multiplicity packet.  The strict endpoint premises
are explicit and are not inferred from a closed rectangle.
-/

theorem rob_bv_zeroes_rect_mass_le_density_bound
    (sigma d : Real) (S : Set Complex) (hfin : S.Finite)
    (hzero : forall z : S, riemannZeta (z : Complex) = 0)
    (hsigma : forall z : S, sigma < (z : Complex).re)
    (hupper : forall z : S, (z : Complex).re < 1)
    (hpositive : forall z : S, 0 < (z : Complex).im)
    (hheight : forall z : S, (z : Complex).im < d)
    (ZDB : zero_density_bound)
    (hT0 : rob_bv_density_T0 ZDB <= d)
    (hrange : Membership.mem (rob_bv_density_range ZDB) sigma) :
    letI : Fintype S := hfin.fintype
    Finset.univ.sum (fun z : S =>
      ((riemannZeta.order (z : Complex) : Int) : Real)) <= ZDB.N sigma d := by
  letI : Fintype S := hfin.fintype
  let A : Finset Complex := Finset.univ.image (fun z : S => (z : Complex))
  have hA : forall z, Membership.mem A z ->
      sigma < z.re /\ z.re < 1 /\ 0 < z.im /\ z.im < d /\
        riemannZeta z = 0 := by
    intro z hz
    rw [Finset.mem_image] at hz
    cases hz with
    | intro y hy =>
        cases hy with
        | intro hy hzy =>
            cases hzy
            exact And.intro (hsigma y)
              (And.intro (hupper y)
                (And.intro (hpositive y)
                  (And.intro (hheight y) (hzero y))))
  have hmass := rob_bv_positive_zero_mass_le_density_bound
    sigma d A ZDB hA hT0 hrange
  have himage : A.sum (fun z =>
      ((riemannZeta.order z : Int) : Real)) =
      Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) := by
    unfold A
    rw [Finset.sum_image]
    intro z hz y hy hzy
    exact Subtype.ext hzy
  rw [himage] at hmass
  exact hmass

/-!
# Density-substituted zero-free band

This is the endpoint-safe band consumer used by the A.12 height partition.
The zero-density threshold, sigma range, real-part buffer, and both height
buffers are explicit; the conclusion retains the order-weighted mass.
-/

theorem rob_bv_zeroes_rect_zero_free_height_band_count_from_density
    (a b T lambda x R sigma d : Real) (k : Nat)
    (ZDB : zero_density_bound)
    (hT : 1 < T) (hlambda : 1 < lambda)
    (hyband : 1 < T / lambda ^ (k + 1))
    (hx : 1 < x) (hR : 0 < R)
    (hre : forall z : riemannZeta.zeroes_rect (Set.Icc a b)
        (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k)),
      (z : Complex).re <=
        1 - 1 / (R * Real.log (T / lambda ^ (k + 1))))
    (hsigma : sigma < a) (hb : b < 1)
    (hupper : T / lambda ^ k < d)
    (hT0 : rob_bv_density_T0 ZDB <= d)
    (hrange : Membership.mem (rob_bv_density_range ZDB) sigma) :
    let S := riemannZeta.zeroes_rect (Set.Icc a b)
      (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
    letI : Fintype S :=
      (rob_bv_zeroes_rect_Icc_finite a b
        (T / lambda ^ (k + 1)) (T / lambda ^ k)).fintype
    norm (tsum (fun z : S =>
      ((x : Complex) ^ ((z : Complex) - 1) / (z : Complex)) *
        (riemannZeta.order (z : Complex) : Complex))) <=
      (x ^ (-(1 / (R * Real.log (T / lambda ^ (k + 1))))) /
        (T / lambda ^ (k + 1))) * ZDB.N sigma d := by
  let S := riemannZeta.zeroes_rect (Set.Icc a b)
    (Set.Ioo (T / lambda ^ (k + 1)) (T / lambda ^ k))
  have hfin : S.Finite := rob_bv_zeroes_rect_Icc_finite a b
    (T / lambda ^ (k + 1)) (T / lambda ^ k)
  have hmass :
      letI : Fintype S := hfin.fintype
      Finset.univ.sum (fun z : S =>
        ((riemannZeta.order (z : Complex) : Int) : Real)) <= ZDB.N sigma d := by
    letI : Fintype S := hfin.fintype
    refine rob_bv_zeroes_rect_mass_le_density_bound sigma d S hfin ?_ ?_ ?_ ?_ ?_ ZDB hT0 hrange
    next =>
      intro z
      exact z.property.2.2
    next =>
      intro z
      have hz := (Set.mem_Icc.mp z.property.1).1
      exact lt_of_lt_of_le hsigma hz
    next =>
      intro z
      exact lt_of_le_of_lt (Set.mem_Icc.mp z.property.1).2 hb
    next =>
      intro z
      exact lt_trans (by positivity) (Set.mem_Ioo.mp z.property.2.1).1
    next =>
      intro z
      exact lt_trans (Set.mem_Ioo.mp z.property.2.1).2 hupper
  dsimp
  exact rob_bv_zeroes_rect_zero_free_height_band_count
    a b T lambda x R (ZDB.N sigma d) k hT hlambda hyband hx hR hre hmass
