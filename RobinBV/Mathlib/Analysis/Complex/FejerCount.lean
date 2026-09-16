/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.Analysis.Complex.FejerKernel

/-!
# Finite interval counting from circle phase estimates

An exact finite Gram expansion converts off-diagonal phase bounds into a
uniform bound on the summed kernel. Integrated localization then majorizes
the number of phase points in a closed real interval, including both endpoint
enlargements and the full tail cost. The final theorem is cross-multiplied:
a normalized count upper bound additionally requires a positive mass factor.
Arithmetic phase estimates and any signed sieve transfer remain separate.
-/

set_option autoImplicit false

namespace Complex

theorem circle_phase_sum_shift_le {v : Type*} (s : Finset v) (x : v -> Real)
    (k : Int) (t : Real) :
    (s.sum (fun i => exp (I*(k : Complex)*((x i-t : Real) : Complex)))).re <=
      norm (s.sum (fun i => exp (I*(k : Complex)*(x i : Complex)))) := by
  have he : s.sum (fun i => exp (I*(k : Complex)*((x i-t : Real) : Complex))) =
      s.sum (fun i => exp (I*(k : Complex)*(x i : Complex))) * exp (-I*(k : Complex)*(t : Complex)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [<- exp_add]
    congr 1
    push_cast
    ring
  have hu : norm (exp (-I*(k : Complex)*(t : Complex))) = 1 := by
    have hh : -I*(k : Complex)*(t : Complex) = (((-(k : Real)*t) : Real) : Complex)*I := by
      push_cast
      ring
    rw [hh, norm_exp_ofReal_mul_I]
  calc
    _ <= norm (s.sum (fun i => exp (I*(k : Complex)*((x i-t : Real) : Complex)))) :=
      re_le_norm _
    _ = _ := by rw [he, norm_mul, hu, mul_one]

theorem sum_finiteFejerKernel_le {v : Type*} (s : Finset v) (x : v -> Real)
    (H : Nat) (hH : 1 <= H) (E : Real)
    (hE : forall j, j < H -> forall k, k < H -> Not (j=k) ->
      norm (s.sum (fun i => exp (I*(((j : Int)-k : Int) : Complex)*(x i : Complex)))) <= E)
    (t : Real) :
    s.sum (fun i => finiteFejerKernel H (x i-t)) <=
      (s.card : Real)+((H : Real)-1)*E := by
  classical
  have hre (f : Nat -> Complex) : ((Finset.range H).sum f).re =
      (Finset.range H).sum (fun j => (f j).re) := map_sum reAddGroupHom f _
  have hres (f : v -> Complex) : (s.sum f).re = s.sum (fun i => (f i).re) :=
    map_sum reAddGroupHom f s
  have hp (i : v) : norm (finiteCircleSum H (x i-t))^2 =
      (Finset.range H).sum (fun j => (Finset.range H).sum (fun k =>
        (exp (I*(((j : Int)-k : Int) : Complex)*((x i-t : Real) : Complex))).re)) := by
    have hh := congrArg Complex.re (finiteCircleSum_sq_eq_cross H (x i-t))
    simp only [ofReal_re] at hh
    simp_rw [hre] at hh
    exact hh
  have henergy : s.sum (fun i => norm (finiteCircleSum H (x i-t))^2) =
      (Finset.range H).sum (fun j => (Finset.range H).sum (fun k =>
        (s.sum (fun i => exp (I*(((j : Int)-k : Int) : Complex)*((x i-t : Real) : Complex)))).re)) := by
    simp_rw [hp, hres]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
  have hb (j : Nat) (hj : j < H) :
      (Finset.range H).sum (fun k =>
        (s.sum (fun i => exp (I*(((j : Int)-k : Int) : Complex)*((x i-t : Real) : Complex)))).re) <=
          (s.card : Real)+((H : Real)-1)*E := by
    calc
      _ <= (Finset.range H).sum (fun k => if j=k then (s.card : Real) else E) := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases he : j=k
        next => subst k; simp
        next =>
          rw [if_neg he]
          exact (circle_phase_sum_shift_le s x ((j : Int)-k) t).trans
            (hE j hj k (Finset.mem_range.mp hk) he)
      _ = _ := by
        have hi (k : Nat) : (if j=k then (s.card : Real) else E) =
            (if k=j then (s.card : Real)-E else 0)+E := by
          by_cases h : j=k
          next => subst k; simp
          next => simp [h, Ne.symm h]
        simp_rw [hi]
        rw [Finset.sum_add_distrib]
        simp [hj]
        ring
  have ht := Finset.sum_le_sum (fun j hj => hb j (Finset.mem_range.mp hj))
  rw [<- henergy] at ht
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at ht
  unfold finiteFejerKernel
  rw [<- Finset.sum_div]
  calc
    _ <= ((H : Real)*((s.card : Real)+((H : Real)-1)*E))/H :=
      div_le_div_of_nonneg_right ht (by positivity)
    _ = _ := by
      have hn : Not ((H : Real)=0) := by exact_mod_cast (show Not (H=0) by omega)
      field_simp

theorem finiteFejer_arc_mass_lower (H : Nat) (hH : 1 <= H)
    (a b x d : Real) (hd : 0 < d) (hdp : d <= Real.pi)
    (hax : a <= x) (hxb : x <= b) :
    2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi)) <=
      intervalIntegral (fun t : Real => finiteFejerKernel H (x-t))
        (a-d) (b+d) MeasureTheory.volume := by
  rw [intervalIntegral.integral_comp_sub_left]
  apply (integral_finiteFejerKernel_near H hH d hd hdp).trans
  apply intervalIntegral.integral_mono_interval (show x-(b+d) <= -d by linarith)
    (show -d <= d by linarith) (show d <= x-(a-d) by linarith)
  exacts [Filter.Eventually.of_forall (finiteFejerKernel_nonneg H),
    (continuous_finiteFejerKernel H).intervalIntegrable _ _]

theorem finiteFejer_arc_count_upper {v : Type*} (s : Finset v) (x : v -> Real)
    (H : Nat) (hH : 1 <= H) (E a b d : Real)
    (hab : a <= b) (hd : 0 < d) (hdp : d <= Real.pi)
    (hE : forall j, j < H -> forall k, k < H -> Not (j=k) ->
      norm (s.sum (fun i => exp (I*(((j : Int)-k : Int) : Complex)*(x i : Complex)))) <= E) :
    (2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi)))*
      ((s.filter (fun i => a <= x i /\ x i <= b)).card : Real) <=
        (b-a+2*d)*((s.card : Real)+((H : Real)-1)*E) := by
  classical
  let L : Real := 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi))
  let f : v -> Real -> Real := fun i t => finiteFejerKernel H (x i-t)
  have hc (i : v) : Continuous (f i) :=
    (continuous_finiteFejerKernel H).comp (continuous_const.sub continuous_id)
  have hi (i : v) : IntervalIntegrable (f i) MeasureTheory.volume (a-d) (b+d) :=
    (hc i).intervalIntegrable _ _
  have hn (i : v) : 0 <= intervalIntegral (f i) (a-d) (b+d) MeasureTheory.volume :=
    intervalIntegral.integral_nonneg (by linarith) (fun t ht => finiteFejerKernel_nonneg H (x i-t))
  have hl : L*((s.filter (fun i => a <= x i /\ x i <= b)).card : Real) <=
      s.sum (fun i => intervalIntegral (f i) (a-d) (b+d) MeasureTheory.volume) := by
    calc
      _ = (s.filter (fun i => a <= x i /\ x i <= b)).sum (fun _ => L) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ <= (s.filter (fun i => a <= x i /\ x i <= b)).sum
          (fun i => intervalIntegral (f i) (a-d) (b+d) MeasureTheory.volume) := by
        apply Finset.sum_le_sum
        intro i hi
        have hx := (Finset.mem_filter.mp hi).2
        exact finiteFejer_arc_mass_lower H hH a b (x i) d hd hdp hx.1 hx.2
      _ <= _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ s)
        (fun i hi hnot => hn i)
  have hsi : IntervalIntegrable (fun t => s.sum (fun i => f i t))
      MeasureTheory.volume (a-d) (b+d) :=
    (continuous_finsetSum _ (fun i hi => hc i)).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : Real => (s.card : Real)+((H : Real)-1)*E)
      MeasureTheory.volume (a-d) (b+d) := intervalIntegrable_const
  have hu := intervalIntegral.integral_mono_on (show a-d <= b+d by linarith)
    hsi hconst (fun t ht => sum_finiteFejerKernel_le s x H hH E hE t)
  rw [intervalIntegral.integral_finsetSum (fun i hmem => hi i)] at hu
  rw [intervalIntegral.integral_const] at hu
  simp only [smul_eq_mul] at hu
  exact (hl.trans hu).trans_eq (by ring)

theorem finiteFejer_mass_factor_pos (H : Nat) (hH : 1 <= H) (d : Real)
    (hd : 0 < d) (hgap : Real.pi < ((H : Real)+1)*d) :
    0 < 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi)) := by
  have hHr : 0 < (H : Real) := by exact_mod_cast (show 0 < H by omega)
  have he : 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi)) =
      (2*Real.pi*(((H : Real)+1)*d-Real.pi))/((H : Real)*d) := by
    field_simp [ne_of_gt hHr, ne_of_gt hd, ne_of_gt Real.pi_pos]
    ring
  rw [he]
  exact _root_.div_pos (mul_pos (by positivity) (sub_pos.mpr hgap)) (mul_pos hHr hd)

theorem finiteFejer_arc_count_div_upper {v : Type*} (s : Finset v) (x : v -> Real)
    (H : Nat) (hH : 1 <= H) (E a b d : Real)
    (hab : a <= b) (hd : 0 < d) (hdp : d <= Real.pi)
    (hgap : Real.pi < ((H : Real)+1)*d)
    (hE : forall j, j < H -> forall k, k < H -> Not (j=k) ->
      norm (s.sum (fun i => exp (I*(((j : Int)-k : Int) : Complex)*(x i : Complex)))) <= E) :
    ((s.filter (fun i => a <= x i /\ x i <= b)).card : Real) <=
      ((b-a+2*d)*((s.card : Real)+((H : Real)-1)*E)) /
        (2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi))) := by
  classical
  let A : Real := 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi))
  have hA : 0 < A := finiteFejer_mass_factor_pos H hH d hd hgap
  have hu := finiteFejer_arc_count_upper s x H hH E a b d hab hd hdp hE
  change A*_ <= _ at hu
  calc
    _ = (A*((s.filter (fun i => a <= x i /\ x i <= b)).card : Real))/A := by
      field_simp [ne_of_gt hA]
    _ <= _ := div_le_div_of_nonneg_right hu hA.le

theorem finiteFejer_arc_count_lower {v : Type*} (s : Finset v) (x : v -> Real)
    (H : Nat) (hH : 1 <= H) (E a b d : Real)
    (ha : 0 <= a) (hab : a <= b) (hb : b <= 2*Real.pi)
    (hd : 0 < d) (hdp : d <= Real.pi)
    (hgap : Real.pi < ((H : Real)+1)*d)
    (hx : forall i, Membership.mem s i -> 0 <= x i /\ x i <= 2*Real.pi)
    (hE : forall j, j < H -> forall k, k < H -> Not (j=k) ->
      norm (s.sum (fun i => exp (I*(((j : Int)-k : Int) : Complex)*(x i : Complex)))) <= E) :
    (2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi)))*(s.card : Real)-
      (2*Real.pi-(b-a)+4*d)*((s.card : Real)+((H : Real)-1)*E) <=
      (2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi)))*
        ((s.filter (fun i => a <= x i /\ x i <= b)).card : Real) := by
  classical
  let U := s.filter (fun i => a <= x i /\ x i <= b)
  let V := s.filter (fun i => 0 <= x i /\ x i <= a)
  let W := s.filter (fun i => b <= x i /\ x i <= 2*Real.pi)
  have hcover : forall i, Membership.mem s i ->
      Membership.mem (Union.union (Union.union U V) W) i := by
    intro i hi
    have hxi := hx i hi
    by_cases hia : a <= x i
    next =>
      by_cases hib : x i <= b
      next =>
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr (And.intro hi (And.intro hia hib))))
      next =>
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr (And.intro hi (And.intro (le_of_not_ge hib) hxi.2)))
    next =>
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr (And.intro hi (And.intro hxi.1 (le_of_not_ge hia)))))
  have hc : s.card <= U.card+V.card+W.card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcr : (s.card : Real) <= (U.card : Real)+(V.card : Real)+(W.card : Real) := by
    exact_mod_cast hc
  let A : Real := 2*Real.pi-2*(Real.pi^2/(H : Real)*(1/d-1/Real.pi))
  have hA : 0 < A := finiteFejer_mass_factor_pos H hH d hd hgap
  have hmul := mul_le_mul_of_nonneg_left hcr hA.le
  have hl := finiteFejer_arc_count_upper s x H hH E 0 a d ha hd hdp hE
  have hr := finiteFejer_arc_count_upper s x H hH E b (2*Real.pi) d hb hd hdp hE
  change A*(V.card : Real) <= _ at hl
  change A*(W.card : Real) <= _ at hr
  change A*(s.card : Real)-_ <= A*(U.card : Real)
  nlinarith

end Complex
