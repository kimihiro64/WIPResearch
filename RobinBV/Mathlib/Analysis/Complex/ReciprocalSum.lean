/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.GCongr
import RobinBV.Mathlib.Analysis.Complex.ReciprocalCorrelation

/-!
# Explicit finite reciprocal exponential-sum bounds

A finite Cauchy inequality keeps the complete Gram matrix. The existing
pointwise reciprocal correlation estimate bounds each off-diagonal entry
for equally spaced shifts. Exact endpoint blocks control the shift error.
The final bound has no additional analytic-source hypothesis. All real
positivity, natural cutoffs and small-increment conditions are explicit.

These bounds do not by themselves estimate a prime or composite count.
Their transfer to a signed sieve packet requires a separate counting proof.
-/

set_option autoImplicit false
open scoped Classical
namespace Complex

/-- Finite Cauchy bound with the full Gram matrix retained. This is the
input to a shift estimate for reciprocal phases in skew factor rows. -/
theorem norm_sum_sq_le_card_gram {i j : Type*} (s : Finset i) (t : Finset j)
    (a : i -> j -> Complex) :
    norm (s.sum (fun x => t.sum (a x)))^2 <=
      (s.card : Real)*t.sum (fun h => t.sum (fun k =>
        (s.sum (fun x => a x h * star (a x k))).re)) := by
  classical
  have hre (f : j -> Complex) : (t.sum f).re = t.sum (fun z => (f z).re) :=
    map_sum Complex.reAddGroupHom f t
  have him (f : j -> Complex) : (t.sum f).im = t.sum (fun z => (f z).im) :=
    map_sum Complex.imAddGroupHom f t
  have hres (f : i -> Complex) : (s.sum f).re = s.sum (fun z => (f z).re) :=
    map_sum Complex.reAddGroupHom f s
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : Real))
    (fun x => norm (t.sum (a x)))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hnorm := norm_sum_le s (fun x => t.sum (a x))
  have hnon : 0 <= s.sum (fun x => norm (t.sum (a x))) :=
    Finset.sum_nonneg (fun x _ => norm_nonneg _)
  have hsq : norm (s.sum (fun x => t.sum (a x)))^2 <=
      (s.card : Real)*s.sum (fun x => norm (t.sum (a x))^2) := by
    nlinarith [norm_nonneg (s.sum (fun x => t.sum (a x)))]
  have hpoint (x : i) : norm (t.sum (a x))^2 =
      t.sum (fun h => t.sum (fun k => (a x h * star (a x k)).re)) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hre, him]
    simp only [mul_re, star_def, conj_re, conj_im, mul_neg, sub_neg_eq_add]
    simp only [Finset.sum_add_distrib, Finset.sum_mul_sum]
  have he : s.sum (fun x => norm (t.sum (a x))^2) =
      t.sum (fun h => t.sum (fun k => (s.sum (fun x => a x h * star (a x k))).re)) := by
    simp_rw [hpoint, hres]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.sum_comm]
  rw [he] at hsq
  exact hsq

/-- Uniform diagonal and off-diagonal correlation bounds give a usable
finite energy bound; neither the candidate supply nor a prime count is used. -/
theorem norm_sum_sq_le_uniform_gram {i j : Type*} (s : Finset i) (t : Finset j)
    (a : i -> j -> Complex) (B C : Real)
    (hdiag : forall h, Membership.mem t h ->
      (s.sum (fun x => a x h * star (a x h))).re <= B)
    (hoff : forall h, Membership.mem t h -> forall k, Membership.mem t k ->
      Not (h = k) -> (s.sum (fun x => a x h * star (a x k))).re <= C) :
    norm (s.sum (fun x => t.sum (a x)))^2 <=
      (s.card : Real)*((t.card : Real)*B+((t.card : Real)^2-t.card)*C) := by
  classical
  have hrow : forall h, Membership.mem t h ->
      t.sum (fun k => (s.sum (fun x => a x h * star (a x k))).re) <=
        B+((t.card : Real)-1)*C := by
    intro h hh
    calc
      _ <= t.sum (fun k => if h = k then B else C) := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases he : h = k
        next => subst k; simpa using hdiag h hh
        next => simpa only [he, if_false] using hoff h hh k hk he
      _ = B+((t.card : Real)-1)*C := by
        have he (k : j) : (if h = k then B else C) =
            (if k = h then B-C else 0)+C := by
          by_cases hk : h = k
          next => subst k; simp
          next => simp [hk, Ne.symm hk]
        simp_rw [he]
        rw [Finset.sum_add_distrib]
        simp [hh] <;> ring
  have htotal := Finset.sum_le_sum hrow
  have hbound : t.sum (fun h => t.sum (fun k =>
      (s.sum (fun x => a x h * star (a x k))).re)) <=
        (t.card : Real)*B+((t.card : Real)^2-t.card)*C := by
    calc
      _ <= t.sum (fun _ => B+((t.card : Real)-1)*C) := htotal
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  exact (norm_sum_sq_le_card_gram s t a).trans
    (_root_.mul_le_mul_of_nonneg_left hbound (by positivity))

/-- An exact finite shift changes only the two endpoint blocks. -/
theorem norm_sum_shift_sub_le_two (a : Nat -> Complex) (N k : Nat)
    (ha : forall j, norm (a j) <= 1) :
    norm ((Finset.range N).sum (fun j => a (j+k))-(Finset.range N).sum a) <=
      2*(k : Real) := by
  have hNk := Finset.sum_range_add a N k
  have hkN := Finset.sum_range_add a k N
  have he : (Finset.range N).sum a+(Finset.range k).sum (fun j => a (N+j)) =
      (Finset.range k).sum a+(Finset.range N).sum (fun j => a (j+k)) := by
    rw [<- hNk]
    simpa only [Nat.add_comm] using hkN
  have hd : (Finset.range N).sum (fun j => a (j+k))-(Finset.range N).sum a =
      (Finset.range k).sum (fun j => a (N+j))-(Finset.range k).sum a := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using he.symm
  have hnorm (b : Nat -> Complex) (hb : forall j, norm (b j) <= 1) :
      norm ((Finset.range k).sum b) <= (k : Real) := by
    calc
      _ <= (Finset.range k).sum (fun j => norm (b j)) := norm_sum_le _ _
      _ <= (Finset.range k).sum (fun _ => (1 : Real)) :=
        Finset.sum_le_sum (fun j _ => hb j)
      _ = _ := by simp
  rw [hd]
  exact (norm_sub_le _ _).trans (by
    have h1 := hnorm (fun j => a (N+j)) (fun j => ha (N+j))
    have h2 := hnorm a ha
    linarith only [h1, h2])

/-- The aggregate endpoint cost is retained exactly when averaging equally
spaced shifts; there is no periodic or infinite-support substitution. -/
theorem norm_sum_le_shift_average_boundary (a : Nat -> Complex) (N H D : Nat)
    (ha : forall j, norm (a j) <= 1) :
    (H : Real)*norm ((Finset.range N).sum a) <=
      norm ((Finset.range N).sum (fun j => (Finset.range H).sum (fun h => a (j+h*D))))+
        (D : Real)*H*(H-1) := by
  let S := (Finset.range N).sum a
  let U := (Finset.range N).sum (fun j => (Finset.range H).sum (fun h => a (j+h*D)))
  have he : U-(H : Complex)*S = (Finset.range H).sum (fun h =>
      (Finset.range N).sum (fun j => a (j+h*D))-S) := by
    dsimp only [U]
    rw [Finset.sum_comm, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum : forall M : Nat, (Finset.range M).sum (fun h => (h : Real)) =
      (M : Real)*(M-1)/2 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hc : norm (U-(H : Complex)*S) <= (D : Real)*H*(H-1) := by
    rw [he]
    calc
      _ <= (Finset.range H).sum (fun h =>
          norm ((Finset.range N).sum (fun j => a (j+h*D))-S)) := norm_sum_le _ _
      _ <= (Finset.range H).sum (fun h => 2*((h*D : Nat) : Real)) :=
        Finset.sum_le_sum (fun h _ => norm_sum_shift_sub_le_two a N (h*D) ha)
      _ = (2*(D : Real))*(Finset.range H).sum (fun h => (h : Real)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        push_cast
        ring
      _ = _ := by rw [hsum]; ring
  have hid : (H : Complex)*S = U-(U-(H : Complex)*S) := by ring
  calc
    (H : Real)*norm S = norm ((H : Complex)*S) := by simp [norm_mul]
    _ = norm (U-(U-(H : Complex)*S)) := congrArg norm hid
    _ <= norm U+norm (U-(H : Complex)*S) := norm_sub_le _ _
    _ <= _ := by linarith only [hc]

/-- The product of two phases, with the second conjugated, is their phase difference. -/
theorem exp_phase_mul_star (a b : Real) :
    exp (I*(a : Complex))*star (exp (I*(b : Complex))) =
      exp (I*((a-b : Real) : Complex)) := by
  simp only [star_def, <- exp_conj, map_mul, conj_I, conj_ofReal]
  rw [<- exp_add]
  congr 1
  push_cast
  ring

/-- Pointwise off-diagonal correlation for evenly spaced reciprocal shifts. -/
theorem reciprocal_shift_gram_norm_le {Y P : Real} {N H D h k : Nat}
    (hY : 0 < Y) (hP : 0 < P) (hD : 0 < D)
    (hk : k < h) (hh : h < H)
    (hsmall : 2*Y*((H*D : Nat) : Real) <= Real.pi*P^3) :
    norm ((Finset.range N).sum (fun j =>
      exp (I*((Y/(P+j+h*D) : Real) : Complex))*
        star (exp (I*((Y/(P+j+k*D) : Real) : Complex))))) <=
      3*Real.pi*(P+N+H*D)^3/(2*Y*D) := by
  let L := (h-k)*D
  have hL : 0 < L := Nat.mul_pos (Nat.sub_pos_of_lt hk) hD
  have hDL : D <= L := by
    have ht : 1 <= h-k := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right D ht
  have hLH : L <= H*D := Nat.mul_le_mul_right D (by omega)
  have hLsum : k*D+L = h*D := by
    dsimp [L]
    rw [<- Nat.add_mul, Nat.add_sub_of_le hk.le]
  have hPn : 0 < P+(k*D : Nat) := by positivity
  have hbase : P^3 <= (P+(k*D : Nat))^3 := by
    gcongr
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hLHr : (L : Real) <= (H*D : Nat) := by exact_mod_cast hLH
  have hsmallL : 2*Y*(L : Real) <= Real.pi*(P+(k*D : Nat))^3 := by
    have h1 := _root_.mul_le_mul_of_nonneg_left hLHr (show 0 <= 2*Y by positivity)
    have h2 := _root_.mul_le_mul_of_nonneg_left hbase Real.pi_pos.le
    linarith only [h1, hsmall, h2]
  have hc := norm_sum_exp_reciprocal_difference_le Y (P+(k*D : Nat)) N L hY hPn hL hsmallL
  have hform (j : Nat) :
      exp (I*((Y/(P+j+h*D) : Real) : Complex))*
        star (exp (I*((Y/(P+j+k*D) : Real) : Complex))) =
          exp (I*((Y/(P+(k*D : Nat)+j+L)-Y/(P+(k*D : Nat)+j) : Real) : Complex)) := by
    rw [exp_phase_mul_star]
    have he1 : P+(k*D : Nat)+j+L = P+j+h*D := by
      have he : ((k*D : Nat) : Real)+(L : Real) = (h*D : Nat) := by exact_mod_cast hLsum
      push_cast at he
      push_cast
      linarith only [he]
    have he2 : P+(k*D : Nat)+j = P+j+k*D := by push_cast; ring
    rw [he1, he2]
  simp_rw [hform]
  have htop : P+(k*D : Nat)+N+L <= P+N+H*D := by
    have he : ((k*D : Nat) : Real)+(L : Real) = (h*D : Nat) := by exact_mod_cast hLsum
    have hi : ((h*D : Nat) : Real) <= (H*D : Nat) := by
      exact_mod_cast Nat.mul_le_mul_right D hh.le
    push_cast at he hi
    push_cast
    linarith only [he, hi]
  have hnum : 3*Real.pi*(P+(k*D : Nat)+N+L)^3 <= 3*Real.pi*(P+N+H*D)^3 := by
    gcongr
  have hden : 2*Y*(D : Real) <= 2*Y*(L : Real) := by
    exact _root_.mul_le_mul_of_nonneg_left (by exact_mod_cast hDL) (by positivity)
  calc
    _ <= 3*Real.pi*(P+(k*D : Nat)+N+L)^3/(2*Y*L) := hc
    _ <= 3*Real.pi*(P+N+H*D)^3/(2*Y*L) :=
      _root_.div_le_div_of_nonneg_right hnum (by positivity)
    _ <= _ := _root_.div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-- A complete pointwise energy estimate for shifted reciprocal phases.
Both diagonal and off-diagonal estimates are discharged here. -/
theorem reciprocal_shift_energy_le {Y P : Real} {N H D : Nat}
    (hY : 0 < Y) (hP : 0 < P) (hD : 0 < D)
    (hsmall : 2*Y*((H*D : Nat) : Real) <= Real.pi*P^3) :
    norm ((Finset.range N).sum (fun j => (Finset.range H).sum (fun h =>
      exp (I*((Y/(P+j+h*D) : Real) : Complex)))))^2 <=
        (N : Real)*((H : Real)*N+((H : Real)^2-H)*
          (3*Real.pi*(P+N+H*D)^3/(2*Y*D))) := by
  let a := fun j h : Nat => exp (I*((Y/(P+j+h*D) : Real) : Complex))
  let C := 3*Real.pi*(P+N+H*D)^3/(2*Y*D)
  have hdiag : forall h, Membership.mem (Finset.range H) h ->
      ((Finset.range N).sum (fun j => a j h * star (a j h))).re <= (N : Real) := by
    intro h _
    dsimp only [a]
    simp_rw [exp_phase_mul_star]
    simp
  have hsym (h k : Nat) :
      ((Finset.range N).sum (fun j => a j h * star (a j k))).re =
        ((Finset.range N).sum (fun j => a j k * star (a j h))).re := by
    have hr (f : Nat -> Complex) : ((Finset.range N).sum f).re =
        (Finset.range N).sum (fun j => (f j).re) := map_sum reAddGroupHom f _
    rw [hr, hr]
    apply Finset.sum_congr rfl
    intro j _
    simp only [mul_re, star_def, conj_re, conj_im]
    ring
  have hoff : forall h, Membership.mem (Finset.range H) h ->
      forall k, Membership.mem (Finset.range H) k -> Not (h = k) ->
        ((Finset.range N).sum (fun j => a j h * star (a j k))).re <= C := by
    intro h hh k hk hne
    by_cases horder : k < h
    next =>
      exact (re_le_norm _).trans (reciprocal_shift_gram_norm_le hY hP hD
        horder (Finset.mem_range.mp hh) hsmall)
    next =>
      rw [hsym]
      exact (re_le_norm _).trans (reciprocal_shift_gram_norm_le hY hP hD
        (by omega : h < k) (Finset.mem_range.mp hk) hsmall)
  simpa only [Finset.card_range] using
    norm_sum_sq_le_uniform_gram (Finset.range N) (Finset.range H) a (N : Real) C hdiag hoff

/-- Fully discharged reciprocal exponential-sum bound, including finite
shift endpoints. Division by H is justified only when H is positive. -/
theorem norm_reciprocal_sum_mul_shift_le {Y P : Real} {N H D : Nat}
    (hY : 0 < Y) (hP : 0 < P) (hD : 0 < D)
    (hsmall : 2*Y*((H*D : Nat) : Real) <= Real.pi*P^3) :
    (H : Real)*norm ((Finset.range N).sum (fun j =>
      exp (I*((Y/(P+j) : Real) : Complex)))) <=
        Real.sqrt ((N : Real)*((H : Real)*N+((H : Real)^2-H)*
          (3*Real.pi*(P+N+H*D)^3/(2*Y*D))))+
            (D : Real)*H*(H-1) := by
  let a := fun j : Nat => exp (I*((Y/(P+j) : Real) : Complex))
  let U := (Finset.range N).sum (fun j => (Finset.range H).sum (fun h =>
    exp (I*((Y/(P+j+h*D) : Real) : Complex))))
  let E := (N : Real)*((H : Real)*N+((H : Real)^2-H)*
    (3*Real.pi*(P+N+H*D)^3/(2*Y*D)))
  have ha : forall j, norm (a j) <= 1 := by
    intro j
    dsimp only [a]
    rw [mul_comm I]
    exact (norm_exp_ofReal_mul_I _).le
  have hb := norm_sum_le_shift_average_boundary a N H D ha
  simp only [a, Nat.cast_add, Nat.cast_mul, add_assoc] at hb
  have he : norm U^2 <= E := reciprocal_shift_energy_le hY hP hD hsmall
  have hE : 0 <= E := (sq_nonneg (norm U)).trans he
  have hroot : norm U <= Real.sqrt E := by
    nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg E, norm_nonneg U]
  have hU : norm ((Finset.range N).sum (fun j => (Finset.range H).sum (fun h =>
      exp (I*((Y/(P+(j+h*D)) : Real) : Complex))))) = norm U := by
    simp only [U, add_assoc]
  rw [hU] at hb
  apply hb.trans
  dsimp only [E] at hroot
  linarith only [hroot]

end Complex
