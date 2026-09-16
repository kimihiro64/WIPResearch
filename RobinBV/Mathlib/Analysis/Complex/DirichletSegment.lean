/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RobinBV.Mathlib.Analysis.Complex.KusminLandau

/-!
# First-derivative bounds for Dirichlet segments

Positive decreasing logarithmic angular increments satisfy the finite
Kusmin--Landau hypotheses. Nonnegative decreasing real power weights
have endpoint norm plus total variation equal to their initial value.
Conjugation treats both imaginary-part signs without discarding phases.

The complete complex-power segment bound is specialized to the exact
complement between floor(T) and ceil(T^(9/8)), including an empty tail.
All constants in that tail bound are explicit. No zeta-zero, prime-count,
or zero-density hypothesis occurs in this module.
-/

set_option autoImplicit false

namespace Real

/-- The positive unit logarithmic increment lies between its two reciprocal endpoint bounds. -/
theorem log_unit_increment_bounds {a : Real} (ha : 0 < a) :
    1/(a+1) <= log (a+1)-log a /\ log (a+1)-log a <= 1/a := by
  have ha1 : 0 < a+1 := by linarith
  have hratio : 0 < (a+1)/a := div_pos ha1 ha
  have hlog := log_div ha1.ne' ha.ne'
  have hlo := one_sub_inv_le_log_of_pos hratio
  have hhi := log_le_sub_one_of_pos hratio
  rw [hlog] at hlo hhi
  have helo : 1-((a+1)/a)^(-1 : Int) = 1/(a+1) := by
    simp only [zpow_neg_one]
    field_simp
    <;> ring
  have hehi : (a+1)/a-1 = 1/a := by field_simp; ring
  simp only [zpow_neg_one] at helo
  rw [helo] at hlo
  rw [hehi] at hhi
  exact And.intro hlo hhi

/-- Unit logarithmic increments decrease along every positive translated integer sequence. -/
theorem log_unit_increment_antitone {M : Real} (hM : 0 < M) :
    Antitone (fun j : Nat => log (M+((j+1 : Nat) : Real))-log (M+(j : Real))) := by
  have he (j : Nat) :
      log (M+((j+1 : Nat) : Real))-log (M+(j : Real)) =
        log (1+1/(M+(j : Real))) := by
    have ha : 0 < M+(j : Real) := by positivity
    have ha1 : 0 < M+(j : Real)+1 := by positivity
    simp only [Nat.cast_add, Nat.cast_one, <- add_assoc]
    rw [<- log_div ha1.ne' ha.ne']
    congr 1
    field_simp
    <;> ring
  intro i j hij
  dsimp only
  rw [he i, he j]
  apply log_le_log (by positivity)
  have hijR : (i : Real) <= j := by exact_mod_cast hij
  exact add_le_add (le_refl 1)
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith))

end Real

namespace Complex

/-- An explicit first-derivative bound for a positive logarithmic phase. -/
theorem norm_sum_log_phase_le {M t : Real} (hM : 0 < M) (ht : 0 < t)
    (htM : t <= 2*M) (N : Nat) :
    norm ((Finset.range N).sum (fun j =>
      exp (I*Complex.ofReal (t*Real.log (M+(j : Real)))))) <=
      3*Real.pi*(M+(N : Real))/t := by
  let f : Nat -> Real := fun j => t*Real.log (M+(j : Real))
  have hinc (j : Nat) : f (j+1)-f j =
      t*(Real.log (M+(j : Real)+1)-Real.log (M+(j : Real))) := by
    dsimp [f]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hpos (j : Nat) : 0 < f (j+1)-f j := by
    rw [hinc]
    have h := (Real.log_unit_increment_bounds
      (show 0 < M+(j : Real) by positivity)).1
    have hp : 0 < 1/(M+(j : Real)+1) := by positivity
    exact mul_pos ht (hp.trans_le h)
  have hpi (j : Nat) : f (j+1)-f j <= Real.pi := by
    rw [hinc]
    have h := (Real.log_unit_increment_bounds
      (show 0 < M+(j : Real) by positivity)).2
    calc
      _ <= t*(1/(M+(j : Real))) := mul_le_mul_of_nonneg_left h ht.le
      _ <= t*(1/M) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by norm_num) hM
          (le_add_of_nonneg_right (Nat.cast_nonneg j))) ht.le
      _ = t/M := by ring
      _ <= (2*M)/M := div_le_div_of_nonneg_right htM hM.le
      _ = 2 := by field_simp
      _ <= Real.pi := Real.two_le_pi
  have hanti : Antitone (fun j => f (j+1)-f j) := by
    intro i j hij
    dsimp only
    rw [hinc i, hinc j]
    have h := Real.log_unit_increment_antitone hM hij
    simp only [Nat.cast_add, Nat.cast_one, <- add_assoc] at h
    exact mul_le_mul_of_nonneg_left h ht.le
  have hspace : 0 < t/(M+(N : Real)) := by positivity
  have hlower (j : Nat) (hj : j < N) : t/(M+(N : Real)) <= f (j+1)-f j := by
    have hjR : (j : Real)+1 <= N := by exact_mod_cast (Nat.succ_le_of_lt hj)
    rw [hinc]
    calc
      _ <= t/(M+(j : Real)+1) :=
        div_le_div_of_nonneg_left ht.le (by positivity) (by linarith)
      _ = t*(1/(M+(j : Real)+1)) := by ring
      _ <= _ := mul_le_mul_of_nonneg_left
        (Real.log_unit_increment_bounds (show 0 < M+(j : Real) by positivity)).1 ht.le
  have h := norm_sum_exp_le_of_antitone_increment f N hspace hpos hpi hanti hlower
  calc
    _ <= 3*Real.pi/(t/(M+(N : Real))) := h
    _ = _ := by field_simp

/-- Decreasing power weights cost exactly their initial value in the prefix bound. -/
theorem norm_sum_weighted_log_phase_le {M t sigma : Real}
    (hM : 0 < M) (ht : 0 < t) (htM : t <= 2*M) (hsigma : 0 <= sigma) (N : Nat) :
    norm ((Finset.range N).sum (fun j =>
      Complex.ofReal ((M+(j : Real))^(-sigma))*
        exp (I*Complex.ofReal (t*Real.log (M+(j : Real)))))) <=
      (3*Real.pi*(M+(N : Real))/t)*M^(-sigma) := by
  let u : Nat -> Complex := fun j => exp (I*Complex.ofReal (t*Real.log (M+(j : Real))))
  let w : Nat -> Real := fun j => (M+(j : Real))^(-sigma)
  let b : Nat -> Complex := fun j => Complex.ofReal (w j)
  let E : Real := 3*Real.pi*(M+(N : Real))/t
  have hE : 0 <= E := by dsimp [E]; positivity
  have hpartial (j : Nat) (hj : j <= N) :
      norm ((Finset.range j).sum u) <= E := by
    have h := norm_sum_log_phase_le hM ht htM j
    have hjR : (j : Real) <= N := by exact_mod_cast hj
    exact h.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : M+(j : Real) <= M+(N : Real))
        (by positivity : 0 <= 3*Real.pi)) ht.le)
  have hw0 (j : Nat) : 0 <= w j := by dsimp [w]; positivity
  have hw : Antitone w := by
    intro i j hij
    dsimp [w]
    have hijR : (i : Real) <= j := by exact_mod_cast hij
    exact Real.rpow_le_rpow_of_nonpos
      (show 0 < M+(i : Real) by positivity) (by linarith) (by linarith)
  have hb (j : Nat) : norm (b j) = w j := by
    simp only [b, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 j)]
  have hstep (j : Nat) : norm (b (j+1)-b j) = w j-w (j+1) := by
    have he : b (j+1)-b j = Complex.ofReal (w (j+1)-w j) := by
      simp only [b, Complex.ofReal_sub]
    rw [he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hw (show j <= j+1 by omega)))]
    ring
  have hv : (Finset.range (N-1)).sum (fun j => norm (b (j+1)-b j)) = w 0-w (N-1) := by
    simp_rw [hstep]
    induction (N-1) with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  have h := norm_sum_mul_le_partial_variation u b N hE hpartial
  rw [hb, hv] at h
  calc
    _ <= E*(w (N-1)+(w 0-w (N-1))) := h
    _ = _ := by
      simp only [E, w, Nat.cast_zero, add_zero]
      ring

/-- Conjugation gives the same weighted estimate for the negative phase. -/
theorem norm_sum_weighted_neg_log_phase_le {M t sigma : Real}
    (hM : 0 < M) (ht : 0 < t) (htM : t <= 2*M) (hsigma : 0 <= sigma) (N : Nat) :
    norm ((Finset.range N).sum (fun j =>
      Complex.ofReal ((M+(j : Real))^(-sigma))*
        exp (I*Complex.ofReal (-t*Real.log (M+(j : Real)))))) <=
      (3*Real.pi*(M+(N : Real))/t)*M^(-sigma) := by
  have he : (Finset.range N).sum (fun j =>
      Complex.ofReal ((M+(j : Real))^(-sigma))*
        exp (I*Complex.ofReal (-t*Real.log (M+(j : Real))))) =
      (starRingEnd Complex) ((Finset.range N).sum (fun j =>
        Complex.ofReal ((M+(j : Real))^(-sigma))*
          exp (I*Complex.ofReal (t*Real.log (M+(j : Real)))))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul, conj_ofReal, <- exp_conj, map_mul, conj_I, conj_ofReal]
    simp only [neg_mul, Complex.ofReal_neg, mul_neg]
  rw [he, norm_conj]
  exact norm_sum_weighted_log_phase_le hM ht htM hsigma N

/-- A negative complex power on the positive axis has its exact real weight and phase. -/
theorem ofReal_cpow_neg_eq_weighted_log_phase {a : Real} (ha : 0 < a) (s : Complex) :
    Complex.ofReal a^(-s) = Complex.ofReal (a^(-s.re))*
      exp (I*Complex.ofReal (-s.im*Real.log a)) := by
  have haC : Not (Complex.ofReal a = 0) := by exact_mod_cast ha.ne'
  rw [cpow_def_of_ne_zero haC, <- ofReal_log ha.le,
    Real.rpow_def_of_pos ha, ofReal_exp, <- exp_add]
  apply congrArg exp
  apply Complex.ext <;> simp <;> ring

/-- Uniform complex-power segment bound when its first angular increment is at most two. -/
theorem norm_sum_cpow_le_of_large_start {M : Real} {s : Complex}
    (hM : 0 < M) (ht : 0 < abs s.im) (htM : abs s.im <= 2*M)
    (hsigma : 0 <= s.re) (N : Nat) :
    norm ((Finset.range N).sum (fun j => Complex.ofReal (M+(j : Real))^(-s))) <=
      (3*Real.pi*(M+(N : Real))/abs s.im)*M^(-s.re) := by
  have he (j : Nat) : Complex.ofReal (M+(j : Real))^(-s) =
      Complex.ofReal ((M+(j : Real))^(-s.re))*
        exp (I*Complex.ofReal (-s.im*Real.log (M+(j : Real)))) :=
    ofReal_cpow_neg_eq_weighted_log_phase (by positivity) s
  simp_rw [he]
  by_cases hi : 0 <= s.im
  next =>
    rw [abs_of_nonneg hi] at ht htM
    rw [abs_of_nonneg hi]
    exact norm_sum_weighted_neg_log_phase_le hM ht htM hsigma N
  next =>
    have hi0 : s.im < 0 := lt_of_not_ge hi
    rw [abs_of_neg hi0] at ht htM
    rw [abs_of_neg hi0]
    exact norm_sum_weighted_log_phase_le hM ht htM hsigma N

/-- The entire tail above floor(T) through ceil(T^(9/8)) has explicit power decay. -/
theorem norm_sum_cpow_ceiling_tail_le {T : Real} {s : Complex}
    (hT : 1 <= T) (hsigma : (1/2 : Real) <= s.re)
    (ht0 : T <= abs s.im) (ht1 : abs s.im <= 2*T) :
    norm ((Finset.range (Nat.ceil (T^(9/8 : Real))-Nat.floor T)).sum
      (fun j => ((Nat.floor T+j+1 : Nat) : Complex)^(-s))) <=
      9*Real.pi*T^(-(3/8 : Real)) := by
  have hT0 : 0 < T := by linarith
  let q : Real := T^(9/8 : Real)
  let A : Nat := Nat.floor T
  let N : Nat := Nat.ceil q
  let M : Real := (A : Real)+1
  let K : Nat := N-A
  have hq0 : 0 < q := Real.rpow_pos_of_pos hT0 _
  have hq1 : 1 <= q := Real.one_le_rpow hT (by norm_num)
  have hTq : T <= q := by
    calc
      _ = T^(1 : Real) := (Real.rpow_one T).symm
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have hA : (A : Real) <= T := Nat.floor_le hT0.le
  have hNlo : q <= (N : Real) := Nat.le_ceil q
  have hAN : A <= N := by exact_mod_cast (hA.trans (hTq.trans hNlo))
  have hNhi : (N : Real) <= 2*q := by
    have h := Nat.ceil_lt_add_one hq0.le
    change (N : Real) < q+1 at h
    linarith
  have hTM : T < M := Nat.lt_floor_add_one T
  have hM : 0 < M := hT0.trans hTM
  have hMK : M+(K : Real) = (N : Real)+1 := by
    dsimp [M, K]
    rw [Nat.cast_sub hAN]
    ring
  have hMKq : M+(K : Real) <= 3*q := by rw [hMK]; linarith
  have hu : 0 < abs s.im := hT0.trans_le ht0
  have huM : abs s.im <= 2*M := by linarith
  have hweight : M^(-s.re) <= T^(-(1/2 : Real)) := by
    calc
      _ <= T^(-s.re) := Real.rpow_le_rpow_of_nonpos hT0 hTM.le (by linarith)
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hfactor : 3*Real.pi*(M+(K : Real))/abs s.im <= 9*Real.pi*q/T := by
    calc
      _ <= (3*Real.pi*(3*q))/abs s.im :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMKq (by positivity)) (abs_nonneg _)
      _ <= (3*Real.pi*(3*q))/T :=
        div_le_div_of_nonneg_left (by positivity) hT0 ht0
      _ = _ := by ring
  have hpower : (q/T)*T^(-(1/2 : Real)) = T^(-(3/8 : Real)) := by
    calc
      _ = (T^(9/8 : Real)/T^(1 : Real))*T^(-(1/2 : Real)) := by
        rw [Real.rpow_one]
      _ = T^((9/8 : Real)-1)*T^(-(1/2 : Real)) := by
        rw [<- Real.rpow_sub hT0]
      _ = T^(((9/8 : Real)-1)+(-(1/2 : Real))) :=
        (Real.rpow_add hT0 _ _).symm
      _ = _ := by norm_num
  have he : (fun j : Nat => ((A+j+1 : Nat) : Complex)^(-s)) =
      (fun j : Nat => Complex.ofReal (M+(j : Real))^(-s)) := by
    funext j
    congr 1
    dsimp [M]
    push_cast
    ring
  change norm ((Finset.range K).sum (fun j => ((A+j+1 : Nat) : Complex)^(-s))) <= _
  rw [he]
  calc
    _ <= (3*Real.pi*(M+(K : Real))/abs s.im)*M^(-s.re) :=
      norm_sum_cpow_le_of_large_start hM hu huM (by linarith) K
    _ <= (9*Real.pi*q/T)*T^(-(1/2 : Real)) :=
      mul_le_mul hfactor hweight (Real.rpow_nonneg hM.le _) (by positivity)
    _ = 9*Real.pi*((q/T)*T^(-(1/2 : Real))) := by ring
    _ = _ := by rw [hpower]

/-- The exact finite partition transfers a ceiling-cutoff estimate to floor(T). -/
theorem norm_sum_cpow_floor_le_ceiling {T : Real} {s : Complex}
    (hT : 1 <= T) (hsigma : (1/2 : Real) <= s.re)
    (ht0 : T <= abs s.im) (ht1 : abs s.im <= 2*T) :
    norm ((Finset.range (Nat.floor T)).sum (fun n => ((n+1 : Nat) : Complex)^(-s))) <=
      norm ((Finset.range (Nat.ceil (T^(9/8 : Real)))).sum
        (fun n => ((n+1 : Nat) : Complex)^(-s))) + 9*Real.pi*T^(-(3/8 : Real)) := by
  let A : Nat := Nat.floor T
  let N : Nat := Nat.ceil (T^(9/8 : Real))
  let f : Nat -> Complex := fun n => ((n+1 : Nat) : Complex)^(-s)
  have hAN : A <= N := by
    have h1 : (A : Real) <= T := Nat.floor_le (by linarith)
    have h2 : T <= T^(9/8 : Real) := by
      calc
        _ = T^(1 : Real) := (Real.rpow_one T).symm
        _ <= _ := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
    exact_mod_cast h1.trans (h2.trans (Nat.le_ceil _))
  have he := Finset.sum_range_add f A (N-A)
  rw [show A+(N-A) = N by omega] at he
  have hs : (Finset.range A).sum f = (Finset.range N).sum f -
      (Finset.range (N-A)).sum (fun j => f (A+j)) := by
    linear_combination -he
  change norm ((Finset.range A).sum f) <= norm ((Finset.range N).sum f) + _
  rw [hs]
  exact (norm_sub_le _ _).trans (add_le_add (le_refl _)
    (norm_sum_cpow_ceiling_tail_le hT hsigma ht0 ht1))

end Complex
