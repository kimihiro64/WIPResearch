/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalFifthIncidence

/-!
# Uniform optimization of the corrected fifth-incidence shift

A two-parameter polynomial factorization proves the optimal discrete shift
against all competing shifts. The chooser uses exact integer moments and
ceiling arithmetic; optimality does not imply positivity of the optimum.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- The shift-dependent part of the normalized fifth moment before division by b times b plus one. -/
def fifthShiftKernel (A B : Int) (b : Nat) : Int :=
  (8*(b : Int)-12)*A-20*B

/-- The exact factored cross difference for any two root shifts. -/
theorem fifthShiftKernel_cross (A B : Int) (b t : Nat) :
    (b : Int)*((b : Int)+1)*fifthShiftKernel A B t-
      (t : Int)*((t : Int)+1)*fifthShiftKernel A B b =
      4*((t : Int)-(b : Int))*
        (5*B*((t : Int)+(b : Int)+1)+
          (3*(t : Int)+3*(b : Int)+3-2*(b : Int)*(t : Int))*A) := by
  unfold fifthShiftKernel
  ring

/-- A discrete coefficient bracket certifies global optimality against every natural shift. -/
theorem fifthShiftKernel_optimal {A B : Int} {t : Nat} (hA : 0 <= A)
    (hlo : ((t : Int)-4)*A <= 5*B) (hhi : 5*B <= ((t : Int)-3)*A) (b : Nat) :
    (t : Int)*((t : Int)+1)*fifthShiftKernel A B b <=
      (b : Int)*((b : Int)+1)*fifthShiftKernel A B t := by
  let K := 5*B*((t : Int)+(b : Int)+1)+
    (3*(t : Int)+3*(b : Int)+3-2*(b : Int)*(t : Int))*A
  have he := fifthShiftKernel_cross A B b t
  change _ = 4*((t : Int)-(b : Int))*K at he
  by_cases hbt : b = t
  next => subst b; exact le_rfl
  next =>
    by_cases hlt : b < t
    next =>
      have hpart1 := mul_nonneg (show (0 : Int) <= (t : Int)+(b : Int)+1 by omega)
        (show 0 <= 5*B-((t : Int)-4)*A by omega)
      have hpart2 := mul_nonneg (mul_nonneg hA (show (0 : Int) <= (t : Int)+1 by omega))
        (show 0 <= (t : Int)-(b : Int)-1 by omega)
      have hK : 0 <= K := by dsimp [K]; nlinarith only [hpart1, hpart2]
      have hp := mul_nonneg (show (0 : Int) <= (t : Int)-(b : Int) by omega) hK
      nlinarith only [he, hp]
    next =>
      have hgt : t < b := by omega
      have hpart1 := mul_nonpos_of_nonneg_of_nonpos
        (show (0 : Int) <= (t : Int)+(b : Int)+1 by omega)
        (show 5*B-((t : Int)-3)*A <= 0 by omega)
      have hpart2 := mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hA (show (0 : Int) <= (t : Int) by omega))
        (show (t : Int)+1-(b : Int) <= 0 by omega)
      have hK : K <= 0 := by dsimp [K]; nlinarith only [hpart1, hpart2]
      have hp := mul_nonneg_of_nonpos_of_nonpos (show (t : Int)-(b : Int) <= 0 by omega) hK
      nlinarith only [he, hp]

/-- Exact natural ceiling arithmetic supplies both sides of the optimizer bracket. -/
theorem fifthShift_ceil_bracket {A B : Nat} (hA : 0 < A) :
    let q := (5*B+A-1)/A;
    q*A <= 5*B+A /\ 5*B <= q*A := by
  have hle := Nat.div_mul_le_self (5*B+A-1) A
  have hmod := Nat.mod_lt (5*B+A-1) hA
  have hdiv := Nat.mod_add_div (5*B+A-1) A
  have he := Nat.sub_add_cancel (show 1 <= 5*B+A by omega)
  dsimp only
  constructor <;> nlinarith only [hle, hmod, hdiv, he]

/-- The explicit ceiling-based shift is a global optimizer for every positive natural fourth moment. -/
theorem fifthShiftKernel_nat_optimal {A B : Nat} (hA : 0 < A) (b : Nat) :
    let t := 3+(5*B+A-1)/A;
    (t : Int)*((t : Int)+1)*fifthShiftKernel (A : Int) (B : Int) b <=
      (b : Int)*((b : Int)+1)*fifthShiftKernel (A : Int) (B : Int) t := by
  let q := (5*B+A-1)/A
  have hbracket := fifthShift_ceil_bracket (B := B) hA
  have hleft : (q : Int)*(A : Int) <= 5*(B : Int)+(A : Int) := by
    exact_mod_cast hbracket.1
  have hright : 5*(B : Int) <= (q : Int)*(A : Int) := by
    exact_mod_cast hbracket.2
  apply fifthShiftKernel_optimal (by omega)
  next =>
    change (((3+q : Nat) : Int)-4)*(A : Int) <= 5*(B : Int)
    push_cast
    nlinarith only [hleft]
  next =>
    change 5*(B : Int) <= (((3+q : Nat) : Int)-3)*(A : Int)
    push_cast
    nlinarith only [hright]

/-- Natural-valued exact binomial moments on the complete two-stage survivor set. -/
noncomputable def squareCorrectedMomentNat (n z k : Nat) : Nat :=
  (squareMomentSurvivors n z).sum (fun m => (squareMomentMultiplicity z m).choose k)

/-- The natural and integer corrected moments agree exactly. -/
theorem cast_squareCorrectedMomentNat (n z k : Nat) :
    (squareCorrectedMomentNat n z k : Int) = squareCorrectedMoment n z k := by
  simp [squareCorrectedMomentNat, squareCorrectedMoment]

/-- Vanishing of a binomial moment forces every higher moment to vanish on the actual support. -/
theorem squareCorrectedMomentNat_zero_of_le {n z k l : Nat} (hkl : k <= l)
    (hzero : squareCorrectedMomentNat n z k = 0) :
    squareCorrectedMomentNat n z l = 0 := by
  unfold squareCorrectedMomentNat at hzero
  unfold squareCorrectedMomentNat
  apply Finset.sum_eq_zero
  intro m hm
  have hle : (squareMomentMultiplicity z m).choose k <=
      (squareMomentSurvivors n z).sum (fun x => (squareMomentMultiplicity z x).choose k) :=
    Finset.single_le_sum (fun x _ => Nat.zero_le ((squareMomentMultiplicity z x).choose k)) hm
  rw [hzero] at hle
  have hr := Nat.choose_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hle)
  exact Nat.choose_eq_zero_of_lt (lt_of_lt_of_le hr hkl)

/-- The explicit fifth-degree root optimizer, with a separate zero-fourth-moment branch. -/
noncomputable def squareFifthOptimalShift (n z : Nat) : Nat :=
  let A := squareCorrectedMomentNat n z 4;
  let B := squareCorrectedMomentNat n z 5;
  if A = 0 then 2 else 3+(5*B+A-1)/A

/-- The explicit optimizer always belongs to the admissible shift family. -/
theorem squareFifthOptimalShift_two_le (n z : Nat) : 2 <= squareFifthOptimalShift n z := by
  unfold squareFifthOptimalShift
  dsimp only
  split_ifs
  next => exact le_rfl
  next => exact le_trans (by decide : 2 <= 3) (Nat.le_add_right 3 _)

/-- The exact cross comparison certifies normalized optimality over every admissible shift b at least two. -/
theorem squareFifthOptimalShift_cross_optimal (n z b : Nat) :
    let t := squareFifthOptimalShift n z;
    (t : Int)*((t : Int)+1)*squareFifthMomentNumerator n z b <=
      (b : Int)*((b : Int)+1)*squareFifthMomentNumerator n z t := by
  let A := squareCorrectedMomentNat n z 4
  let B := squareCorrectedMomentNat n z 5
  let H := squareCorrectedMoment n z 0-squareCorrectedMoment n z 1+
    squareCorrectedMoment n z 2-squareCorrectedMoment n z 3
  have hAcast : (A : Int) = squareCorrectedMoment n z 4 := cast_squareCorrectedMomentNat n z 4
  have hBcast : (B : Int) = squareCorrectedMoment n z 5 := cast_squareCorrectedMomentNat n z 5
  have hrep (c : Nat) : squareFifthMomentNumerator n z c =
      6*(c : Int)*((c : Int)+1)*H + 6*fifthShiftKernel (A : Int) (B : Int) c := by
    rw [hAcast, hBcast]
    unfold squareFifthMomentNumerator fifthShiftKernel
    dsimp only [H]
    ring
  by_cases hA : A = 0
  next =>
    have hB : B = 0 := squareCorrectedMomentNat_zero_of_le (by omega) hA
    have ht : squareFifthOptimalShift n z = 2 := by
      change (if A = 0 then 2 else 3+(5*B+A-1)/A) = 2
      rw [if_pos hA]
    dsimp only
    rw [ht, hrep b, hrep 2, hA, hB]
    simp only [Nat.cast_zero, fifthShiftKernel, mul_zero, sub_zero, add_zero]
    apply le_of_eq
    ring
  next =>
    have hapos : 0 < A := by omega
    have ht : squareFifthOptimalShift n z = 3+(5*B+A-1)/A := by
      change (if A = 0 then 2 else 3+(5*B+A-1)/A) = _
      rw [if_neg hA]
    have hopt := fifthShiftKernel_nat_optimal (B := B) hapos b
    dsimp only
    rw [ht, hrep b, hrep (3+(5*B+A-1)/A)]
    dsimp only at hopt
    nlinarith only [hopt]

/-- The chosen fifth shift is positive exactly when some admissible shift is positive. -/
theorem square_fifth_optimal_pos_iff (n z : Nat) :
    0 < squareFifthMomentNumerator n z (squareFifthOptimalShift n z) <->
      exists b : Nat, 2 <= b /\ 0 < squareFifthMomentNumerator n z b := by
  constructor
  next =>
    intro h
    exact Exists.intro (squareFifthOptimalShift n z)
      (And.intro (squareFifthOptimalShift_two_le n z) h)
  next =>
    intro h
    choose b hb using h
    have ht := squareFifthOptimalShift_two_le n z
    have hc := squareFifthOptimalShift_cross_optimal n z b
    dsimp only at hc
    have hp : 0 < (squareFifthOptimalShift n z : Int)*
        ((squareFifthOptimalShift n z : Int)+1)*squareFifthMomentNumerator n z b :=
      mul_pos (mul_pos (by omega) (by omega)) hb.2
    have hprod := lt_of_lt_of_le hp hc
    by_contra hnpos
    have hnle : squareFifthMomentNumerator n z (squareFifthOptimalShift n z) <= 0 := by omega
    have hden : 0 <= (b : Int)*((b : Int)+1) := mul_nonneg (by omega) (by omega)
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hden hnle
    omega

/-- Positivity of the fully optimized corrected moment supplies an actual square-interval prime. -/
theorem square_fifth_optimal_pos_implies_prime {n z : Nat} (hn : 2 <= n) (hz : z <= n)
    (hpos : 0 < squareFifthMomentNumerator n z (squareFifthOptimalShift n z)) :
    exists p : Nat, n*n < p /\ p < (n+1)*(n+1) /\ Nat.Prime p :=
  square_fifth_moment_pos_implies_prime hn hz hpos

/-- The canonical cube-root cutoff never exceeds the square-interval index. -/
theorem square_cube_root_le_index (n : Nat) : Nat.nthRoot 3 (n*n+2*n) <= n := by
  have h : Nat.nthRoot 3 (n*n+2*n) < n+1 :=
    (Nat.nthRoot_lt_iff (by decide : Not (3 = 0))).mpr
      (by nlinarith only [Nat.zero_le (n*n*n), Nat.zero_le (n*n)])
  omega

/-- The original cube-cutoff fifth-moment proposal has an explicit optimized sufficient condition for a prime. -/
theorem square_cube_fifth_optimal_pos_implies_prime {n : Nat} (hn : 2 <= n)
    (hpos : 0 < squareFifthMomentNumerator n (Nat.nthRoot 3 (n*n+2*n))
      (squareFifthOptimalShift n (Nat.nthRoot 3 (n*n+2*n)))) :
    exists p : Nat, n*n < p /\ p < (n+1)*(n+1) /\ Nat.Prime p :=
  square_fifth_optimal_pos_implies_prime hn (square_cube_root_le_index n) hpos

end Nat.PrimeSieve
