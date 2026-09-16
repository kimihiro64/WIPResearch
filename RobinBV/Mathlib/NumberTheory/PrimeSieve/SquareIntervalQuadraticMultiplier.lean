/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalQuadraticOwner

/-!
# Uniform finite multiplied-quadratic witnesses

Shifted odd rounding gives an exact factor-eight center-offset bound. A known
lower factor cutoff supplies a finite multiplier range, and both signed
quadratic coordinates recover the smaller factor of every admissible odd
semiprime cofactor. The resulting witness feeds the existing least-owner
rejection predicate. This is a completeness theorem for the finite search,
not an estimate of the total composite allowance or a positivity theorem.
-/

set_option autoImplicit false

namespace Int

/-- A shifted balance condition gives the sharp-scale center allowance without
discarding the exact product or replacing its square root by a sampled value. -/
theorem balanced_product_center_bound {r s x A R : Int}
    (hs : 0 <= s) (hR : 0 <= R) (hcenter : 2*A = x+s)
    (hproduct : x*s <= R*R)
    (hup : 4*s*x <= 4*s*s+r*r+4*r*s)
    (hdown : 4*s*s+r*r <= 4*s*x+4*r*s) :
    8*s*(A-R) <= r*r := by
  let e := 4*s*x-4*s*s-r*r
  have heUp : 0 <= 4*r*s-e := by dsimp only [e]; omega
  have heDown : 0 <= 4*r*s+e := by dsimp only [e]; omega
  have heProd := mul_nonneg heUp heDown
  have heSq : e*e <= 16*r*r*s*s := by nlinarith only [heProd]
  have hscaled := mul_le_mul_of_nonneg_left hproduct (sq_nonneg (8*s))
  have hc := congrArg (fun z => 4*s*z) hcenter
  have hlinear : 8*s*A-r*r = 4*s*x+4*s*s-r*r := by nlinarith only [hc]
  have hid : (8*s*A-r*r)^2 = e*e+64*s*s*s*x-16*r*r*s*s := by
    rw [hlinear]
    dsimp only [e]
    ring
  have hsq : (8*s*A-r*r)^2 <= (8*s*R)^2 := by
    nlinarith only [hid, heSq, hscaled]
  have hnonneg : 0 <= 8*s*R := mul_nonneg (by omega) hR
  by_contra hnot
  have hd : 0 < (8*s*A-r*r)-(8*s*R) := by nlinarith only [hnot]
  have ha : 0 < (8*s*A-r*r)+(8*s*R) := by linarith
  have hp := mul_pos hd ha
  nlinarith only [hp, hsq]

end Int

namespace Nat.PrimeSieve

/-- Shifted odd rounding balances the multiplied factors at the center-error
scale, rather than merely minimizing their arithmetic difference. -/
def balancedOddMultiplier (r s : Nat) : Nat :=
  2*((4*s*s+r*r)/(8*r*s))+1

theorem balancedOddMultiplier_data {r s : Nat} (hr : 3 <= r) (hrs : r <= s) :
    let d := balancedOddMultiplier r s
    1 <= d /\ d%2 = 1 /\ d < s /\
      4*r*s*d <= 4*s*s+r*r+4*r*s /\
      4*s*s+r*r <= 4*r*s*d+4*r*s := by
  let d := balancedOddMultiplier r s
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have hz : 0 < 8*r*s := Nat.mul_pos (Nat.mul_pos (by omega) hr0) hs0
  have hm := Nat.mod_add_div (4*s*s+r*r) (8*r*s)
  have hmlt := Nat.mod_lt (4*s*s+r*r) hz
  have hm0 := Nat.zero_le ((4*s*s+r*r)%(8*r*s))
  have he : 4*r*s*d = 8*r*s*((4*s*s+r*r)/(8*r*s))+4*r*s := by
    dsimp only [d, balancedOddMultiplier]
    ring
  have hu : 4*r*s*d <= 4*s*s+r*r+4*r*s := by nlinarith only [hm, he, hm0]
  have hl : 4*s*s+r*r <= 4*r*s*d+4*r*s := by nlinarith only [hm, he, hmlt]
  have hd0 : 1 <= d := by dsimp only [d, balancedOddMultiplier]; omega
  have hdodd : d%2 = 1 := by dsimp only [d, balancedOddMultiplier]; omega
  have hds : d < s := by
    have hsquare := Nat.mul_self_le_mul_self hrs
    have hcross := Nat.mul_le_mul_right (4*s) hrs
    have hlarge := Nat.mul_le_mul_right (4*s*d) hr
    have hspos : 0 < s*s := Nat.mul_pos hs0 hs0
    by_contra hnot
    have hbad := Nat.mul_le_mul_left (12*s) (show s <= d by omega)
    nlinarith only [hu, hsquare, hcross, hlarge, hspos, hbad]
  exact And.intro hd0 (And.intro hdodd (And.intro hds (And.intro hu hl)))

/-- The actual integer multiplier attains the factor-eight center-offset
bound. All rounding is integral and the ceiling square root is exact. -/
theorem balancedOddMultiplier_center_bound {r s : Nat}
    (hr : 3 <= r) (hrs : r <= s) (hro : r%2 = 1) (hso : s%2 = 1) :
    let d := balancedOddMultiplier r s
    let A := (d*r+s)/2
    let R := cofactorCeilRoot (d*(r*s))
    8*(r*s)*(A-R) <= r*r*r := by
  let d := balancedOddMultiplier r s
  let A := (d*r+s)/2
  let R := cofactorCeilRoot (d*(r*s))
  have hd := balancedOddMultiplier_data hr hrs
  change 1 <= d /\ d%2 = 1 /\ d < s /\
    4*r*s*d <= 4*s*s+r*r+4*r*s /\ 4*s*s+r*r <= 4*r*s*d+4*r*s at hd
  have hxodd : (d*r)%2 = 1 := by rw [Nat.mul_mod, hd.2.1, hro]
  have hA : 2*A = d*r+s := by dsimp only [A]; omega
  have hAI : (2:Int)*A = (d:Int)*r+s := by exact_mod_cast hA
  have hprodI : (d:Int)*r*s <= (A:Int)*A := by
    have hc := congrArg (fun z : Int => z*z) hAI
    nlinarith only [hc, sq_nonneg ((d:Int)*r-s)]
  have hprod : d*(r*s) <= A*A := by exact_mod_cast (show (d:Int)*(r*s) <= (A:Int)*A by nlinarith only [hprodI])
  have hRA : R <= A := cofactorCeilRoot_le_of_le_sq hprod
  have hroot : d*(r*s) <= R*R := le_cofactorCeilRoot_sq (d*(r*s))
  have hg := Int.balanced_product_center_bound
    (r := (r:Int)) (s := (s:Int)) (x := (d:Int)*r) (A := (A:Int)) (R := (R:Int))
    (by omega) (by omega) hAI
    (by exact_mod_cast (show (d*r)*s <= R*R by nlinarith only [hroot]))
    (by have hh : (4:Int)*r*s*d <= 4*s*s+r*r+4*r*s := by exact_mod_cast hd.2.2.2.1
        nlinarith only [hh])
    (by have hh : (4:Int)*s*s+r*r <= 4*r*s*d+4*r*s := by exact_mod_cast hd.2.2.2.2
        nlinarith only [hh])
  have hsub : ((A-R : Nat) : Int) = (A:Int)-R := Nat.cast_sub hRA
  rw [<- hsub] at hg
  have hnat : 8*s*(A-R) <= r*r := by exact_mod_cast hg
  have hm := Nat.mul_le_mul_left r hnat
  change 8*(r*s)*(A-R) <= r*r*r
  nlinarith only [hm]

/-- A known lower factor cutoff and the proposed owner bound give a fully
explicit finite multiplier range. Both divisors in this statement are positive. -/
theorem balancedOddMultiplier_range {r s p L : Nat}
    (hr : 3 <= r) (hrs : r <= s) (hL : 0 < L) (hLr : L <= r) (hrp : r < p) :
    (r*s)/(p*p) <= balancedOddMultiplier r s /\
      balancedOddMultiplier r s <= (r*s)/(L*L)+2 := by
  let d := balancedOddMultiplier r s
  have hd := balancedOddMultiplier_data hr hrs
  change 1 <= d /\ d%2 = 1 /\ d < s /\
    4*r*s*d <= 4*s*s+r*r+4*r*s /\ 4*s*s+r*r <= 4*r*s*d+4*r*s at hd
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have hslow : s < r*(d+1) := by
    by_contra hnot
    have hm := Nat.mul_le_mul_left (4*s) (show r*(d+1) <= s by omega)
    have hpos : 0 < r*r := Nat.mul_pos hr0 hr0
    nlinarith only [hd.2.2.2.2, hm, hpos]
  have hfast : d*r <= s+2*r := by
    by_contra hnot
    have hm := Nat.mul_le_mul_left (4*s) (show s+2*r+1 <= d*r by omega)
    have hsq := Nat.mul_le_mul_left r hrs
    have hpos : 0 < r*s := Nat.mul_pos hr0 hs0
    nlinarith only [hd.2.2.2.1, hm, hsq, hpos]
  constructor
  next =>
    change (r*s)/(p*p) <= d
    by_contra hnot
    have hdiv : d+1 <= (r*s)/(p*p) := by omega
    have hmul := (Nat.le_div_iff_mul_le
      (Nat.mul_pos (show 0 < p by omega) (show 0 < p by omega))).mp hdiv
    have hsq := Nat.mul_le_mul_left (d+1) (Nat.mul_self_le_mul_self hrp.le)
    have hlt := Nat.mul_lt_mul_of_pos_left hslow hr0
    nlinarith only [hmul, hsq, hlt]
  next =>
    change d <= (r*s)/(L*L)+2
    by_cases hsmall : d <= 2
    next => have hn := Nat.zero_le ((r*s)/(L*L)); omega
    next =>
      let f := d-2
      have he : d = f+2 := by dsimp only [f]; omega
      rw [he] at hfast
      have hfr : f*r <= s := by nlinarith only [hfast]
      have hmul := Nat.mul_le_mul_right r hfr
      have hsq := Nat.mul_le_mul_left f (Nat.mul_self_le_mul_self hLr)
      have hbound : f*(L*L) <= r*s := by nlinarith only [hmul, hsq]
      have hdiv := (Nat.le_div_iff_mul_le (Nat.mul_pos hL hL)).mpr hbound
      omega

/-- A depth chosen from p^3<=8vE captures the exact witness for every factor
r<p in the stated odd cofactor family. No finite sample substitutes for r. -/
theorem balancedOddMultiplier_center_depth {r s p E : Nat}
    (hr : 3 <= r) (hrs : r <= s) (hro : r%2 = 1) (hso : s%2 = 1)
    (hrp : r < p) (hE : p*p*p <= 8*(r*s)*E) :
    let d := balancedOddMultiplier r s
    let A := (d*r+s)/2
    A-cofactorCeilRoot (d*(r*s)) < E := by
  let d := balancedOddMultiplier r s
  let A := (d*r+s)/2
  let R := cofactorCeilRoot (d*(r*s))
  have hb := balancedOddMultiplier_center_bound hr hrs hro hso
  change 8*(r*s)*(A-R) <= r*r*r at hb
  have hr0 : 0 < r := by omega
  have hlt := Nat.mul_lt_mul_of_pos_right hrp (Nat.mul_pos hr0 hr0)
  have hle := Nat.mul_le_mul_left p (Nat.mul_self_le_mul_self hrp.le)
  have hcube : r*r*r < p*p*p := by nlinarith only [hlt, hle]
  change A-R < E
  by_contra hnot
  have hm := Nat.mul_le_mul_left (8*(r*s)) (show E <= A-R by omega)
  nlinarith only [hb, hcube, hm, hE]

end Nat.PrimeSieve

namespace Nat.PrimeSieve

/-- Exact natural square coordinates for either ordering of an odd factor pair. -/
theorem odd_factor_pair_quadratic_coordinates {u w : Nat}
    (hu : u%2 = 1) (hw : w%2 = 1) :
    let A := (u+w)/2
    let B := Nat.sqrt (A*A-u*w)
    u*w+B*B = A*A /\ (u = A-B \/ u = A+B) := by
  let A := (u+w)/2
  by_cases hle : u <= w
  next =>
    let b := (w-u)/2
    have hew : w = u+2*b := by dsimp only [b]; omega
    have hA : A = u+b := by dsimp only [A]; omega
    have he : u*w+b*b = A*A := by nlinarith only [hew, hA]
    have hsub : A*A-u*w = b*b := by omega
    have hsqrt : Nat.sqrt (A*A-u*w) = b := by rw [hsub, Nat.sqrt_eq]
    change u*w+Nat.sqrt (A*A-u*w)*Nat.sqrt (A*A-u*w) = A*A /\
      (u = A-Nat.sqrt (A*A-u*w) \/ u = A+Nat.sqrt (A*A-u*w))
    rw [hsqrt]
    exact And.intro he (Or.inl (by omega))
  next =>
    let b := (u-w)/2
    have heu : u = w+2*b := by dsimp only [b]; omega
    have hA : A = w+b := by dsimp only [A]; omega
    have he : u*w+b*b = A*A := by nlinarith only [heu, hA]
    have hsub : A*A-u*w = b*b := by omega
    have hsqrt : Nat.sqrt (A*A-u*w) = b := by rw [hsub, Nat.sqrt_eq]
    change u*w+Nat.sqrt (A*A-u*w)*Nat.sqrt (A*A-u*w) = A*A /\
      (u = A-Nat.sqrt (A*A-u*w) \/ u = A+Nat.sqrt (A*A-u*w))
    rw [hsqrt]
    exact And.intro he (Or.inr (by omega))

/-- A prime larger cofactor makes the multiplied coordinate expose exactly r. -/
theorem balancedOddMultiplier_witness {r s p : Nat}
    (hr : 3 <= r) (hrs : r <= s) (hro : r%2 = 1) (hso : s%2 = 1)
    (hs : Nat.Prime s) (hrp : r < p) :
    let d := balancedOddMultiplier r s
    exists k, k < 2 /\ QuadraticMultipleWitness p (r*s) d ((d*r+s)/2) k := by
  let d := balancedOddMultiplier r s
  let A := (d*r+s)/2
  have hd := balancedOddMultiplier_data hr hrs
  change 1 <= d /\ d%2 = 1 /\ d < s /\
    4*r*s*d <= 4*s*s+r*r+4*r*s /\ 4*s*s+r*r <= 4*r*s*d+4*r*s at hd
  have hcop : Nat.Coprime d s := Nat.coprime_comm.mp
    (hs.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hd.2.2.1))
  have hgcd : Nat.gcd (d*r) (r*s) = r := by
    rw [Nat.mul_comm d r, Nat.gcd_mul_left, hcop.gcd_eq_one, Nat.mul_one]
  have hodd : (d*r)%2 = 1 := by rw [Nat.mul_mod, hd.2.1, hro]
  have hcoords := odd_factor_pair_quadratic_coordinates hodd hso
  have hc : d*(r*s)+Nat.sqrt (A*A-d*(r*s))*Nat.sqrt (A*A-d*(r*s)) = A*A /\
      (d*r = A-Nat.sqrt (A*A-d*(r*s)) \/ d*r = A+Nat.sqrt (A*A-d*(r*s))) := by
    simpa only [Nat.mul_assoc] using hcoords
  have hmake : forall k, k < 2 -> quadraticMultipleCoordinate (r*s) d A k = d*r ->
      exists k, k < 2 /\ QuadraticMultipleWitness p (r*s) d A k := by
    intro k hk he
    refine Exists.intro k (And.intro hk ?_)
    change d*(r*s)+Nat.sqrt (A*A-d*(r*s))*Nat.sqrt (A*A-d*(r*s)) = A*A /\
      1 < Nat.gcd (quadraticMultipleCoordinate (r*s) d A k) (r*s) /\
      Nat.gcd (quadraticMultipleCoordinate (r*s) d A k) (r*s) < p
    rw [he, hgcd]
    exact And.intro hc.1 (And.intro (by omega) hrp)
  rcases hc.2 with hminus | hplus
  next => exact hmake 0 (by decide) (by
    change A-Nat.sqrt (A*A-d*(r*s)) = d*r
    exact hminus.symm)
  next => exact hmake 1 (by decide) (by
    change A+Nat.sqrt (A*A-d*(r*s)) = d*r
    exact hplus.symm)

/-- Every admissible odd semiprime cofactor with a smaller factor has a witness
inside the explicit multiplier interval and exact ceiling-root depth. -/
theorem balancedOddMultiplier_finite_witness {r s p L E : Nat}
    (hr : 3 <= r) (hrs : r <= s) (hro : r%2 = 1) (hso : s%2 = 1)
    (hs : Nat.Prime s) (hL : 0 < L) (hLr : L <= r) (hrp : r < p)
    (hE : p*p*p <= 8*(r*s)*E) :
    exists d j k, Membership.mem (Finset.Icc ((r*s)/(p*p)) ((r*s)/(L*L)+2)) d /\
      j < E /\ k < 2 /\
      QuadraticMultipleWitness p (r*s) d (cofactorCeilRoot (d*(r*s))+j) k := by
  let d := balancedOddMultiplier r s
  let A := (d*r+s)/2
  let R := cofactorCeilRoot (d*(r*s))
  choose k hk using balancedOddMultiplier_witness hr hrs hro hso hs hrp
  change k < 2 /\ QuadraticMultipleWitness p (r*s) d A k at hk
  have hprod : d*(r*s) <= A*A := by have he := hk.2.1; omega
  have hRA : R <= A := cofactorCeilRoot_le_of_le_sq hprod
  have hcenter : R+(A-R) = A := by omega
  have hrange := balancedOddMultiplier_range hr hrs hL hLr hrp
  have hdepth := balancedOddMultiplier_center_depth hr hrs hro hso hrp hE
  refine Exists.intro d (Exists.intro (A-R) (Exists.intro k
    (And.intro (Finset.mem_Icc.mpr hrange) (And.intro hdepth (And.intro hk.1 ?_)))))
  change QuadraticMultipleWitness p (r*s) d (R+(A-R)) k
  rw [hcenter]
  exact hk.2

/-- The finite quadratic search rejects every false owner in this cofactor
family, in the existing line-compatible composite allowance. -/
theorem not_multipliedQuadratic_compatible_of_semiprime {r s p L E Q D : Nat}
    (hr : 3 <= r) (hrs : r <= s) (hro : r%2 = 1) (hso : s%2 = 1)
    (hs : Nat.Prime s) (hL : 0 < L) (hLr : L <= r) (hrp : r < p)
    (hE : p*p*p <= 8*(r*s)*E) :
    Not (OwnerLineFamilyCompatible
      (multipliedQuadraticLineDirections
        (Finset.Icc ((r*s)/(p*p)) ((r*s)/(L*L)+2)) Q D E) p (r*s)) := by
  choose d j k h using balancedOddMultiplier_finite_witness hr hrs hro hso hs hL hLr hrp hE
  exact not_multipliedQuadraticLineDirections_compatible h.1 h.2.1 h.2.2.1 h.2.2.2

end Nat.PrimeSieve
