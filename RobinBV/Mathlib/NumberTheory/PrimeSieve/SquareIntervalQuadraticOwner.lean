/-
Copyright (c) 2026 Jonas Whidden.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import RobinBV.Mathlib.NumberTheory.PrimeSieve.SquareIntervalPrimitiveLine

/-!
# Exact quadratic restrictions on square-interval least-owner counts

Odd factor pairs are represented by exact integer square centers. Finite
center families and multiplied centers reject false proposed least owners
without excluding genuine ones. The complete prime-candidate clock bound
retains its original supply, lower-owner costs and all remaining high cells.
The cube and fourth-power cutoffs retain repeated factors. No uniform
positivity, prime-distribution estimate or conjecture is asserted here.
-/

set_option autoImplicit false
open scoped Classical
namespace Nat.PrimeSieve

/-- The first integer square center at or above the cofactor. -/
def cofactorCeilRoot (v : Nat) : Nat :=
  Nat.sqrt v + if Nat.sqrt v*Nat.sqrt v = v then 0 else 1

/-- Exact square, positive-factor and proposed-owner restrictions. -/
def QuadraticOwnerWitness (p v A : Nat) : Prop :=
  let B := Nat.sqrt (A*A-v)
  v+B*B = A*A /\ 1 < A-B /\ A-B < p

/-- A finite band of exact quadratic cofactor tests; no cofactor primality oracle. -/
noncomputable def quadraticOwnerDirections (D p v : Nat) : Finset (Prod Nat Nat) :=
  ((Finset.range D).filter (fun j =>
    QuadraticOwnerWitness p v (cofactorCeilRoot v+j))).image (fun j =>
      let A := cofactorCeilRoot v+j
      Prod.mk (A-Nat.sqrt (A*A-v)) 1)

/-- Combine the original line family and the quadratic cofactor band. -/
noncomputable def quadraticLineOwnerDirections (Q D p v : Nat) :
    Finset (Prod Nat Nat) :=
  Union.union (twoSidedOwnerDirections Q p v) (quadraticOwnerDirections D p v)

/-- The square discriminant yields an actual smaller positive divisor. -/
theorem QuadraticOwnerWitness.factorization {p v A : Nat}
    (h : QuadraticOwnerWitness p v A) :
    v = (A-Nat.sqrt (A*A-v))*(A+Nat.sqrt (A*A-v)) := by
  let B := Nat.sqrt (A*A-v)
  change v+B*B = A*A /\ 1 < A-B /\ A-B < p at h
  have hBA : B <= A := by omega
  have he : (v : Int)+(B : Int)*B = (A : Int)*A := by exact_mod_cast h.1
  have hsub : ((A-B : Nat) : Int) = (A : Int)-B := Nat.cast_sub hBA
  have hprod : (v : Int) = ((A-B : Nat) : Int)*(A+B : Nat) := by
    rw [hsub]
    push_cast
    nlinarith [he]
  exact_mod_cast hprod

/-- Every retained quadratic witness rejects the proposed owner in the combined family. -/
theorem not_quadraticLineOwnerDirections_compatible {Q D p v j : Nat}
    (hj : j < D) (hw : QuadraticOwnerWitness p v (cofactorCeilRoot v+j)) :
    Not (OwnerLineFamilyCompatible (quadraticLineOwnerDirections Q D) p v) := by
  classical
  let A := cofactorCeilRoot v+j
  let B := Nat.sqrt (A*A-v)
  let a := A-B
  have hwa : v+B*B = A*A /\ 1 < a /\ a < p := hw
  have hfactor : v = a*(A+B) := hw.factorization
  have hd : Dvd.dvd a v := by rw [hfactor]; exact dvd_mul_right a (A+B)
  have hg : Nat.gcd a v = a := Nat.dvd_antisymm
    (Nat.gcd_dvd_left a v) (Nat.dvd_gcd (dvd_refl a) hd)
  have hcop : Nat.Coprime a 1 := Nat.coprime_one_right a
  have hmem : Membership.mem (quadraticLineOwnerDirections Q D p v) (Prod.mk a 1) := by
    apply Finset.mem_union.mpr
    apply Or.inr
    apply Finset.mem_image.mpr
    exact Exists.intro j (And.intro (Finset.mem_filter.mpr
      (And.intro (Finset.mem_range.mpr hj) hw)) rfl)
  intro hc
  have hcontent := primitive_line_content_gcd a 1 p v hcop
  have hg1 : 1 < Nat.gcd a (a*p+1*v) := by rw [hcontent,hg]; exact hwa.2.1
  have hbig := hc (Prod.mk a 1) hmem hcop hg1
  change p <= Nat.gcd a (a*p+1*v) at hbig
  rw [hcontent,hg] at hbig
  omega

/-- The combined predicate is exactly the old predicate with every witnessed
quadratic rejection removed; this identifies the evaluated allowance. -/
theorem quadraticLineOwnerDirections_compatible_iff (Q D p v : Nat) :
    OwnerLineFamilyCompatible (quadraticLineOwnerDirections Q D) p v <->
      OwnerLineFamilyCompatible (twoSidedOwnerDirections Q) p v /\
        forall j, j < D -> Not (QuadraticOwnerWitness p v (cofactorCeilRoot v+j)) := by
  classical
  constructor
  next =>
    intro h
    refine And.intro ?_ ?_
    next =>
      intro z hz hc hg
      exact h z (Finset.mem_union.mpr (Or.inl hz)) hc hg
    next =>
      intro j hj hw
      exact not_quadraticLineOwnerDirections_compatible hj hw h
  next =>
    intro h z hz hc hg
    have hz' := Finset.mem_union.mp hz
    rcases hz' with hbase | hquad
    next => exact h.1 z hbase hc hg
    next =>
      have hx := Finset.mem_image.mp hquad
      choose j hj using hx
      have hj' := Finset.mem_filter.mp hj.1
      exact False.elim (h.2 j (Finset.mem_range.mp hj'.1) hj'.2)

/-- The same total bound with both exact geometric families; no added source premise. -/
theorem prime_count_quadratic_line_clock_bound {n T W : Nat} (Q D : Nat) (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell /\ ell%2 = 1)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    oddOwnerProductDrift S*(n : Int)+prefixClockMinimum S <=
      (oddOwnerPeriod 1 S : Int)*
        (((squareIntervalPrimes n).card : Int)+
          ((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
          ((ownerLineFamilyHighFactorCells (quadraticLineOwnerDirections Q D) n T S R).card : Int)) :=
  prime_count_line_family_clock_bound (quadraticLineOwnerDirections Q D) S R hR hn hW0 hS hW


/-- Above the exact cube cutoff, a genuine least owner's cofactor is prime. -/
theorem prime_cofactor_of_owner_cube {p v : Nat} (hp : Nat.Prime p) (hv : 2 <= v)
    (howner : (p*v).minFac = p) (hcube : p*v < p*p*p) : Nat.Prime v := by
  by_contra hnp
  choose b hb using exists_minFac_mul hv hnp
  have hqprime : Nat.Prime v.minFac := Nat.minFac_prime (by omega)
  have hvd : Dvd.dvd v (p*v) := dvd_mul_left v p
  have hqd : Dvd.dvd v.minFac (p*v) := dvd_trans (Nat.minFac_dvd v) hvd
  have hpr := Nat.minFac_le_of_dvd hqprime.two_le hqd
  rw [howner] at hpr
  have hbd : Dvd.dvd b (p*v) := dvd_trans
    (show Dvd.dvd b v by rw [hb.2]; exact dvd_mul_left b v.minFac) hvd
  have hpb := Nat.minFac_le_of_dvd hb.1 hbd
  rw [howner] at hpb
  have hvlarge : p*p <= v := by
    have hm := Nat.mul_le_mul hpr hpb
    rw [<- hb.2] at hm
    exact hm
  have hm := Nat.mul_le_mul_left p hvlarge
  nlinarith

/-- Above the exact fourth-power cutoff, genuine least-owner composites
have two or three prime factors, with every repetition retained. -/
theorem owner_two_or_three_of_fourth_cutoff {n p v : Nat}
    (hp : Nat.Prime p) (hv : 2 <= v) (howner : (p*v).minFac = p)
    (hhi : p*v < (n+1)*(n+1)) (hfour : n*n+2*n < (p*p)*(p*p)) :
    IsTwoPrime (p*v) \/ IsThreePrime (p*v) := by
  have hcut : n < p*p := by
    by_contra hn
    have hs : p*p <= n := by omega
    have hs2 := Nat.mul_le_mul hs hs
    omega
  have hrough : forall t, Nat.Prime t -> Dvd.dvd t (p*v) -> n < t*t := by
    intro t ht htd
    have hpt := Nat.minFac_le_of_dvd ht.two_le htd
    rw [howner] at hpt
    have hs := Nat.mul_le_mul hpt hpt
    omega
  have hm : 2 <= p*v := by have := hp.two_le; nlinarith
  have hnp : Not (Nat.Prime (p*v)) := not_prime_of_two_factors hp.two_le hv
  exact (rough_prime_or_two_or_three hm hhi hrough).resolve_left hnp

/-- The ceiling square root is below every integer square center. -/
theorem cofactorCeilRoot_le_of_le_sq {v A : Nat} (h : v <= A*A) :
    cofactorCeilRoot v <= A := by
  have hs : Nat.sqrt v <= A := by
    have ht := Nat.sqrt_le_sqrt h
    simpa only [Nat.sqrt_eq] using ht
  unfold cofactorCeilRoot
  split_ifs with he
  next => omega
  next =>
    have hne : Not (Nat.sqrt v = A) := by
      intro ha
      have hl := Nat.sqrt_le v
      have hv : Nat.sqrt v*Nat.sqrt v = v := by rw [ha] at hl; nlinarith
      exact he hv
    omega

/-- The ceiling square root really bounds the cofactor by its square. -/
theorem le_cofactorCeilRoot_sq (v : Nat) :
    v <= cofactorCeilRoot v*cofactorCeilRoot v := by
  unfold cofactorCeilRoot
  split_ifs with he
  next => simpa only [Nat.add_zero] using he.ge
  next => exact (Nat.lt_succ_sqrt v).le

/-- Every odd positive factor pair gives the exact admissible quadratic witness. -/
theorem quadraticOwnerWitness_of_odd_factor_pair {p v r s : Nat}
    (hr : 1 < r) (hrp : r < p) (hrs : r <= s)
    (hro : r%2 = 1) (hso : s%2 = 1) (hv : v = r*s) :
    QuadraticOwnerWitness p v ((r+s)/2) := by
  let A := (r+s)/2
  let B := (s-r)/2
  have hs : s = r+2*B := by dsimp [B]; omega
  have hA : A = r+B := by dsimp [A]; omega
  have he : v+B*B = A*A := by nlinarith [hv]
  have hsub : A*A-v = B*B := by omega
  have hroot : Nat.sqrt (A*A-v) = B := by rw [hsub, Nat.sqrt_eq]
  change v+Nat.sqrt (A*A-v)*Nat.sqrt (A*A-v) = A*A /\
    1 < A-Nat.sqrt (A*A-v) /\ A-Nat.sqrt (A*A-v) < p
  rw [hroot]
  exact And.intro he (And.intro (by omega) (by omega))

/-- An empty tested center band pushes every forbidden factor pair beyond it. -/
theorem quadratic_center_lower_of_compatible {Q D p v r s : Nat}
    (hc : OwnerLineFamilyCompatible (quadraticLineOwnerDirections Q D) p v)
    (hr : 1 < r) (hrp : r < p) (hrs : r <= s)
    (hro : r%2 = 1) (hso : s%2 = 1) (hv : v = r*s) :
    cofactorCeilRoot v+D <= (r+s)/2 := by
  have hw := quadraticOwnerWitness_of_odd_factor_pair hr hrp hrs hro hso hv
  have hsquare : v <= ((r+s)/2)*((r+s)/2) := by
    have he := hw.1
    omega
  have hbase := cofactorCeilRoot_le_of_le_sq hsquare
  by_contra hn
  have hj : (r+s)/2-cofactorCeilRoot v < D := by omega
  have hcenter : cofactorCeilRoot v+((r+s)/2-cofactorCeilRoot v) = (r+s)/2 := by
    omega
  apply not_quadraticLineOwnerDirections_compatible hj _ hc
  simpa only [hcenter] using hw

/-- The smaller hyperbola coordinate decreases past a specified center. -/
theorem small_factor_le_center_cutoff {v r s A : Nat}
    (hrA : r <= A) (hvA : v <= A*A) (hv : v = r*s)
    (hcenter : 2*A <= r+s) :
    r <= A-Nat.sqrt (A*A-v) := by
  let k := Nat.sqrt (A*A-v)
  let x := A-r
  have hxs : x+r = A := Nat.sub_add_cancel hrA
  have hkA : k <= A := by
    have h := Nat.sqrt_le_sqrt (Nat.sub_le (A*A) v)
    simpa only [Nat.sqrt_eq] using h
  have hks : k*k <= A*A-v := Nat.sqrt_le (A*A-v)
  have hvs : A*A-v+v = A*A := Nat.sub_add_cancel hvA
  by_contra hn
  have hxk : x < k := by change Not (r <= A-k) at hn; omega
  have hk : 0 < k := by omega
  have hxx : x*x < k*k := lt_of_le_of_lt
    (Nat.mul_le_mul_left x hxk.le) (Nat.mul_lt_mul_of_pos_right hxk hk)
  have hc := Nat.mul_le_mul_left r hcenter
  have he := congrArg (fun t : Nat => t*t) hxs
  nlinarith [hc, he, hv]

/-- Every smaller forbidden cofactor factor lies in this exact residual range. -/
theorem quadratic_residual_factor_cutoff {Q D p v r s : Nat}
    (hc : OwnerLineFamilyCompatible (quadraticLineOwnerDirections Q D) p v)
    (hr : 1 < r) (hrp : r < p) (hrs : r <= s)
    (hro : r%2 = 1) (hso : s%2 = 1) (hv : v = r*s) :
    r <= cofactorCeilRoot v+D-
      Nat.sqrt ((cofactorCeilRoot v+D)*(cofactorCeilRoot v+D)-v) := by
  have hcenter := quadratic_center_lower_of_compatible hc hr hrp hrs hro hso hv
  have hrr : r*r <= v := by nlinarith [Nat.mul_le_mul_left r hrs]
  have hrroot : r <= Nat.sqrt v := Nat.le_sqrt.mpr hrr
  have hrA : r <= cofactorCeilRoot v+D := by unfold cofactorCeilRoot; omega
  have hvA : v <= (cofactorCeilRoot v+D)*(cofactorCeilRoot v+D) := by
    have hs := le_cofactorCeilRoot_sq v
    nlinarith
  exact small_factor_le_center_cutoff hrA hvA hv (by omega)

/-- A simpler polynomial form of the same residual size restriction. -/
theorem quadratic_residual_factor_polynomial {Q D p v r s : Nat}
    (hc : OwnerLineFamilyCompatible (quadraticLineOwnerDirections Q D) p v)
    (hr : 1 < r) (hrp : r < p) (hrs : r <= s)
    (hro : r%2 = 1) (hso : s%2 = 1) (hv : v = r*s) :
    r*r+2*D*r <= v := by
  have hcenter := quadratic_center_lower_of_compatible hc hr hrp hrs hro hso hv
  have hrr : r*r <= v := by nlinarith [Nat.mul_le_mul_left r hrs]
  have hrroot : r <= Nat.sqrt v := Nat.le_sqrt.mpr hrr
  have hrA : r <= cofactorCeilRoot v := by unfold cofactorCeilRoot; omega
  have hs : r+2*D <= s := by omega
  have hm := Nat.mul_le_mul_left r hs
  nlinarith [hm, hv]

/-- Once the residual quadratic range meets the line-detection range, a retained
cofactor below the owner square must be prime. The repeated-owner case is explicit. -/
theorem prime_cofactor_of_quadratic_line_coverage {Q D p v : Nat}
    (hp : Nat.Prime p) (hpv : p < v) (hvo : v%2 = 1)
    (hsmall : v < p*p) (hnot : Not (Dvd.dvd p v))
    (hc : OwnerLineFamilyCompatible (quadraticLineOwnerDirections Q D) p v)
    (hcover : cofactorCeilRoot v+D-
      Nat.sqrt ((cofactorCeilRoot v+D)*(cofactorCeilRoot v+D)-v) <= Q+1) :
    Nat.Prime v := by
  by_contra hnp
  have hv2 : 2 <= v := by have := hp.two_le; omega
  choose s hs using exists_minFac_mul hv2 hnp
  let r := v.minFac
  have hr : Nat.Prime r := Nat.minFac_prime (by omega)
  have hvr : v = r*s := hs.2
  have hrs : r <= s := Nat.minFac_le_of_dvd hs.1
    (show Dvd.dvd s v by rw [hvr]; exact dvd_mul_left s r)
  have hrr : r*r <= v := by nlinarith [Nat.mul_le_mul_left r hrs]
  have hrp : r < p := by
    by_contra hn
    have hpr : p <= r := by omega
    have hm := Nat.mul_le_mul hpr hpr
    omega
  have hmod : 1 = (r%2*(s%2))%2 := by
    rw [<- hvo, hvr, Nat.mul_mod]
  have hro : r%2 = 1 := by
    by_contra hn
    have hz : r%2 = 0 := by omega
    rw [hz, Nat.zero_mul, Nat.zero_mod] at hmod
    omega
  have hso : s%2 = 1 := by
    by_contra hn
    have hz : s%2 = 0 := by omega
    rw [hz, Nat.mul_zero, Nat.zero_mod] at hmod
    omega
  have hcut := quadratic_residual_factor_cutoff hc hr.one_lt hrp hrs hro hso hvr
  have hbase := (quadraticLineOwnerDirections_compatible_iff Q D p v).mp hc
  exact not_ownerLineFamilyCompatible_of_small_factor hp hr hrp hpv
    (Nat.minFac_dvd v) hnot (hcut.trans hcover) hbase.1

/-- Both factor directions are needed because multiplication can reverse their order. -/
def quadraticMultipleCoordinate (v d A k : Nat) : Nat :=
  if k = 0 then A-Nat.sqrt (A*A-d*v) else A+Nat.sqrt (A*A-d*v)

/-- A multiplied quadratic center is useful precisely when the chosen signed
factor exposes a divisor below the proposed least owner. -/
def QuadraticMultipleWitness (p v d A k : Nat) : Prop :=
  let B := Nat.sqrt (A*A-d*v)
  let a := quadraticMultipleCoordinate v d A k
  d*v+B*B = A*A /\ 1 < Nat.gcd a v /\ Nat.gcd a v < p

/-- Exact multiplied quadratic directions, with set union removing all overlap. -/
noncomputable def quadraticMultipleDirections (U : Finset Nat) (E p v : Nat) :
    Finset (Prod Nat Nat) :=
  U.biUnion (fun d =>
    (Finset.range E).biUnion (fun j =>
      ((Finset.range 2).filter (fun k =>
        QuadraticMultipleWitness p v d (cofactorCeilRoot (d*v)+j) k)).image (fun k =>
          Prod.mk (quadraticMultipleCoordinate v d (cofactorCeilRoot (d*v)+j) k) 1)))

/-- Keep both original families and add multiplied quadratic centers. -/
noncomputable def multipliedQuadraticLineDirections
    (U : Finset Nat) (Q D E p v : Nat) : Finset (Prod Nat Nat) :=
  Union.union (quadraticLineOwnerDirections Q D p v) (quadraticMultipleDirections U E p v)

/-- Every exact multiplied square witness rejects the false proposed owner. -/
theorem not_multipliedQuadraticLineDirections_compatible
    {U : Finset Nat} {Q D E p v d j k : Nat}
    (hd : Membership.mem U d) (hj : j < E) (hk : k < 2)
    (hw : QuadraticMultipleWitness p v d (cofactorCeilRoot (d*v)+j) k) :
    Not (OwnerLineFamilyCompatible (multipliedQuadraticLineDirections U Q D E) p v) := by
  classical
  let A := cofactorCeilRoot (d*v)+j
  let a := quadraticMultipleCoordinate v d A k
  have hwa : d*v+Nat.sqrt (A*A-d*v)*Nat.sqrt (A*A-d*v) = A*A /\
      1 < Nat.gcd a v /\ Nat.gcd a v < p := hw
  have hcop : Nat.Coprime a 1 := Nat.coprime_one_right a
  have hmem : Membership.mem (multipliedQuadraticLineDirections U Q D E p v)
      (Prod.mk a 1) := by
    apply Finset.mem_union.mpr
    apply Or.inr
    apply Finset.mem_biUnion.mpr
    refine Exists.intro d (And.intro hd ?_)
    apply Finset.mem_biUnion.mpr
    refine Exists.intro j (And.intro (Finset.mem_range.mpr hj) ?_)
    apply Finset.mem_image.mpr
    exact Exists.intro k (And.intro (Finset.mem_filter.mpr
      (And.intro (Finset.mem_range.mpr hk) hw)) rfl)
  intro hc
  have he := primitive_line_content_gcd a 1 p v hcop
  have hlarge := hc (Prod.mk a 1) hmem hcop
    (show 1 < Nat.gcd a (a*p+1*v) by rw [he]; exact hwa.2.1)
  change p <= Nat.gcd a (a*p+1*v) at hlarge
  rw [he] at hlarge
  omega

/-- Exact agreement with the evaluated exclusion algorithm, including all overlaps. -/
theorem multipliedQuadraticLineDirections_compatible_iff
    (U : Finset Nat) (Q D E p v : Nat) :
    OwnerLineFamilyCompatible (multipliedQuadraticLineDirections U Q D E) p v <->
      OwnerLineFamilyCompatible (quadraticLineOwnerDirections Q D) p v /\
        forall d, Membership.mem U d -> forall j, j < E -> forall k, k < 2 ->
          Not (QuadraticMultipleWitness p v d (cofactorCeilRoot (d*v)+j) k) := by
  classical
  constructor
  next =>
    intro h
    refine And.intro ?_ ?_
    next =>
      intro z hz hc hg
      exact h z (Finset.mem_union.mpr (Or.inl hz)) hc hg
    next =>
      intro d hd j hj k hk hw
      exact not_multipliedQuadraticLineDirections_compatible hd hj hk hw h
  next =>
    intro h z hz hc hg
    rcases Finset.mem_union.mp hz with hbase | hmult
    next => exact h.1 z hbase hc hg
    next =>
      choose d hd using Finset.mem_biUnion.mp hmult
      choose j hj using Finset.mem_biUnion.mp hd.2
      choose k hk using Finset.mem_image.mp hj.2
      have hk' := Finset.mem_filter.mp hk.1
      exact False.elim (h.2 d hd.1 j (Finset.mem_range.mp hj.1)
        k (Finset.mem_range.mp hk'.1) hk'.2)

/-- The complete prime-candidate inequality with the multiplied quadratic family. -/
theorem prime_count_multiplied_quadratic_clock_bound {n T W : Nat}
    (U : Finset Nat) (Q D E : Nat) (S R : Finset Nat)
    (hR : forall ell, Membership.mem R ell -> 2 <= ell)
    (hn : 2 <= n) (hW0 : 0 < W)
    (hS : forall ell, Membership.mem S ell -> Nat.Prime ell /\ ell%2 = 1)
    (hW : forall ell, Membership.mem S ell -> Dvd.dvd ell W) :
    oddOwnerProductDrift S*(n : Int)+prefixClockMinimum S <=
      (oddOwnerPeriod 1 S : Int)*
        (((squareIntervalPrimes n).card : Int)+
          ((lowClockOwners S T).sum (fun p => oddCofactorWindowCapacity S W ((n+p-1)/p)) : Int)+
          ((ownerLineFamilyHighFactorCells
            (multipliedQuadraticLineDirections U Q D E) n T S R).card : Int)) :=
  prime_count_line_family_clock_bound (multipliedQuadraticLineDirections U Q D E)
    S R hR hn hW0 hS hW

end Nat.PrimeSieve
