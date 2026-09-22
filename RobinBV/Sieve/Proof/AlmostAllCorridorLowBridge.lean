/- Copyright (c) 2026 Jonas Whidden. -/
import RobinBV.Sieve.Proof.AlmostAllCorridorPartition

/-!
# Low-packet corridor bridge

These consumers subtract the high-real-part packet from a full corridor
lower bound without dropping the exact norm and multiplicity bookkeeping.
-/

set_option autoImplicit false

open scoped Classical

namespace RobinBV.Sieve

theorem square_corridor_inner_low_norm_bridge
    {delta N theta eta x : Real}
    (hd : 0 <= delta) (hN : 0 <= N)
    (htheta : 0 <= theta) (htheta2 : 2*theta < 1)
    (heta : 0 < eta) (hx : 0 < x)
    (hfull : delta*N <= norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorInnerTest theta eta x)
          (Zeta23.gammaOf rho))))
    (hhigh : norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if Not ((rho : Complex).re <= 79/100) then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorInnerTest theta eta x)
            (Zeta23.gammaOf rho) else 0)) <= delta*N/2) :
    delta*N/2 <= norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if (rho : Complex).re <= 79/100 then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorInnerTest theta eta x)
            (Zeta23.gammaOf rho) else 0)) := by
  have hp := square_corridor_inner_zero_partition_unconditional htheta htheta2 heta hx
  have hfull' : delta*N <= norm (
      tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if (rho : Complex).re <= 79/100 then
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorInnerTest theta eta x)
              (Zeta23.gammaOf rho) else 0) +
      tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if Not ((rho : Complex).re <= 79/100) then
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorInnerTest theta eta x)
              (Zeta23.gammaOf rho) else 0)) := by
    have hsplit := hp.2.2
    dsimp only at hsplit
    rw [<- hsplit]
    exact hfull
  exact low_norm_from_full_and_high hd hN hfull' hhigh

theorem square_corridor_outer_low_norm_bridge
    {delta N theta eta x : Real}
    (hd : 0 <= delta) (hN : 0 <= N)
    (htheta : 0 <= theta) (heta : 0 < eta) (hx : 0 < x)
    (hfull : delta*N <= norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf rho))))
    (hhigh : norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if Not ((rho : Complex).re <= 79/100) then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorOuterTest theta eta x)
            (Zeta23.gammaOf rho) else 0)) <= delta*N/2) :
    delta*N/2 <= norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if (rho : Complex).re <= 79/100 then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorOuterTest theta eta x)
            (Zeta23.gammaOf rho) else 0)) := by
  have hp := square_corridor_outer_zero_partition_unconditional htheta heta hx
  have hfull' : delta*N <= norm (
      tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if (rho : Complex).re <= 79/100 then
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorOuterTest theta eta x)
              (Zeta23.gammaOf rho) else 0) +
      tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if Not ((rho : Complex).re <= 79/100) then
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorOuterTest theta eta x)
              (Zeta23.gammaOf rho) else 0)) := by
    have hsplit := hp.2.2
    dsimp only at hsplit
    rw [<- hsplit]
    exact hfull
  exact low_norm_from_full_and_high hd hN hfull' hhigh

theorem square_corridor_low_fourth_from_full_or_high
    {delta N theta eta x : Real}
    (hd : 0 <= delta) (hN : 0 <= N)
    (htheta : 0 <= theta) (htheta2 : 2*theta < 1)
    (heta : 0 < eta) (hx : 0 < x)
    (hfull :
      Or
        (delta*N <= norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorInnerTest theta eta x)
              (Zeta23.gammaOf rho))))
        (delta*N <= norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorOuterTest theta eta x)
              (Zeta23.gammaOf rho)))))
    (hhigh :
      And
        (norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          if Not ((rho : Complex).re <= 79/100) then
            (Zeta23.zetaZeroConfig.mult rho : Complex) *
              Zeta23.paperFT (squareCorridorInnerTest theta eta x)
                (Zeta23.gammaOf rho) else 0)) <= delta*N/2)
        (norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
          if Not ((rho : Complex).re <= 79/100) then
            (Zeta23.zetaZeroConfig.mult rho : Complex) *
              Zeta23.paperFT (squareCorridorOuterTest theta eta x)
                (Zeta23.gammaOf rho) else 0)) <= delta*N/2)) :
    ENNReal.ofReal ((delta*N/2)^4) <= ENNReal.ofReal (
      norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if (rho : Complex).re <= 79/100 then
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorInnerTest theta eta x)
              (Zeta23.gammaOf rho) else 0))^4 +
      norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if (rho : Complex).re <= 79/100 then
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorOuterTest theta eta x)
              (Zeta23.gammaOf rho) else 0))^4) := by
  have hfourth {a b : Real} (ha : 0 <= a) (hb : 0 <= b) (hab : a <= b) :
      a^4 <= b^4 := by
    have hs := mul_le_mul hab hab ha hb
    have h4 := mul_le_mul hs hs (mul_nonneg ha ha) (mul_nonneg hb hb)
    calc
      a^4 = (a*a)*(a*a) := by ring
      _ <= (b*b)*(b*b) := h4
      _ = b^4 := by ring
  rcases hfull with hinner | houter
  next =>
    have hlow := square_corridor_inner_low_norm_bridge
      hd hN htheta htheta2 heta hx hinner hhigh.1
    have ha : 0 <= delta*N/2 := by positivity
    have hpow := hfourth ha (norm_nonneg _) hlow
    apply ENNReal.ofReal_le_ofReal
    have hnonneg : 0 <= norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if (rho : Complex).re <= 79/100 then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorOuterTest theta eta x)
            (Zeta23.gammaOf rho) else 0))^4 := by positivity
    linarith
  next =>
    have hlow := square_corridor_outer_low_norm_bridge
      hd hN htheta heta hx houter hhigh.2
    have ha : 0 <= delta*N/2 := by positivity
    have hpow := hfourth ha (norm_nonneg _) hlow
    apply ENNReal.ofReal_le_ofReal
    have hnonneg : 0 <= norm (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if (rho : Complex).re <= 79/100 then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorInnerTest theta eta x)
            (Zeta23.gammaOf rho) else 0))^4 := by positivity
    linarith

end RobinBV.Sieve
