/- Copyright (c) 2026 Jonas Whidden. -/
import RobinBV.Sieve.Helpers.SquareCorridorTest
import RobinBV.Sieve.Proof.AlmostAllCorridorSummability
import RobinBV.Sieve.Proof.AlmostAllZeroPartition

/-!
# Almost-all corridor partition

The inner and outer actual-zero series are partitioned at real part 79/100,
with all summability and tsum identities retained.
-/

set_option autoImplicit false

open scoped Classical

namespace RobinBV.Sieve

theorem square_corridor_inner_zero_partition
    {theta eta x : Real}
    (hs : Summable (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorInnerTest theta eta x)
          (Zeta23.gammaOf rho))) :
    (And (Summable (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if (rho : Complex).re <= 79/100 then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorInnerTest theta eta x)
            (Zeta23.gammaOf rho) else 0))
    (And (Summable (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if Not ((rho : Complex).re <= 79/100) then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorInnerTest theta eta x)
            (Zeta23.gammaOf rho) else 0))
    (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorInnerTest theta eta x)
          (Zeta23.gammaOf rho)) =
      tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if (rho : Complex).re <= 79/100 then
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorInnerTest theta eta x)
              (Zeta23.gammaOf rho) else 0) +
      tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if Not ((rho : Complex).re <= 79/100) then
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorInnerTest theta eta x)
          (Zeta23.gammaOf rho) else 0)))) := by
  exact summable_predicate_partition _ (fun rho : Zeta23.zetaZeroConfig.carrier =>
    (rho : Complex).re <= 79/100) hs

theorem square_corridor_outer_zero_partition
    {theta eta x : Real}
    (hs : Summable (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf rho))) :
    (And (Summable (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if (rho : Complex).re <= 79/100 then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorOuterTest theta eta x)
            (Zeta23.gammaOf rho) else 0))
    (And (Summable (fun rho : Zeta23.zetaZeroConfig.carrier =>
      if Not ((rho : Complex).re <= 79/100) then
        (Zeta23.zetaZeroConfig.mult rho : Complex) *
          Zeta23.paperFT (squareCorridorOuterTest theta eta x)
            (Zeta23.gammaOf rho) else 0))
    (tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf rho)) =
      tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if (rho : Complex).re <= 79/100 then
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorOuterTest theta eta x)
              (Zeta23.gammaOf rho) else 0) +
      tsum (fun rho : Zeta23.zetaZeroConfig.carrier =>
        if Not ((rho : Complex).re <= 79/100) then
          (Zeta23.zetaZeroConfig.mult rho : Complex) *
            Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf rho) else 0)))) := by
  exact summable_predicate_partition _ (fun rho : Zeta23.zetaZeroConfig.carrier =>
    (rho : Complex).re <= 79/100) hs

theorem square_corridor_inner_zero_partition_unconditional
    {theta eta x : Real} (htheta : 0 <= theta) (htheta2 : 2*theta < 1)
    (heta : 0 < eta) (hx : 0 < x) :
    let f : Zeta23.zetaZeroConfig.carrier -> Complex := fun rho =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorInnerTest theta eta x)
          (Zeta23.gammaOf rho)
    let p : Zeta23.zetaZeroConfig.carrier -> Prop := fun rho =>
      (rho : Complex).re <= 79/100
    And (Summable (fun rho => if p rho then f rho else 0))
      (And (Summable (fun rho => if Not (p rho) then f rho else 0))
        (tsum f = tsum (fun rho => if p rho then f rho else 0) +
          tsum (fun rho => if Not (p rho) then f rho else 0))) := by
  dsimp
  exact square_corridor_inner_zero_partition
    (square_corridor_inner_zero_sum_summable htheta htheta2 heta hx)

theorem square_corridor_outer_zero_partition_unconditional
    {theta eta x : Real} (htheta : 0 <= theta)
    (heta : 0 < eta) (hx : 0 < x) :
    let f : Zeta23.zetaZeroConfig.carrier -> Complex := fun rho =>
      (Zeta23.zetaZeroConfig.mult rho : Complex) *
        Zeta23.paperFT (squareCorridorOuterTest theta eta x)
          (Zeta23.gammaOf rho)
    let p : Zeta23.zetaZeroConfig.carrier -> Prop := fun rho =>
      (rho : Complex).re <= 79/100
    And (Summable (fun rho => if p rho then f rho else 0))
      (And (Summable (fun rho => if Not (p rho) then f rho else 0))
        (tsum f = tsum (fun rho => if p rho then f rho else 0) +
          tsum (fun rho => if Not (p rho) then f rho else 0))) := by
  dsimp
  exact square_corridor_outer_zero_partition
    (square_corridor_outer_zero_sum_summable htheta heta hx)

end RobinBV.Sieve
