import RobinBV

/-!
# Headline solutions
-/

theorem oddFundamentalDiscriminant_quadraticZetaFactorization
    (D : Int)
    (habs : 1 < D.natAbs)
    (hsquarefree : Squarefree D.natAbs)
    (hmod : D % 4 = 1) :
    letI : NeZero D.natAbs := NeZero.mk (Nat.ne_zero_of_lt habs)
    Exists fun K : Type =>
      Exists fun fieldK : Field K =>
        letI : Field K := fieldK
        Exists fun numberFieldK : NumberField K =>
          letI : NumberField K := numberFieldK
          Exists fun chi : DirichletCharacter Complex D.natAbs =>
            And (NumberField.discr K = D)
              (And (Module.finrank Rat K = 2)
                (And
                  (DirichletCharacter.IsPrimitive chi)
                  (forall {s : Complex}, 1 < s.re ->
                    NumberField.dedekindZeta K s =
                      riemannZeta s *
                        DirichletCharacter.LFunction chi s))) := by
  let D0 : NumberField.OddFundamentalDiscriminant := {
    value := D
    abs_gt_one := habs
    squarefree_natAbs := hsquarefree
    mod_four := hmod }
  let fieldK : Field D0.QuadraticField := inferInstance
  let numberFieldK : @NumberField D0.QuadraticField fieldK :=
    D0.quadraticField_numberField
  refine Exists.intro D0.QuadraticField ?_
  refine Exists.intro fieldK ?_
  letI : Field D0.QuadraticField := fieldK
  refine Exists.intro numberFieldK ?_
  letI : NumberField D0.QuadraticField := numberFieldK
  refine Exists.intro D0.character ?_
  apply And.intro
  next =>
    simpa only [D0] using D0.discr_quadraticField
  next =>
    apply And.intro
    next =>
      exact D0.finrank_quadraticField
    next =>
      apply And.intro
      next =>
        exact D0.character_isPrimitive
      next =>
        intro s hs
        exact D0.dedekindZeta_quadraticField_eq_riemannZeta_mul_LFunction hs
