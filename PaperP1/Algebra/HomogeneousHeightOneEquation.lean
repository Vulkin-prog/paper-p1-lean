module

public import PaperP1.Algebra.HomogeneousPrincipalIdealGenerator
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # A height-one homogeneous polynomial prime is an actual positive-degree homogeneous equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousHeightOneEquation

variable {F σ : Type*} [Field F]

local instance polynomialRing : CommRing (MvPolynomial σ F) := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_equation (I : Ideal (MvPolynomial σ F)) [I.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ F)) (hh : I.height = 1) :
    ∃ (e : ℕ) (p : MvPolynomial σ F), 0 < e ∧ p ≠ 0 ∧ p.IsHomogeneous e ∧ I = Ideal.span {p} := by
  have := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh
  exact HomogeneousPrincipalIdealGenerator.exists_positive_generator I hI
    (Ideal.ne_bot_of_height_eq_one hh) (Ideal.IsPrime.ne_top inferInstance)

end PaperP1.HomogeneousHeightOneEquation
