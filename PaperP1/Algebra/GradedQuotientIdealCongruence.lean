module

public import PaperP1.Algebra.FiniteGradedParameters
public import PaperP1.Algebra.HomogeneousQuotientGrading

/-! # Finite parameters and actual Hilbert polynomials respect equality of quotient ideals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedQuotientIdealCongruence

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A)

local instance quotientRing (I : Ideal A) : CommRing (A ⧸ I) := inferInstance
local instance quotientSemiring (I : Ideal A) : Semiring (A ⧸ I) := (quotientRing I).toSemiring
local instance quotientModule (I : Ideal A) : Module F (A ⧸ I) := Algebra.toModule

theorem parameters {I J : Ideal A} (h : I = J)
    (hp : FiniteGradedParameters.HasParameters (HomogeneousQuotientGrading.piece G I)) :
    FiniteGradedParameters.HasParameters (HomogeneousQuotientGrading.piece G J) := by
  subst J
  exact hp

theorem hilbertPolynomial {I J : Ideal A} (h : I = J) {p : Polynomial ℚ}
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial (HomogeneousQuotientGrading.piece G I) p) :
    GradedHilbertPolynomial.IsHilbertPolynomial (HomogeneousQuotientGrading.piece G J) p := by
  subst J
  exact hp

end PaperP1.GradedQuotientIdealCongruence
