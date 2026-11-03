module

public import PaperP1.Algebra.HomogeneousLinearNormalization
public import PaperP1.Algebra.VeroneseFinitePowerParameters
public import PaperP1.Algebra.TwoVariableGradedHilbert
public import PaperP1.Algebra.MvPolynomialHilbert
public import PaperP1.Algebra.GradedVeronesePieceEquiv
public import PaperP1.Algebra.GradedVeroneseQuotient

/-! # Finite two-parameter normalization and Hilbert existence for actual plane quotient Veroneses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneQuotientVeroneseNormalization

open MvPolynomial

variable {F : Type*} [Field F] [Infinite F]

local instance polynomialRing : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance polynomialSemiring : Semiring (MvPolynomial (Fin 3) F) := (polynomialRing (F := F)).toSemiring
attribute [local instance] MvPolynomial.gradedAlgebra

variable (I : Ideal (MvPolynomial (Fin 3) F))
  (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) F)) (D : ℕ) (hD : 0 < D)

abbrev Ring := GradedVeroneseQuotient.Target (MvPolynomial.homogeneousSubmodule (Fin 3) F) I D

def piece (n : ℕ) : Submodule F (Ring I D) :=
  GradedVeroneseQuotient.targetPiece (MvPolynomial.homogeneousSubmodule (Fin 3) F) I hI D n

@[instance_reducible] def grading : GradedAlgebra (piece I hI D) :=
  GradedVeroneseQuotient.targetGrading (MvPolynomial.homogeneousSubmodule (Fin 3) F) I hI D hD

include hI hD in
theorem exists_parameters {e : ℕ} (p : MvPolynomial (Fin 3) F)
    (hp : p.IsHomogeneous e) (hp0 : p ≠ 0) (hmem : p ∈ I) :
    ∃ g : Fin 2 → Ring I D, (∀ i, g i ∈ piece I hI D 1) ∧ (aeval (R := F) g).Finite := by
  let := HomogeneousQuotientGrading.grading (MvPolynomial.homogeneousSubmodule (Fin 3) F) I hI
  obtain ⟨g, hg, hf⟩ := HomogeneousLinearNormalization.exists_parameters I p hp hp0 hmem
  refine ⟨VeroneseFinitePowerParameters.parameters (HomogeneousQuotientGrading.piece
      (MvPolynomial.homogeneousSubmodule (Fin 3) F) I) g hg D,
    VeroneseFinitePowerParameters.parameter_mem _ g hg D, ?_⟩
  exact VeroneseFinitePowerParameters.finite _ g hg D hD hf

include hI in
omit [Infinite F] in
theorem piece_finite (n : ℕ) : Module.Finite F (piece I hI D n) := by
  let := HomogeneousQuotientGrading.grading (MvPolynomial.homogeneousSubmodule (Fin 3) F) I hI
  have : Module.Finite F (MvPolynomial.homogeneousSubmodule (Fin 3) F (n * D)) :=
    MvPolynomialHilbert.piece_finite F (Fin 3) (n * D)
  have : Module.Finite F (HomogeneousQuotientGrading.piece
      (MvPolynomial.homogeneousSubmodule (Fin 3) F) I (n * D)) :=
    HomogeneousQuotientGrading.piece_finite (MvPolynomial.homogeneousSubmodule (Fin 3) F) I (n * D)
  exact GradedVeronesePieceEquiv.finite _ D n

include hI hD in
theorem exists_polynomial [I.IsPrime] {e : ℕ} (p : MvPolynomial (Fin 3) F)
    (hp : p.IsHomogeneous e) (hp0 : p ≠ 0) (hmem : p ∈ I) :
    ∃ q, GradedHilbertPolynomial.IsHilbertPolynomial (piece I hI D) q := by
  let := grading I hI D hD
  let (n : ℕ) : Module.Finite F (piece I hI D n) := piece_finite I hI D n
  obtain ⟨g, hg, hf⟩ := exists_parameters I hI D hD p hp hp0 hmem
  exact TwoVariableGradedHilbert.exists_polynomial_of_finite (piece I hI D) g hg hf

end PaperP1.PlaneQuotientVeroneseNormalization
