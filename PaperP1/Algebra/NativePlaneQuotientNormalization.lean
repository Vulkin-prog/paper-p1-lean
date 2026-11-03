module

public import PaperP1.Algebra.PlaneQuotientVeroneseNormalization
public import PaperP1.Algebra.FiniteGradedParameters
public import PaperP1.Algebra.SourceVeroneseGrading

/-! # Finite parameters and Hilbert existence for literal native contracted plane quotients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NativePlaneQuotientNormalization

open MvPolynomial

variable {F : Type*} [Field F] [Infinite F]

local instance polynomialRing : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance polynomialSemiring : Semiring (MvPolynomial (Fin 3) F) := (polynomialRing (F := F)).toSemiring
attribute [local instance] MvPolynomial.gradedAlgebra

variable (I : Ideal (MvPolynomial (Fin 3) F))
  (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) F)) (D : ℕ) (hD : 0 < D)

abbrev Ring := StandardBaseVeronese.nativeVeronese F D ⧸
  GradedVeroneseQuotient.contracted (MvPolynomial.homogeneousSubmodule (Fin 3) F) I D

local instance nativeQuotientRing : CommRing (Ring I D) := inferInstance
local instance nativeQuotientSemiring : Semiring (Ring I D) := (nativeQuotientRing I D).toSemiring
local instance nativeQuotientModule : Module F (Ring I D) := Algebra.toModule

def piece (n : ℕ) : Submodule F (Ring I D) :=
  GradedVeroneseQuotient.piece (MvPolynomial.homogeneousSubmodule (Fin 3) F) I D n

@[instance_reducible] def grading : GradedAlgebra (piece I D) := by
  letI := SourceVeroneseGrading.nativeGrading F D hD
  exact HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D)
    (GradedVeroneseQuotient.contracted (MvPolynomial.homogeneousSubmodule (Fin 3) F) I D)
    (GradedVeroneseQuotient.contracted_homogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) F) I hI D hD)

include hI hD in
theorem hasParameters {e : ℕ} (p : MvPolynomial (Fin 3) F)
    (hp : p.IsHomogeneous e) (hp0 : p ≠ 0) (hmem : p ∈ I) :
    FiniteGradedParameters.HasParameters (piece I D) := by
  apply FiniteGradedParameters.of_equiv (piece I D) (PlaneQuotientVeroneseNormalization.piece I hI D)
    (GradedVeroneseQuotient.equiv (MvPolynomial.homogeneousSubmodule (Fin 3) F) I hI D hD)
    (GradedVeroneseQuotient.piece_map (MvPolynomial.homogeneousSubmodule (Fin 3) F) I hI D hD 1)
  exact PlaneQuotientVeroneseNormalization.exists_parameters I hI D hD p hp hp0 hmem

omit [Infinite F] in
theorem piece_finite (n : ℕ) : Module.Finite F (piece I D n) := by
  have : Module.Finite F (MvPolynomial.homogeneousSubmodule (Fin 3) F (n * D)) :=
    MvPolynomialHilbert.piece_finite F (Fin 3) (n * D)
  have : Module.Finite F (SourceVeroneseGrading.nativePiece F D n) :=
    GradedVeronesePieceEquiv.finite (MvPolynomial.homogeneousSubmodule (Fin 3) F) D n
  exact HomogeneousQuotientGrading.piece_finite (SourceVeroneseGrading.nativePiece F D)
    (GradedVeroneseQuotient.contracted (MvPolynomial.homogeneousSubmodule (Fin 3) F) I D) n

include hI hD in
theorem exists_polynomial [I.IsPrime] {e : ℕ} (p : MvPolynomial (Fin 3) F)
    (hp : p.IsHomogeneous e) (hp0 : p ≠ 0) (hmem : p ∈ I) :
    ∃ q, GradedHilbertPolynomial.IsHilbertPolynomial (piece I D) q := by
  let := grading I hI D hD
  let (n : ℕ) : Module.Finite F (piece I D n) := piece_finite I D n
  have : IsDomain (Ring I D) := by
    change IsDomain (StandardBaseVeronese.nativeVeronese F D ⧸
      I.comap (StandardBaseVeronese.nativeVeronese F D).val.toRingHom)
    infer_instance
  exact FiniteGradedParameters.exists_polynomial (piece I D) (hasParameters I hI D hD p hp hp0 hmem)

end PaperP1.NativePlaneQuotientNormalization
