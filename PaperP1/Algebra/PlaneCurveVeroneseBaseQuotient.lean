module

public import PaperP1.Algebra.GradedVeroneseQuotient
public import PaperP1.Algebra.PlaneCurveVeroneseHilbert
public import PaperP1.Algebra.SourceVeroneseGrading
public import Mathlib.Tactic.Ring

/-! # The literal native Veronese quotient defined by a homogeneous plane equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneCurveVeroneseBaseQuotient

open Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

local instance polynomialRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance

variable (F : Type*) [Field F] {e : ℕ} (f : MvPolynomial (Fin 3) F)
  (hf : f.IsHomogeneous e) (D : ℕ) (hD : 0 < D)

def ideal : Ideal (StandardBaseVeronese.nativeVeronese F D) :=
  GradedVeroneseQuotient.contracted (MvPolynomial.homogeneousSubmodule (Fin 3) F)
    (HomogeneousPrincipalQuotient.ideal f) D

abbrev CoordinateRing := StandardBaseVeronese.nativeVeronese F D ⧸ ideal F f D

def piece (n : ℕ) : Submodule F (CoordinateRing F f D) :=
  HomogeneousQuotientGrading.piece (SourceVeroneseGrading.nativePiece F D) (ideal F f D) n

def toPlane : CoordinateRing F f D ≃ₐ[F] PlaneCurveVeroneseHilbert.CoordinateRing F f hf D :=
  GradedVeroneseQuotient.equiv (MvPolynomial.homogeneousSubmodule (Fin 3) F)
    (HomogeneousPrincipalQuotient.ideal f) (PlaneCurveHilbert.ideal_homogeneous F f hf) D hD

include hf hD in
theorem ideal_homogeneous :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    (ideal F f D).IsHomogeneous (SourceVeroneseGrading.nativePiece F D) :=
  GradedVeroneseQuotient.contracted_homogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) F)
    (HomogeneousPrincipalQuotient.ideal f) (PlaneCurveHilbert.ideal_homogeneous F f hf) D hD

@[instance_reducible] def grading : GradedAlgebra (piece F f D) := by
  letI := SourceVeroneseGrading.nativeGrading F D hD
  exact HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D) (ideal F f D)
    (ideal_homogeneous F f hf D hD)

def pieceEquiv (n : ℕ) : piece F f D n ≃ₗ[F] PlaneCurveVeroneseHilbert.piece F f hf D n :=
  GradedVeroneseQuotient.pieceEquiv (MvPolynomial.homogeneousSubmodule (Fin 3) F)
    (HomogeneousPrincipalQuotient.ideal f) (PlaneCurveHilbert.ideal_homogeneous F f hf) D hD n

include hf hD in
theorem piece_finrank (n : ℕ) : Module.finrank F (piece F f D n) =
    Module.finrank F (PlaneCurveVeroneseHilbert.piece F f hf D n) :=
  (pieceEquiv F f hf D hD n).finrank_eq

include hf hD in
theorem piece_finite (n : ℕ) : Module.Finite F (piece F f D n) := by
  have := PlaneCurveVeroneseHilbert.piece_finite F f hf D n
  exact Module.Finite.of_surjective (pieceEquiv F f hf D hD n).symm.toLinearMap
    (pieceEquiv F f hf D hD n).symm.surjective

variable (hf0 : f ≠ 0)

include hf hf0 hD in
theorem isHilbertPolynomial : GradedHilbertPolynomial.IsHilbertPolynomial (piece F f D)
    (GradedVeroneseHilbertPolynomial.rescale D (PlaneCurveHilbert.polynomial e)) := by
  obtain ⟨N, hN⟩ := PlaneCurveVeroneseHilbert.isHilbertPolynomial F f hf hf0 D hD
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [piece_finrank F f hf D hD]
  exact hN n hn

include hf hf0 hD in
theorem exists_polynomial : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (piece F f D) p :=
  ⟨_, isHilbertPolynomial F f hf D hD hf0⟩

theorem rescale_polynomial : GradedVeroneseHilbertPolynomial.rescale D (PlaneCurveHilbert.polynomial e) =
    C ((D : ℚ) * (e : ℚ)) * X + C ((3 * (e : ℚ) - (e : ℚ) ^ 2) / 2) := by
  simp only [GradedVeroneseHilbertPolynomial.rescale, PlaneCurveHilbert.polynomial,
    add_comp, mul_comp, C_comp, X_comp, map_mul]
  ring

include hf hf0 hD in
theorem affine_isHilbertPolynomial : GradedHilbertPolynomial.IsHilbertPolynomial (piece F f D)
    (C ((D : ℚ) * (e : ℚ)) * X + C ((3 * (e : ℚ) - (e : ℚ) ^ 2) / 2)) := by
  rw [← rescale_polynomial (e := e) D]
  exact isHilbertPolynomial F f hf D hD hf0

include hD in
theorem multiplicity (he : 0 < e) : GradedHilbertPolynomial.multiplicity (piece F f D)
    (exists_polynomial F f hf D hD hf0) = ((D * e : ℕ) : ℚ) := by
  rw [GradedHilbertPolynomial.multiplicity_eq _ _ _ (isHilbertPolynomial F f hf D hD hf0),
    PlaneCurveVeroneseHilbert.polynomial_natDegree D hD he,
    PlaneCurveVeroneseHilbert.polynomial_leadingCoeff D hD he]
  simp

end PaperP1.PlaneCurveVeroneseBaseQuotient
