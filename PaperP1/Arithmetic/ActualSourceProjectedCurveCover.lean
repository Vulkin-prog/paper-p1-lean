module

public import PaperP1.Geometry.SourceSurfaceCurvePullback
public import PaperP1.Arithmetic.SourceImageIntegerPointEvaluation

/-! # Exact projected polynomial vanishing lifts the original normalized integer points to a uniformly bounded source-curve family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualSourceProjectedCurveCover

open MvPolynomial HomogeneousSplitRadicalData SourceVeroneseGrading SourceProjectiveEmbedding
  SourceProjectiveCurveData SourceSurfaceBoundedProjection LinearHypersurfaceImage

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) := index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
  (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
  (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
  (u : GeneratorIndex ℚ (Fin s.length) D → ℕ)

include hc hne hI hJ

theorem uniform_curve_cover
    (Q : Ideal (CoordinateRing (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
      (primitive c D I J u))) [Q.IsPrime]
    (hQ : letI := sourceGrading c D I J hdeg hD;
      letI := grading (sourcePiece c D I J) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
        (SourceSurfacePowerParameters.parameter_mem s c D hD I J hs) (primitive c D I J u)
        (SourceImageIntegerPointEvaluation.primitive_mem s c D hD I J hdeg u);
      Q.IsHomogeneous (piece (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
        (primitive c D I J u)))
    (hheight : Q.height = 1) (E β : ℚ)
    (hcurve : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece
        (piece (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs) (primitive c D I J u)) Q)
      (Polynomial.C E * Polynomial.X + Polynomial.C β))
    (M : ℕ) (hEM : E ≤ (M : ℚ)) :
    ∃ curves : Finset (Curve s c D I J hdeg hD),
      curves.card ≤ M * (2 ^ s.length * D ^ 2) ∧
      (∀ Γ ∈ curves, degree s c D I J hs hdeg hD Γ ≤ ((M * (2 ^ s.length * D ^ 2) : ℕ) : ℚ)) ∧
      ∀ (H : ℕ) (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
        (_hv : v ∈ SourceIntegerPoints.curvePoints D
          (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H),
        (∀ P ∈ SourceImageIntegerPointEvaluation.imageIdeal s c D hD I J hs u Q,
          eval (fun i ↦ (SourceIntegerHypersurfaceProjection.projection D u v i : ℚ)) P = 0) →
        ∃ Γ ∈ curves, v ∈ SourceIntegerPoints.curvePoints D (SourceProjectiveCurveData.ideal s c D I J hdeg hD Γ) H := by
  obtain ⟨curves, hcount, hdegree, hcover⟩ := SourceSurfaceCurvePullback.uniform_curve_cover
    s c D I J hs hdeg hD hc hne hI hJ (primitive c D I J u)
    (SourceImageIntegerPointEvaluation.primitive_mem s c D hD I J hdeg u) Q hQ hheight E β hcurve M hEM
  refine ⟨curves, hcount, hdegree, ?_⟩
  intro H v hv hpoint
  exact hcover H v hv ((SourceImageIntegerPointEvaluation.annihilates_iff s c D hD I J hs hdeg u Q
    v (SourceIntegerPointEvaluation.valid_of_mem c D I J hdeg hD H v hv)).mpr hpoint)

end PaperP1.ActualSourceProjectedCurveCover
