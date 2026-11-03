module

public import PaperP1.Geometry.SourceEmbeddedCurveLinearHilbert
public import PaperP1.Geometry.SourceEmbeddedCurvePointData
public import PaperP1.Geometry.ProjectiveCurveData

/-! # Actual source projective curves construct their own generic prime/Hilbert curve data -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceProjectiveCurveData

open PaperP1.HomogeneousSplitRadicalData

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

structure Curve (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ)
    (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D) where
  point : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece c D I J)
  height : (SourceCurveProjectivePointData.ideal s c D I J hdeg hD point).height = 1

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (Γ : Curve s c D I J hdeg hD)

def sourceIdeal : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J) :=
  SourceCurveProjectivePointData.ideal s c D I J hdeg hD Γ.point

def ideal : Ideal (MvPolynomial (SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D) ℚ) :=
  SourceCurveEmbeddingCoordinates.coordinateIdeal c D I J hdeg hD (sourceIdeal s c D I J hdeg hD Γ)

def degree : ℚ := GradedHilbertPolynomial.multiplicity
  (SourceCurveEmbeddingCoordinates.coordinatePiece c D I J hdeg hD (sourceIdeal s c D I J hdeg hD Γ))
  (SourceProjectiveCurveEmbeddingHilbert.exists_polynomial s c D I J hs hdeg hD Γ.point Γ.height)

theorem degree_pos : 0 < degree s c D I J hs hdeg hD Γ :=
  SourceEmbeddedCurveLinearHilbert.degree_pos s c D I J hs hdeg hD Γ.point Γ.height

def toCurve : ProjectiveCurveData.Curve (SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D) where
  ideal := ideal s c D I J hdeg hD Γ
  prime := SourceEmbeddedCurvePointData.ideal_prime s c D I J hdeg hD Γ.point
  homogeneous := SourceCurveEmbeddingCoordinates.coordinateIdeal_homogeneous c D I J hdeg hD
    (sourceIdeal s c D I J hdeg hD Γ) (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD Γ.point)
  degree := degree s c D I J hs hdeg hD Γ
  degree_pos := degree_pos s c D I J hs hdeg hD Γ
  constant := (SourceEmbeddedCurveLinearHilbert.exists_affine_polynomial s c D I J hs hdeg hD Γ.point Γ.height).choose
  hilbert := (SourceEmbeddedCurveLinearHilbert.exists_affine_polynomial s c D I J hs hdeg hD Γ.point Γ.height).choose_spec

theorem toCurve_ideal : (toCurve s c D I J hs hdeg hD Γ).ideal = ideal s c D I J hdeg hD Γ := rfl

theorem toCurve_degree : (toCurve s c D I J hs hdeg hD Γ).degree = degree s c D I J hs hdeg hD Γ := rfl

end PaperP1.SourceProjectiveCurveData
