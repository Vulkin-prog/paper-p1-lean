module

public import PaperP1.Algebra.SourceCurveLinearHilbert
public import PaperP1.Geometry.SourceProjectiveCurveEmbeddingHilbert
public import PaperP1.Algebra.SourceCurvePlaneEquationHilbert

/-! # Actual source curves have positive degree and a linear Hilbert polynomial in the chosen embedding -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceEmbeddedCurveLinearHilbert

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance nativeRing : CommRing (MvPolynomial (Fin 3) ℚ) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (p : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece c D I J))
  (hheight : (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p).height = 1)

local instance sourceQuotientRing : CommRing (SourceCurveQuotient.SourceRing s c D I J
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)

theorem exists_affine_polynomial : ∃ β : ℚ, GradedHilbertPolynomial.IsHilbertPolynomial
    (SourceCurveEmbeddingCoordinates.coordinatePiece c D I J hdeg hD
      (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (C (GradedHilbertPolynomial.multiplicity
      (SourceCurveEmbeddingCoordinates.coordinatePiece c D I J hdeg hD
        (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceProjectiveCurveEmbeddingHilbert.exists_polynomial s c D I J hs hdeg hD p hheight)) * X + C β) := by
  rw [SourceProjectiveCurveEmbeddingHilbert.multiplicity_eq s c D I J hs hdeg hD p hheight]
  let P := SourceCurveProjectivePointData.ideal s c D I J hdeg hD p
  let := SourceCurveProjectivePointData.ideal_prime s c D I J hdeg hD p
  have hP := SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p
  obtain ⟨e, f, he, hf0, hf, _hirr, hbase, _hmul⟩ :=
    SourceProjectiveCurveDegree.exists_degree_formula s c D I J hs hdeg hD p hheight
  have hbaseHP := SourceCurvePlaneEquationHilbert.base_isHilbertPolynomial s c D I J hs hD P f hf hf0 hbase
  obtain ⟨β, hβ⟩ := SourceCurveLinearHilbert.affine_polynomial_multiplicity s c D I J hs hD P hdeg hP
    ((D : ℚ) * (e : ℚ)) ((3 * (e : ℚ) - (e : ℚ) ^ 2) / 2)
    (mul_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr he)) hbaseHP
    (SourceProjectiveCurveDegree.exists_polynomial s c D I J hs hdeg hD p hheight)
  refine ⟨β, ?_⟩
  exact (GradedHilbertTransport.isHilbertPolynomial_iff _ _
    (SourceProjectiveCurveEmbeddingHilbert.piece_finrank s c D I J hdeg hD p) _).mpr hβ

theorem degree_pos : 0 < GradedHilbertPolynomial.multiplicity
    (SourceCurveEmbeddingCoordinates.coordinatePiece c D I J hdeg hD
      (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
    (SourceProjectiveCurveEmbeddingHilbert.exists_polynomial s c D I J hs hdeg hD p hheight) := by
  rw [SourceProjectiveCurveEmbeddingHilbert.multiplicity_eq s c D I J hs hdeg hD p hheight]
  let P := SourceCurveProjectivePointData.ideal s c D I J hdeg hD p
  let := SourceCurveProjectivePointData.ideal_prime s c D I J hdeg hD p
  obtain ⟨e, f, he, _hf0, _hf, _hirr, _hbase, hmul⟩ :=
    SourceProjectiveCurveDegree.exists_degree_formula s c D I J hs hdeg hD p hheight
  have hraw := hmul.trans (congrArg (fun r : ℕ ↦ (D : ℚ) * (e : ℚ) * (r : ℚ))
    (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p))
  have hr := (SourceCurveQuotient.rank_bounds s c D I J hs hD P hdeg).1
  have hrQ : (0 : ℚ) < SourceCurveQuotient.rank s c D I J hs hD P := by
    exact_mod_cast (show 0 < SourceCurveQuotient.rank s c D I J hs hD P by omega)
  rw [hraw]
  exact mul_pos (mul_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr he)) hrQ

end PaperP1.SourceEmbeddedCurveLinearHilbert
