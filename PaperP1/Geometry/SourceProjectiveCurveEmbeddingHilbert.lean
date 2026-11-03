module

public import PaperP1.Geometry.SourceCurveEmbeddingCoordinates
public import PaperP1.Geometry.SourceProjectiveCurveDegree
public import PaperP1.Algebra.GradedHilbertTransport

/-! # The actual curve coordinate quotient in the chosen projective embedding has its source Hilbert multiplicity -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveCurveEmbeddingHilbert

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type u} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (p : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece c D I J))

local instance sourceQuotientRing : CommRing (SourceCurveQuotient.SourceRing s c D I J
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)

theorem piece_finrank (n : ℕ) : Module.finrank F
    (SourceCurveEmbeddingCoordinates.coordinatePiece c D I J hdeg hD
      (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) n) =
    Module.finrank F (SourceCurveQuotient.sourcePiece s c D I J
      (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) n) :=
  SourceCurveEmbeddingCoordinates.piece_finrank c D I J hdeg hD _
    (SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD p) n

variable [Infinite F] (hheight : (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p).height = 1)

include hs hheight in
theorem exists_polynomial : ∃ q, GradedHilbertPolynomial.IsHilbertPolynomial
    (SourceCurveEmbeddingCoordinates.coordinatePiece c D I J hdeg hD
      (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) q :=
  (GradedHilbertTransport.exists_polynomial_iff _ _ (piece_finrank s c D I J hdeg hD p)).mpr
    (SourceProjectiveCurveDegree.exists_polynomial s c D I J hs hdeg hD p hheight)

theorem multiplicity_eq : GradedHilbertPolynomial.multiplicity
    (SourceCurveEmbeddingCoordinates.coordinatePiece c D I J hdeg hD
      (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (exists_polynomial s c D I J hs hdeg hD p hheight) =
    GradedHilbertPolynomial.multiplicity
      (SourceCurveQuotient.sourcePiece s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceProjectiveCurveDegree.exists_polynomial s c D I J hs hdeg hD p hheight) :=
  GradedHilbertTransport.multiplicity_eq _ _ (piece_finrank s c D I J hdeg hD p) _ _

theorem exists_degree_formula : beta%
    (fun {m n : ℕ} (_ : m = n) ↦
      ∃ (e : ℕ) (f : MvPolynomial (Fin 3) F), 0 < e ∧ f ≠ 0 ∧ f.IsHomogeneous e ∧ Irreducible f ∧
        SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) =
          PlaneCurveVeroneseBaseQuotient.ideal F f D ∧
        GradedHilbertPolynomial.multiplicity
          (SourceCurveEmbeddingCoordinates.coordinatePiece c D I J hdeg hD
            (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
          (exists_polynomial s c D I J hs hdeg hD p hheight) = (D : ℚ) * (e : ℚ) * (m : ℚ))
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p) := by
  obtain ⟨e, f, he, hf0, hf, hirr, hbase, hmul⟩ :=
    SourceProjectiveCurveDegree.exists_degree_formula s c D I J hs hdeg hD p hheight
  exact ⟨e, f, he, hf0, hf, hirr, hbase, (multiplicity_eq s c D I J hs hdeg hD p hheight).trans hmul⟩

end PaperP1.SourceProjectiveCurveEmbeddingHilbert
