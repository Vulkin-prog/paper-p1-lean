module

public import PaperP1.Geometry.SourceCurveEmbeddingCoordinates
public import PaperP1.Geometry.SourceCurveProjectivePointData

/-! # The curve coordinate ideal is the actual image point's ideal under the chosen projective embedding -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceEmbeddedCurvePointData

open AlgebraicGeometry PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations

attribute [local instance] MvPolynomial.gradedAlgebra

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type u} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (p : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece c D I J))

def point : ProjectiveSpectrum
    (MvPolynomial.homogeneousSubmodule (SourceProjectiveEmbedding.GeneratorIndex F (Fin s.length) D) F) := by
  letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  exact ProjRadicalMap.pointComap (SourceProjectiveEmbedding.evaluation c D I J hdeg hD)
    ((SourceProjectiveEmbedding.irrelevant_le_map c D I J hdeg hD).trans Ideal.le_radical) p

theorem point_eq_embedding :
    point s c D I J hdeg hD p = SourceProjectiveEmbedding.embedding c D I J hdeg hD p := rfl

theorem point_ideal : (point s c D I J hdeg hD p).asHomogeneousIdeal.toIdeal =
    SourceCurveEmbeddingCoordinates.coordinateIdeal c D I J hdeg hD
      (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) := rfl

theorem ideal_prime : (SourceCurveEmbeddingCoordinates.coordinateIdeal c D I J hdeg hD
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)).IsPrime :=
  (point s c D I J hdeg hD p).isPrime

theorem not_irrelevant_le :
    ¬(HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (SourceProjectiveEmbedding.GeneratorIndex F (Fin s.length) D) F)).toIdeal ≤
      SourceCurveEmbeddingCoordinates.coordinateIdeal c D I J hdeg hD
        (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) :=
  (point s c D I J hdeg hD p).not_irrelevant_le

theorem global_relations_le : RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom ≤
    SourceCurveEmbeddingCoordinates.coordinateIdeal c D I J hdeg hD
      (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) := by
  intro a ha
  change SourceProjectiveEmbedding.evaluation c D I J hdeg hD a ∈
    SourceCurveProjectivePointData.ideal s c D I J hdeg hD p
  have hz : SourceProjectiveEmbedding.evaluation c D I J hdeg hD a = 0 := RingHom.mem_ker.mp ha
  rw [hz]
  exact Ideal.zero_mem _

end PaperP1.SourceEmbeddedCurvePointData
