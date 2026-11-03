module

public import PaperP1.Geometry.SourceProjectiveMap
public import PaperP1.Algebra.SourceCurveQuotient
public import PaperP1.Algebra.GradedQuotientChartCoordinate

/-! # An actual projective source point supplies its prime, homogeneous data, and a nonzero base coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceCurveProjectivePointData

open AlgebraicGeometry PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type u} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (p : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece c D I J))

def ideal : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J) := by
  letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  exact p.asHomogeneousIdeal.toIdeal

theorem ideal_prime : (ideal s c D I J hdeg hD p).IsPrime := by
  let := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  exact p.isPrime

theorem ideal_homogeneous :
    letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    (ideal s c D I J hdeg hD p).IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J) := by
  let := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  exact p.asHomogeneousIdeal.isHomogeneous

def basePoint :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    ProjectiveSpectrum (SourceVeroneseGrading.nativePiece F D) := by
  letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  letI := SourceVeroneseGrading.nativeGrading F D hD
  exact ProjRadicalMap.pointComap (SourceVeroneseGradedBaseMap.gradedBaseMap s c D hD I J hs)
    (SourceVeroneseIrrelevant.source_irrelevant_le_radical s c D hD I J hs hdeg) p

theorem basePoint_ideal :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    (basePoint s c D I J hs hdeg hD p).asHomogeneousIdeal.toIdeal =
      SourceCurveQuotient.baseIdeal s c D I J hs hD (ideal s c D I J hdeg hD p) := rfl

theorem exists_coordinate :
    ∃ b : SourceCurveQuotient.BaseRing s c D I J hs hD (ideal s c D I J hdeg hD p),
      b ∈ SourceCurveQuotient.basePiece s c D I J hs hD (ideal s c D I J hdeg hD p) 1 ∧ b ≠ 0 := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  have hrel : ¬(HomogeneousIdeal.irrelevant (SourceVeroneseGrading.nativePiece F D)).toIdeal ≤
      SourceCurveQuotient.baseIdeal s c D I J hs hD (ideal s c D I J hdeg hD p) := by
    intro h
    apply (basePoint s c D I J hs hdeg hD p).not_irrelevant_le
    exact h
  exact GradedQuotientChartCoordinate.exists_coordinate (SourceVeroneseGrading.nativePiece F D)
    (SourceVeroneseGrading.native_generated_degree_one F D hD)
    (SourceCurveQuotient.baseIdeal s c D I J hs hD (ideal s c D I J hdeg hD p)) hrel

def coordinate : SourceCurveQuotient.BaseRing s c D I J hs hD (ideal s c D I J hdeg hD p) :=
  (exists_coordinate s c D I J hs hdeg hD p).choose

theorem coordinate_mem : coordinate s c D I J hs hdeg hD p ∈
    SourceCurveQuotient.basePiece s c D I J hs hD (ideal s c D I J hdeg hD p) 1 :=
  (exists_coordinate s c D I J hs hdeg hD p).choose_spec.1

theorem coordinate_ne_zero : coordinate s c D I J hs hdeg hD p ≠ 0 :=
  (exists_coordinate s c D I J hs hdeg hD p).choose_spec.2

end PaperP1.SourceCurveProjectivePointData
