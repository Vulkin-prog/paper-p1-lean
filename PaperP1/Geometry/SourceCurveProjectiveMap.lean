module

public import PaperP1.Algebra.SourceCurveQuotient
public import PaperP1.Algebra.GradedQuotientAdmissibility
public import PaperP1.Geometry.SourceProjectiveMap

/-! # The actual homogeneous source quotient projects to the actual base preimage quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceCurveProjectiveMap

open AlgebraicGeometry PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData PaperP1.SourceVeroneseGradedBaseMap

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type u} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)
  (P : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J))

local instance sourceQuotientRing : CommRing (SourceCurveQuotient.SourceRing s c D I J P) := inferInstance
local instance baseQuotientRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD P) := inferInstance

def baseScheme : Scheme.{u} := by
  letI := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
  exact Proj (SourceCurveQuotient.basePiece s c D I J hs hD P)

def sourceScheme : Scheme.{u} := by
  letI := SourceCurveQuotient.sourceGrading s c D I J hD P hdeg hP
  exact Proj (SourceCurveQuotient.sourcePiece s c D I J P)

include hP in
theorem admissible :
    letI := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
    letI := SourceCurveQuotient.sourceGrading s c D I J hD P hdeg hP
    (HomogeneousIdeal.irrelevant (SourceCurveQuotient.sourcePiece s c D I J P)).toIdeal ≤
      ((HomogeneousIdeal.irrelevant (SourceCurveQuotient.basePiece s c D I J hs hD P)).toIdeal.map
        (SourceCurveQuotient.map s c D I J hs hD P).toRingHom).radical := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  let := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  let := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
  let := SourceCurveQuotient.sourceGrading s c D I J hD P hdeg hP
  exact GradedQuotientAdmissibility.irrelevant_le_radical (gradedBaseMap s c D hD I J hs)
    (SourceVeroneseIrrelevant.source_irrelevant_le_radical s c D hD I J hs hdeg) P hP

def projection : sourceScheme s c D I J hD P hdeg hP ⟶ baseScheme s c D I J hs hD P hdeg hP := by
  letI := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
  letI := SourceCurveQuotient.sourceGrading s c D I J hD P hdeg hP
  exact ProjRadicalMap.map (SourceCurveQuotient.map s c D I J hs hD P)
    (admissible s c D I J hs hD P hdeg hP)

end PaperP1.SourceCurveProjectiveMap
