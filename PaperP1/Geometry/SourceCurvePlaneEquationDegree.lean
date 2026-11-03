module

public import PaperP1.Geometry.SourceCurveProjectiveFieldRank
public import PaperP1.Algebra.SourceCurvePlaneEquationHilbert

/-! # The actual source curve projection degree formula over an identified plane equation

All Hilbert-polynomial existence arguments are discharged. The remaining
image hypothesis is the literal equality of its base ideal with the
contracted homogeneous plane-equation ideal.
-/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceCurvePlaneEquationDegree

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type u} [Field F] [Infinite F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)
  (P : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J))
  (b : SourceCurveQuotient.BaseRing s c D I J hs hD P)
  (hb : b ∈ SourceCurveQuotient.basePiece s c D I J hs hD P 1) (hb0 : b ≠ 0)
  {e : ℕ} (f : MvPolynomial (Fin 3) F) (hf : f.IsHomogeneous e) (hf0 : f ≠ 0)
  (hbase : SourceCurveQuotient.baseIdeal s c D I J hs hD P = PlaneCurveVeroneseBaseQuotient.ideal F f D)

local instance sourceQuotientRing : CommRing (SourceCurveQuotient.SourceRing s c D I J P) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J P
local instance baseQuotientRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD P) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD P

/-- The source Hilbert degree is D times the plane degree times the actual projective field degree. -/
theorem multiplicity [P.IsPrime] (he : 0 < e) : beta%
    (fun {m n : ℕ} (_ : m = n) ↦
      GradedHilbertPolynomial.multiplicity (SourceCurveQuotient.sourcePiece s c D I J P)
        (SourceCurvePlaneEquationHilbert.exists_polynomial s c D I J hs hD P hdeg f hf hf0 hbase hP) =
          (D : ℚ) * (e : ℚ) * (m : ℚ))
      (SourceCurveProjectiveFieldRank.comparisonProof s c D I J hs hD P hdeg hP b hb hb0) := by
  have hm := SourceCurvePlaneEquationHilbert.multiplicity s c D I J hs hD P hdeg f hf hf0 hbase hP he
  exact hm.trans ((mul_comm _ _).trans (congrArg (fun r : ℕ ↦ (D : ℚ) * (e : ℚ) * (r : ℚ))
    (SourceCurveProjectiveFieldRank.comparisonProof s c D I J hs hD P hdeg hP b hb hb0).symm))

end PaperP1.SourceCurvePlaneEquationDegree
