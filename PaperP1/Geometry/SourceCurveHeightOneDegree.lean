module

public import PaperP1.Geometry.SourceCurvePlaneImageEquation
public import PaperP1.Geometry.SourceCurvePlaneEquationDegree
public import PaperP1.Geometry.SourceCurveProjectionHeight

/-! # Actual curve degree and Hilbert existence from the height of the actual plane image prime

The homogeneous irreducible plane equation and its contraction equality are
conclusions. A height-one source prime supplies the corresponding image height;
neither image-height equality nor Hilbert existence is assumed in the final corollary.
-/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceCurveHeightOneDegree

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

local instance sourceQuotientRing : CommRing (SourceCurveQuotient.SourceRing s c D I J P) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J P
local instance baseQuotientRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD P) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD P

variable [P.IsPrime]
  (hh : (SourceCurvePlaneImagePrime.ideal s c D I J hs hD P hdeg hP b hb hb0).height = 1)

include hh in
theorem exists_polynomial :
    ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (SourceCurveQuotient.sourcePiece s c D I J P) p := by
  obtain ⟨e, f, _, hf0, hf, _, hbase⟩ := SourceCurvePlaneImageEquation.exists_equation s c D I J hs hD P hdeg hP b hb hb0 hh
  exact SourceCurvePlaneEquationHilbert.exists_polynomial s c D I J hs hD P hdeg f hf hf0 hbase hP

/-- Extracted plane equation, actual source Hilbert degree, and actual projective field degree. -/
theorem exists_degree_formula : beta%
    (fun {m n : ℕ} (_ : m = n) ↦
      ∃ (e : ℕ) (f : MvPolynomial (Fin 3) F), 0 < e ∧ f ≠ 0 ∧ f.IsHomogeneous e ∧ Irreducible f ∧
        SourceCurveQuotient.baseIdeal s c D I J hs hD P = PlaneCurveVeroneseBaseQuotient.ideal F f D ∧
        GradedHilbertPolynomial.multiplicity (SourceCurveQuotient.sourcePiece s c D I J P)
          (exists_polynomial s c D I J hs hD P hdeg hP b hb hb0 hh) = (D : ℚ) * (e : ℚ) * (m : ℚ))
      (SourceCurveProjectiveFieldRank.comparisonProof s c D I J hs hD P hdeg hP b hb hb0) := by
  obtain ⟨e, f, he, hf0, hf, hfirr, hbase⟩ :=
    SourceCurvePlaneImageEquation.exists_equation s c D I J hs hD P hdeg hP b hb hb0 hh
  exact ⟨e, f, he, hf0, hf, hfirr, hbase,
    SourceCurvePlaneEquationDegree.multiplicity s c D I J hs hD P hdeg hP b hb hb0 f hf hf0 hbase he⟩


include hs hD hdeg hP b hb hb0 in
theorem exists_polynomial_of_source_height (hsource : P.height = 1) :
    ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (SourceCurveQuotient.sourcePiece s c D I J P) p :=
  exists_polynomial s c D I J hs hD P hdeg hP b hb hb0
    (SourceCurveProjectionHeight.plane_height_one s c D I J hs hD P hdeg hP b hb hb0 hsource)

/-- A height-one source prime supplies its own irreducible plane equation and actual degree formula. -/
theorem exists_degree_formula_of_source_height (hsource : P.height = 1) : beta%
    (fun {m n : ℕ} (_ : m = n) ↦
      ∃ (e : ℕ) (f : MvPolynomial (Fin 3) F), 0 < e ∧ f ≠ 0 ∧ f.IsHomogeneous e ∧ Irreducible f ∧
        SourceCurveQuotient.baseIdeal s c D I J hs hD P = PlaneCurveVeroneseBaseQuotient.ideal F f D ∧
        GradedHilbertPolynomial.multiplicity (SourceCurveQuotient.sourcePiece s c D I J P)
          (exists_polynomial_of_source_height s c D I J hs hD P hdeg hP b hb hb0 hsource) =
            (D : ℚ) * (e : ℚ) * (m : ℚ))
      (SourceCurveProjectiveFieldRank.comparisonProof s c D I J hs hD P hdeg hP b hb hb0) :=
  exists_degree_formula s c D I J hs hD P hdeg hP b hb hb0
    (SourceCurveProjectionHeight.plane_height_one s c D I J hs hD P hdeg hP b hb hb0 hsource)

end PaperP1.SourceCurveHeightOneDegree
